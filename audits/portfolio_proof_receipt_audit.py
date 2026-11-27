"""Finite portfolio/prefix-proof audit on actual proper DIMACS bytes.

Toy ticks count input bytes, explicit wait ticks, assignments and literal
tests. Neither this meter nor the three-bit proof is an asymptotic RAM.
"""

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, permutations, product
from random import Random

from cnf_width_dictionary_audit import read_dimacs
from compiled_horn_receipt_audit import Circuit, exact_sat


CAP = 12_000
WORDS = tuple(product((0, 1), repeat=3))
PROOFS = frozenset(((0, 1, 0), (0, 1, 1), (1, 1, 0)))


def forbid(word, variables):
    return tuple(-v if b else v for b, v in zip(word, variables))


@lru_cache(None)
def question(prefix):
    net = Circuit(True)
    variables = [net.fresh() for _ in range(3)]
    for word in WORDS:
        if word not in PROOFS:
            net.add(*forbid(word, variables))
    for b, v in zip(prefix, variables):
        net.add(v if b else -v)
    return net.bytes()


def training(rows):
    body = ''.join(' '.join(map(str, (*forbid(w, (1, 2, 3)), 0))) + '\n' for w in rows)
    return (f'p cnf 3 {len(rows)}\n' + body).encode('ascii')


BAD_A = training(WORDS)
BAD_B = training(WORDS[::-1])
GOOD = training(WORDS[:-1])


@dataclass(frozen=True)
class Program:
    name: str
    late: frozenset = frozenset()
    flips: frozenset = frozenset()

    def run(self, raw):
        # Actual deterministic exhaustive decision. A flipped file or a wait
        # is selected by its full bytes, independently of its SAT verdict.
        for _ in raw:
            yield
        if raw in self.late:
            for _ in range(3*CAP):
                yield
        rows = [tuple(map(int, clause)) for clause in read_dimacs(raw)]
        assert all(len(row) == len({abs(v) for v in row}) == 3 for row in rows)
        names = sorted({abs(v) for row in rows for v in row})
        for values in product((False, True), repeat=len(names)):
            yield
            bits = dict(zip(names, values))
            for row in rows:
                for lit in row:
                    yield
                    if bits[abs(lit)] == (lit > 0):
                        break
                else:
                    break
            else:
                return raw not in self.flips
        return raw in self.flips


@lru_cache(None)
def run_to(program, raw, cap):
    driver = program.run(raw)
    ticks = 0
    while True:
        try:
            next(driver)
        except StopIteration as stop:
            return stop.value, ticks
        ticks += 1
        if cap is not None and ticks > cap:
            return None, cap


def vote(members, mode, raw):
    outputs = tuple(run_to(p, raw, CAP)[0] for p in members)
    return (True in outputs) if mode == 'OR' else (False not in outputs)


def attempt(members, mode, retire_files):
    receipts = []

    def ask(raw):
        value = vote(members, mode, raw)
        receipts.append((raw, value))
        return value

    for raw in retire_files:
        if ask(raw) != exact_sat(raw):
            return 'retired', raw, receipts
    prefix = ()
    if ask(question(prefix)):
        while len(prefix) < 3:
            prefix += (int(not ask(question(prefix + (0,)))),)
        if prefix in PROOFS:
            assert exact_sat(question(prefix))
            return 'proof', prefix, receipts
    wrong = next(raw for raw, reported in receipts if exact_sat(raw) != reported)
    return 'failed', wrong, receipts


def subsets(roster):
    for k in range(1, len(roster)+1):
        yield from combinations(roster, k)


def pin(literal, a, b):
    return [(literal, s*a, t*b) for s, t in product((1, -1), repeat=2)]


def seeded_files(base, m):
    """Keep the old body verbatim and append two equally large sets of opposite pins."""
    header, body = base.split(b'\n', 1)
    _, _, bound, count = header.split()
    old = int(bound)
    zeros = tuple(range(old+1, old+m+1))
    ones = tuple(range(old+m+1, old+2*m+1))
    a, b = old+2*m+1, old+2*m+2
    rows = [row for literal in (*(-z for z in zeros), *ones) for row in pin(literal, a, b)]

    def file(added):
        prefix = f'p cnf {b} {int(count)+len(added)}\n'.encode('ascii')
        return prefix + body + b''.join((' '.join(map(str, (*row, 0)))+'\n').encode() for row in added)

    return zeros, ones, (a, b), file(rows), file(rows + pin(-ones[-1], a, b))


def clauses(raw):
    rows = [tuple(map(int, row)) for row in read_dimacs(raw)]
    assert all(len(row) == len({abs(x) for x in row}) == 3 for row in rows)
    key = lambda row: tuple((abs(x), x < 0) for x in row)
    assert all(sorted(row, key=abs) == list(row) for row in rows)
    assert sorted(rows, key=key) == rows and len(set(rows)) == len(rows)
    return rows


def masks(rows, order):
    assert set(order) == {abs(x) for row in rows for x in row} and len(order) == len(set(order))
    weight = {x: 1 << (len(order)-1-i) for i, x in enumerate(order)}
    return [(sum(weight[x] for x in row if x > 0), sum(weight[-x] for x in row if x < 0))
            for row in rows]


def lex_solver(compiled, n, one_first):
    """Return the verdict and actual number of complete assignments tried."""
    end = (1 << n)-1
    for index in range(end+1):
        value = end-index if one_first else index
        if all(value & pos or value & neg != neg for pos, neg in compiled):
            return True, index+1
    return False, end+1


def seed_census():
    # The first base admits both constant assignments, allowing equality
    # in the weight bound by placing all pins of the opposite value last.
    bases = (training((WORDS[2],)), GOOD)
    rng = Random(787)
    order_count = runs = assignments = projections = 0
    for base_index, base in enumerate(bases):
        for m in range(1, 5):
            zeros, ones, (a, b), yes, no = seeded_files(base, m)
            body = base.split(b'\n', 1)[1]
            assert yes.split(b'\n', 1)[1].startswith(body)
            assert no.split(b'\n', 1)[1].startswith(yes.split(b'\n', 1)[1])
            yr, nr = clauses(yes), clauses(no)
            assert exact_sat(yes) and not exact_sat(no)
            names = tuple(range(1, b+1))
            compiled = masks(yr, names)
            # Check every assignment to the old variables, new pins and
            # both anchors. The anchors retain all four possible settings.
            original = clauses(base)
            for values in product((0, 1), repeat=b):
                val = sum(bit << (b-1-i) for i, bit in enumerate(values))
                expected = (all(any(values[abs(x)-1] == (x > 0) for x in row) for row in original)
                            and not any(values[z-1] for z in zeros) and all(values[o-1] for o in ones))
                assert all(val & pos or val & neg != neg for pos, neg in compiled) == expected
                projections += 1
            if base_index == 0 and m == 1:
                orders = permutations(names)
            else:
                orders = (names, names[::-1], tuple(rng.sample(names, b)),
                          tuple(x for x in names if x not in zeros) + zeros,
                          tuple(x for x in names if x not in ones) + ones)
            for order in orders:
                order_count += 1
                cmds_yes, cmds_no = masks(yr, order), masks(nr, order)
                for one_first in (False, True):
                    ok, first = lex_solver(cmds_yes, b, one_first)
                    rejected, full = lex_solver(cmds_no, b, one_first)
                    assert ok and first >= 1 << m and not rejected and full == 1 << b
                    if base_index == 0 and order[-m:] == (zeros if one_first else ones):
                        assert first == 1 << m
                    assignments += first + full
                    runs += 2

    # Exact encoded lengths; at these larger m the rank argument replaces
    # execution. At least 2^m complete assignments are necessary for both
    # scans on both signs, while either file has O(m log(m+2)) bits.
    cutoffs = {}
    for m in range(1, 150):
        *_, yes, no = seeded_files(bases[0], m)
        n = 8*max(len(yes), len(no))
        for k in (1, 2, 3):
            if 1 << m > (n+1)**k:
                cutoffs.setdefault(k, (m, n))
        if len(cutoffs) == 3:
            break
    assert len(cutoffs) == 3
    print(f'seed_census: paired_files=8 variable_orders={order_count} lex_runs={runs} '
          f'assignments_tried={assignments} projected_assignments_checked={projections} '
          f'rank_bound_first_exceeds_(N+1)^k={cutoffs}')


def main():
    prefixes = [p for k in range(4) for p in product((0, 1), repeat=k)]
    files = [question(p) for p in prefixes] + [BAD_A, BAD_B, GOOD]
    assert len(set(files)) == len(files)
    assert all(exact_sat(question(p)) == any(w[:len(p)] == p for w in PROOFS) for p in prefixes)
    assert not exact_sat(BAD_A) and not exact_sat(BAD_B) and exact_sat(GOOD)

    # Q(0) is SAT and Q(00) is UNSAT. On the actual greedy paths all
    # four candidates miss both deadlines, while empty-prefix Q is quick.
    slow = frozenset(question(p) for p in ((0,), (0, 0), (1, 1, 0)))
    a = Program('A', slow | {question((1, 0, 0))})
    b = Program('B', slow | {question((0, 1, 0))})
    x = Program('X', slow, frozenset((BAD_A,)))
    y = Program('Y', slow, frozenset((GOOD,)))
    roster = (a, b, x, y)
    for p in roster:
        for raw in files:
            answer, ticks = run_to(p, raw, None)
            assert answer == (exact_sat(raw) ^ (raw in p.flips))
            if raw in p.late:
                assert ticks >= 3*CAP and run_to(p, raw, CAP)[0] is None
            else:
                assert ticks < CAP and run_to(p, raw, CAP) == (answer, ticks)

    retired = active = receipt_count = common = 0
    for group in subsets(roster):
        for mode in ('OR', 'AND'):
            status, bad, receipts = attempt(group, mode, (BAD_A, BAD_B, GOOD))
            assert status != 'proof' and (bad, not exact_sat(bad)) in receipts
            retired += status == 'retired'
            active += status == 'failed'
            receipt_count += len(receipts)
            if all(p in (a, b) for p in group):
                assert status == 'failed' and exact_sat(bad) == (mode == 'OR')
                assert all(run_to(p, bad, CAP)[0] is None for p in group)
                if group == (a, b):
                    common += 1

    fast = Program('fast')
    proofs = []
    for mode in ('OR', 'AND'):
        status, proof, _ = attempt((a, b, fast), mode, (BAD_A, BAD_B, GOOD))
        assert status == 'proof' and proof == min(PROOFS)
        proofs.append(proof)

    # Both raw programs give demonstrably wrong YES answers, on different
    # files. Their AND portfolio is exact throughout the finite domain.
    # Removing each faulty raw member before evaluating the pair destroys
    # the genuine shared proof that this portfolio recovers.
    p = Program('bad-A-only', flips=frozenset((BAD_A,)))
    q = Program('bad-B-only', flips=frozenset((BAD_B,)))
    assert all(vote((p, q), 'AND', raw) == exact_sat(raw) for raw in files)
    status, proof, _ = attempt((p, q), 'AND', (BAD_A, BAD_B, GOOD))
    assert status == 'proof' and proof == min(PROOFS)
    assert not [u for u in (p, q) if all(run_to(u, raw, CAP)[0] == exact_sat(raw) for raw in files)]
    assert attempt((p, q), 'OR', (BAD_A, BAD_B, GOOD))[0] == 'retired'
    print(f'proper_files={len(files)} proofs={len(PROOFS)} no_proof_portfolios={retired+active} '
          f'retired={retired} active_failed={active} issued_receipts={receipt_count} '
          f'common_all_correct_slow_signs={common} honest_recoveries={len(proofs)} '
          f'jointly_recovered_after_two_individual_errors={proof}')
    seed_census()


if __name__ == '__main__':
    main()
