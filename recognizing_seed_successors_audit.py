"""Exercise both signed successors against the previous recognizers on DIMACS files."""
from collections import defaultdict
from itertools import product
from random import Random

from portfolio_proof_receipt_audit import lex_solver, masks, pin
from single_support_seed_census import WITNESS, signed_copy


def physical_file(rows):
    bound = max(abs(lit) for row in rows for lit in row)
    return (f'p cnf {bound} {len(rows)}\n' +
            ''.join(' '.join(map(str, (*row, 0)))+'\n' for row in rows)).encode('ascii')


def parse(raw):
    header, *lines = raw.splitlines()
    rows = [tuple(map(int, line.split())) for line in lines]
    assert int(header.split()[3]) == len(rows)
    assert all(len(row) == 4 and row[-1] == 0 and len({abs(x) for x in row[:3]}) == 3 for row in rows)
    return [row[:-1] for row in rows]


def components(rows):
    touching = defaultdict(list)
    for i, row in enumerate(rows):
        for name in row:
            touching[name].append(i)
    unseen = set(touching)
    while unseen:
        start = unseen.pop()
        stack, names, indices = [start], [start], set()
        while stack:
            for i in touching[stack.pop()]:
                if i in indices:
                    continue
                indices.add(i)
                for v in rows[i]:
                    if v in unseen:
                        unseen.remove(v)
                        names.append(v)
                        stack.append(v)
        yield names, indices


def solve(raw, method, one_first=False):
    rows = parse(raw)
    support_rows = [tuple(abs(x) for x in row) for row in rows]
    if method == 'component':
        # Complete solver; try only the variables of the current component.
        trials = 0
        for names, indices in components(support_rows):
            local = [rows[i] for i in indices]
            ok, count = lex_solver(masks(local, names), len(names), one_first)
            trials += count
            if not ok:
                return False, trials
        return True, trials

    forced = defaultdict(set)
    equations = []
    buckets = defaultdict(set)
    if method in ('pin', 'xor'):
        for row in rows:
            ordered = sorted(row, key=abs)
            buckets[tuple(map(abs, ordered))].add(tuple(int(x < 0) for x in ordered))
    for names, denied in buckets.items():
        allowed = set(product(range(2), repeat=3)) - denied
        if not allowed:
            return False, 0
        for i, name in enumerate(names):
            values = {word[i] for word in allowed}
            if len(values) == 1:
                forced[name].update(values)
        parities = {sum(word) % 2 for word in allowed}
        if method == 'xor' and len(parities) == 1:
            equations.append((names, parities.pop()))
    for names, indices in components([triple for triple, _ in equations]):
        if len(names) > 4:
            continue
        solutions = []
        for word in product(range(2), repeat=len(names)):
            assignment = dict(zip(names, word))
            if all(sum(assignment[v] for v in equations[i][0]) % 2 == equations[i][1]
                   for i in indices):
                solutions.append(assignment)
        if not solutions:
            return False, 0
        for v in names:
            values = {assignment[v] for assignment in solutions}
            if len(values) == 1:
                forced[v].update(values)
    while forced:
        if any(len(values) > 1 for values in forced.values()):
            return False, 0
        pins = {name: next(iter(values)) for name, values in forced.items()}
        remaining = []
        for row in rows:
            if any(pins.get(abs(x)) == int(x > 0) for x in row):
                continue
            reduced = tuple(x for x in row if abs(x) not in pins)
            if not reduced:
                return False, 0
            remaining.append(reduced)
        rows = remaining
        forced = defaultdict(set)
        for row in rows:
            if len(row) == 1:
                forced[abs(row[0])].add(int(row[0] > 0))
    if not rows:
        return True, 0
    names = sorted({abs(x) for row in rows for x in row})
    return lex_solver(masks(rows, names), len(names), one_first)


def examples():
    old = [(1, 2, 3)]
    pinned = pin(-4, 6, 7) + pin(5, 6, 7)
    yield 'pin', old + pinned, old + pinned + pin(-5, 6, 7), 2

    equations = []
    for offset in (4, 8):
        for omit in range(4):
            inds = [j for j in range(4) if j != omit]
            desired = sum(j >= 2 for j in inds) % 2
            for word in product(range(2), repeat=3):
                if sum(word) % 2 != desired:
                    equations.append(tuple(-(offset+j) if bit else offset+j for j, bit in zip(inds, word)))
    yield 'xor', old + equations, old + equations + [(4, -6, 8)], 16

    hidden = list(signed_copy(WITNESS, 0, 3)) + list(signed_copy(WITNESS, 31, 8))
    yield 'single', old + hidden, old + hidden + [(4, 5, -9)], 32


def main():
    rng = Random(28)
    for level, yes, no, minimum in examples():
        hidden_from = {'pin': ('plain',), 'xor': ('plain', 'pin'),
                       'single': ('plain', 'pin', 'xor')}[level]
        positive_trials, negative_trials = [], []
        for trial in range(12):
            names = sorted({abs(x) for row in no for x in row})
            mapping = dict(zip(names, rng.sample(names, len(names))))
            def materialize(rows):
                if trial == 0:
                    return physical_file(rows)
                shuffled = [tuple(mapping[abs(x)] * (1 if x > 0 else -1)
                                  for x in rng.sample(row, len(row))) for row in rows]
                rng.shuffle(shuffled)
                return physical_file(shuffled)
            legal, illegal = materialize(yes), materialize(no)
            for method in (*hidden_from, 'component') + (() if level == 'single' else (level,)):
                for reverse in (False, True):
                    ok, count = solve(legal, method, reverse)
                    rejected, count_no = solve(illegal, method, reverse)
                    assert ok and not rejected
                    if method in hidden_from:
                        positive_trials.append(count)
                        negative_trials.append(count_no)
                        assert count >= minimum and count_no >= minimum
                    if method == level:
                        assert count <= 8 and count_no == 0
        print(f'{level}: 12 layouts; hidden solvers min assignment trials SAT={min(positive_trials)} '
              f'UNSAT={min(negative_trials)}; component control correct')


if __name__ == '__main__':
    main()
