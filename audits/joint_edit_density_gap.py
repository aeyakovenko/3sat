"""Check the saturation factors and a complete pair of no-common-pin edits."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product

from one_bit_clause_density_threshold import encode, parse


def assignments(names):
    for values in product((False, True), repeat=len(names)):
        yield dict(zip(names, values))


def cofactor(cnf, fixed):
    residual = []
    for clause in cnf:
        if any(abs(x) in fixed and fixed[abs(x)] == (x > 0) for x in clause):
            continue
        short = tuple(x for x in clause if abs(x) not in fixed)
        if not short:
            return None
        residual.append(short)
    return residual


def audit_mass_constants():
    # At most four coordinates are fixed in the product of seven-pattern blocks.
    domains = [(x, 7) for x in (3, 4)], [(x, 7) for x in (1, 2)], [(1, 7)]
    smallest = [Fraction(1)]
    for n in range(1, 5):
        opts = [Fraction(1, 2) * smallest[n-1]]
        for j in range(1, min(3, n)+1):
            actual = Counter(x % (2**j) for x in range(1, 8))
            assert sorted(set(actual.values())) == sorted({a for a, _ in domains[j-1]})
            opts.extend(Fraction(a, b) * smallest[n-j] for a, b in domains[j-1])
        smallest.append(min(opts))
    assert min(smallest) == Fraction(1, 49)
    # If both cylinders saturate, a fixed pattern touching a positive base
    # clause must satisfy a literal there. Filling its remaining k bits then
    # loses no clause mass beyond uniform pinning. By sign symmetry one
    # positive clause suffices to check all local patterns.
    for pinned in range(1, 8):
        for ones in range(1, 8):
            if ones & pinned != ones:
                continue
            allowed = sum((x & pinned) == ones for x in range(1, 8))
            assert Fraction(allowed, 7) >= Fraction(1, 2**pinned.bit_count())
    assert Fraction(1, 16) > Fraction(3, 49)
    q, K = Fraction(7, 8), Fraction(4, 7)**4
    assert max(q, Fraction(6, 7)) < Fraction(46, 49)
    assert (6-Fraction(3, 7))*K > Fraction(4, 7)
    assert (5-Fraction(3, 49))*K > Fraction(4, 7)**2


def make(test_forbidden, edited):
    # Pin boxes for the two original rows; only the selector is shared and
    # its required value differs. Old and new decimal digits differ in one bit.
    selector = 7
    gates = (selector, -selector)
    old, new, pad = (1, 4), (3, 5), (8, 9)
    pins = [frozenset((-g, a, -b, -c)) for g, a, b, c in zip(gates, old, new, pad)]
    assert not pins[0].intersection(pins[1])
    body = []
    for i, (g, a, b, c) in enumerate(zip(gates, old, new, pad)):
        free = old[i ^ 1]
        body.extend(((g, -c, free), (g, -c, -free), (g, a, b), (g, -a, -b)))
        if test_forbidden[i]:
            body.extend(((g, -b, free), (g, -b, -free)))
        body.append((g, new[i] if edited[i] else old[i], c))
    fresh = 100
    bank = []
    for l, r in product(sorted(pins[0]), sorted(pins[1])):
        if abs(l) == abs(r):
            continue
        bank.append(frozenset((abs(l), abs(r))))
        for _ in range(5):
            body.append((l, r, fresh))
            fresh += 1
    # One exceptional single-W support per active old variable.
    body.extend(((old[0], 20, 21), (old[1], 22, 23)))
    # A disjoint full data-only clause exercises the matching in the solver.
    body.append((30, 31, 32))
    return encode(body), pins, bank


def check_transversal(cnf, pins, bank):
    W = sorted({abs(x) for p in pins for x in p})
    minimum_bank = [({*s}) for k in range(5) for s in combinations(W, k)
                    if all(not e.isdisjoint(s) for e in bank)]
    assert {tuple(sorted(s)) for s in minimum_bank} == {
        tuple(sorted(abs(x) for x in p)) for p in pins}
    # Each missed bank pair has five private fillers, so every cover of
    # size <=4 of the core must hit its pair on the control vertices.
    assert all(1 not in s or 4 not in s for s in minimum_bank)
    cover = {*(abs(x) for x in pins[0]), 4, 30}
    assert len(cover) == 6
    assert all(not cover.isdisjoint(map(abs, row)) for row in cnf)
    # The isolated data triple costs one. The remainder costs >=5: each
    # potential four-cover misses the other single-W clause.
    return 6


def all_masses(cnf, pins):
    W = sorted({abs(x) for p in pins for x in p})
    front = [*W, 20, 21, 22, 23]
    all_names = {abs(x) for c in cnf for x in c}
    fillers = all_names - set(front) - {30, 31, 32}
    mass = [0, 0, 0]
    for fixed in assignments(front):
        cut = cofactor(cnf, fixed)
        if cut is None:
            continue
        assert (30,31,32) in cut
        units = {r[0] for r in cut if r != (30,31,32)}
        assert all(len(r) == 1 or r == (30,31,32) for r in cut)
        assert units <= fillers
        ways = 7 * 2**(len(fillers) - len(units))
        mass[0] += ways
        for i, pattern in enumerate(pins):
            if all(fixed[abs(lit)] == (lit > 0) for lit in pattern):
                mass[i+1] += ways
    return [Fraction(x, 2 ** len(all_names)) for x in mass]


def solver(cnf, cap):
    # Only the edited clauses, with no easy file, patterns or densities.
    supports = list({frozenset(map(abs, c)) for c in cnf})
    degree = Counter(x for e in supports for x in e)

    @lru_cache(None)
    def search(Z):
        avoiding = []
        defect = None
        for edge in supports:
            ns = len(edge & Z)
            if ns == 1:
                defect = edge - Z
                break
            if ns == 0:
                avoiding.append(edge)
        if defect is None:
            owners = {}
            for edge in avoiding:
                v = next((x for x in edge if x in owners), None)
                if v is not None:
                    defect = owners[v] | edge
                    break
                for x in edge:
                    owners[x] = edge
        if defect is None:
            return Z
        if len(Z) == cap:
            return None
        for x in sorted(defect, key=lambda z: -degree[z]):
            result = search(Z | {x})
            if result is not None:
                return result
        return None

    chosen = search(frozenset())
    assert chosen is not None
    for fixed in assignments(sorted(chosen)):
        cut = cofactor(cnf, fixed)
        if cut is None:
            continue
        forced = {row[0] for row in cut if len(row) == 1}
        if any(-u in forced for u in forced):
            continue
        blocks = {}
        for row in cut:
            if len(row) == 1:
                continue
            assert len(row) == 3
            block = frozenset(map(abs, row))
            blocks.setdefault(block, []).append(row)
        assert len(set().union(*blocks)) == sum(map(len, blocks))
        for block, rows in blocks.items():
            if not any(all(f[x] == (x in forced) for x in block
                               if x in forced or -x in forced) and cofactor(rows, f) is not None
                       for f in assignments(sorted(block))):
                break
        else:
            return True
    return False


if __name__ == '__main__':
    audit_mass_constants()
    K, q = Fraction(4, 7)**4, Fraction(7, 8)
    for forbidden in ((False, False), (True, False), (True, True)):
        easy, pins, bank = make(forbidden, (False, False))
        cnf = parse(easy)
        tau = check_transversal(cnf, pins, bank)
        assert all_masses(cnf, pins) == [2*K*q**tau, K*q**tau, K*q**tau]
        for edits in ((True, False), (False, True), (True, True)):
            hard, _, _ = make(forbidden, edits)
            assert len(easy) == len(hard)
            assert sum((a^b).bit_count() for a, b in zip(easy, hard)) == sum(edits)
            expected = not all(need and blocked for need, blocked in zip(edits, forbidden))
            assert solver(parse(hard), 16) == expected
    print('Nine proper targets, both joint verdicts, saturated disjoint cylinders and all mass constants checked.')
