"""Exhaust the necessary nine-label incidence pattern and verify actual finite covers."""

from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations


NINE = [(0, 5, 6), (0, 5, 7), (0, 6, 8), (1, 2, 5), (1, 3, 6),
        (1, 4, 7), (2, 3, 8), (2, 4, 7), (3, 4, 8)]
NINE_MATCHING = (0, 5, 6, 1, 3, 4, 2, 7, 8)
NINE_P = (1, 7, 0, 6, 2, 3, 8, 5, 4)
NINE_Q = (2, 0, 8, 1, 3, 7, 4, 6, 5)
NINE_Z = (2, 0, 0, 1, 1, 1, 1, 0, 0)

TWELVE = [(0, 6, 7), (0, 8, 9), (0, 10, 11), (1, 7, 8), (1, 9, 10),
          (1, 11, 6), (2, 3, 6), (3, 4, 8), (4, 5, 10), (2, 4, 7),
          (2, 5, 9), (3, 5, 11)]


def regular(rows):
    n = len(rows)
    assert all(len(set(row)) == 3 for row in rows)
    assert Counter(v for row in rows for v in row) == {i: 3 for i in range(n)}


def exact_solutions(rows):
    size = len(rows)
    if size % 3:
        return []
    row_masks = [sum(1 << v for v in row) for row in rows]
    solutions = []
    for selected in combinations(range(size), size//3):
        mask = sum(1 << v for v in selected)
        if all((row & mask).bit_count() == 1 for row in row_masks):
            solutions.append(selected)
    return solutions


def nine_patterns():
    zero = (5, 6, 7, 8)
    half_edges = list(combinations((1, 2, 3, 4), 2))
    counts = Counter()
    for pairs in combinations_with_replacement(combinations(zero, 2), 3):
        remaining = Counter({v: 3 for v in zero})
        remaining.subtract(v for pair in pairs for v in pair)
        if min(remaining.values()) < 0:
            continue
        for marks in set(permutations(remaining.elements())):
            rows = [(0, *pair) for pair in pairs] + [(*edge, z) for edge, z in zip(half_edges, marks)]
            regular(rows)
            counts['patterns'] += 1
            if not exact_solutions(rows):
                counts['unsatisfiable'] += 1
                neighborhoods = [tuple(j for j, row in enumerate(rows) if v in row) for v in range(9)]
                if len(set(rows)) == len(set(neighborhoods)) == 9:
                    counts['twin-free unsatisfiable'] += 1
    return counts


def normalize(rows):
    """Find the three perfect matchings by backtracking. Used only at twelve labels."""
    def matching(options):
        def visit(i, used):
            if i == len(options):
                return ()
            for v in options[i]:
                if v not in used:
                    rest = visit(i+1, used | {v})
                    if rest is not None:
                        return (v, *rest)
            return None
        return visit(0, set())

    first = matching(rows)
    remaining = [tuple(v for v in row if v != j) for row, j in zip(rows, first)]
    second = matching(remaining)
    third = tuple(next(v for v in row if v != j) for row, j in zip(remaining, second))
    return first, tuple(first.index(v) for v in second), tuple(first.index(v) for v in third)


def table(p, q):
    assert sorted(p) == sorted(q) == list(range(len(p)))
    rows = list(zip(range(len(p)), p, q))
    regular(rows)
    return rows


def one_cycle(p):
    j = 0
    for step in range(1, len(p)+1):
        j = p[j]
        if j == 0:
            return step == len(p)


def lift(p, q, z, degree):
    """Keep identity on the sheets, then fill the two other fiber bijections."""
    size = len(p)
    p_out, q_out = [], []
    selected = {degree*i+s for i in range(size) for s in range(z[i])}
    assert all(0 <= v <= degree for v in z)
    for i, (j, k) in enumerate(zip(p, q)):
        assert z[i]+z[j]+z[k] == degree
        for target, offset, images in [(j, z[i], p_out), (k, z[i]+z[j], q_out)]:
            local = tuple(range(offset, offset+z[target]))
            in_order = local + tuple(s for s in range(degree) if s not in local)
            images.extend(degree*target + in_order.index(s) for s in range(degree))
    rows = table(p_out, q_out)
    assert all(sum(v in selected for v in row) == 1 for row in rows)
    for i in range(size):
        for s in range(degree):
            assert p_out[degree*i+s]//degree == p[i] and q_out[degree*i+s]//degree == q[i]
    return p_out, q_out, selected


def connected(p, q):
    seen = {0}
    while True:
        reached = seen | {p[i] for i in seen} | {q[i] for i in seen}
        if reached == seen:
            return len(seen) == len(p)
        seen = reached


if __name__ == '__main__':
    counts = nine_patterns()
    assert counts == {'patterns': 5640, 'unsatisfiable': 2040, 'twin-free unsatisfiable': 1584}
    print('labeled K4 decorations:', dict(counts))
    for rows, first, p, q, z in [
        (NINE, NINE_MATCHING, NINE_P, NINE_Q, NINE_Z),
        (TWELVE, *normalize(TWELVE), None),
    ]:
        regular(rows)
        physical = [set(row) for row in rows]
        assert all({first[v] for v in row} == old for row, old in zip(table(p, q), physical))
        assert not exact_solutions(rows) and not exact_solutions(table(p, q))
        if z is None:
            physical_z = (2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0)
            z = tuple(physical_z[j] for j in first)
            assert all(len(a & b) <= 1 for a, b in combinations(physical, 2))
        else:
            inverse_p = tuple(p.index(i) for i in range(len(p)))
            assert all(one_cycle(r) for r in (p, q, tuple(inverse_p[j] for j in q)))
        assert connected(p, q)
        assert all(sum(1-z[v] for v in row) == 1 for row in table(p, q))
        pp, qq, chosen = lift(p, q, z, 2)
        assert connected(pp, qq)
        print('labels', len(p), 'P', p, 'Q', q, 'z', z)
        print('2-cover flips for P and Q:', tuple(v%2 for v in pp[::2]), tuple(v%2 for v in qq[::2]))
        for d in range(3, 15):
            # Every d≥2 is 2a + 3b; add the fiber counts of a copies of z and b of the all-one vector.
            a, b = (d//2, 0) if d%2 == 0 else ((d-3)//2, 1)
            lift(p, q, tuple(a*v+b for v in z), d)
    print('verified explicit lifted permutations and integral exact covers through degree 14')
