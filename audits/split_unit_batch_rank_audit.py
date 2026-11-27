"""Compare the interaction formula with independent exact rational ranks."""
from itertools import product
from math import gcd

from first_missing_packed_example import satisfiable


def exact_rank(rows):
    pivots = {}
    for row in rows:
        row = list(row)
        for j in range(len(row)):
            if not row[j]:
                continue
            if j not in pivots:
                pivots[j] = row
                break
            pivot = pivots[j]
            a, b = pivot[j], row[j]
            for k in range(j, len(row)):
                row[k] = a * row[k] - b * pivot[k]
            divisor = gcd(*row)
            if divisor > 1:
                row = [v // divisor for v in row]
    return len(pivots)


def verdict_masks(q, s, t):
    words = list(product(range(q), repeat=s * t))
    return [[sum(1 << i for i in range(t)
                 if all(a[i*s+j] != b[i*s+j] for j in range(s)))
             for b in words] for a in words]


def interaction_rank(table, K, d, t):
    total = 0
    for subset in range(1 << t):
        weight = 0
        for z, value in enumerate(table):
            pos = (z & ~subset).bit_count()
            neg = t - subset.bit_count() - pos
            sign = (-1) ** ((~z & subset).bit_count())
            weight += value * sign * d**pos * (K - d)**neg
        if weight:
            total += (K - 1)**subset.bit_count()
    return total


def test_all(q, s, t):
    K, d = q**s, (q-1)**s
    masks = verdict_masks(q, s, t)
    tests = 0
    for table in product((0, 1), repeat=1 << t):
        matrix = ([table[x] for x in row] for row in masks)
        actual = exact_rank(matrix)
        expected = interaction_rank(table, K, d, t)
        assert actual == expected, (q, s, t, table, actual, expected)
        top = sum(((-1) ** (t-z.bit_count())) * v for z, v in enumerate(table))
        if top % K:
            assert actual == K**t
        if not top:
            assert actual < K**t
        tests += 1
    print(f'q={q}, s={s}, t={t}: {tests} exact ranks')


def test_sharpness(q, s):
    K, d = q**s, (q-1)**s
    r = (max(d, K-d)-1).bit_length() + 1
    t = r+1
    table = [0] * (1 << t)
    minus = [z for z in range(1 << r) if (r-z.bit_count()) % 2]
    plus = [z for z in range(1 << r) if not (r-z.bit_count()) % 2]
    for z in minus[:d]:
        table[z] = 1
    for z in plus[:K-d]:
        table[z | (1 << r)] = 1
    rank = interaction_rank(table, K, d, t)
    top = sum((-1)**(t-z.bit_count()) * v for z, v in enumerate(table))
    assert top == K and K**t - rank >= (K-1)**r
    return t


def test_split_formulas():
    # Two blocks, two positions, two symbols. Clauses forbidding output
    # assignments implement all 16 two-input Boolean aggregates exactly.
    tested = 0
    words = list(product((0, 1), repeat=4))
    for alice, bob in product(words, repeat=2):
        clauses = []
        outcome = 0
        for i in range(2):
            z = i + 1
            pick = [3 + 2*i + j for j in range(2)]
            mark = [7 + 2*i + u for u in range(2)]
            clauses.extend([(z, *pick), (-mark[0], -mark[1])])
            unequal = True
            for j in range(2):
                a, b = alice[2*i+j], bob[2*i+j]
                x = 11 + 4*i + 2*j
                clauses.extend([(-z, x+a), (-z, -(x+b)),
                                (-pick[j], mark[a]), (-pick[j], mark[b])])
                unequal = unequal and a != b
            outcome += int(unequal) << i
        for table in product((0, 1), repeat=4):
            forbidden = [tuple(-(i+1) if z & (1 << i) else i+1 for i in range(2))
                         for z, v in enumerate(table) if not v]
            assert satisfiable(clauses + forbidden) == bool(table[outcome])
            tested += 1
    print(f'{tested} split width-three formulas solved by independent DPLL')


if __name__ == '__main__':
    test_split_formulas()
    for params in [(2, 1, 3), (3, 1, 3), (2, 2, 2), (3, 2, 2)]:
        test_all(*params)
    examples = [(q, s, test_sharpness(q, s))
                for q in range(2, 7) for s in (1, 2)]
    print(f'Divisibility counterexamples (q,s,t): {examples}')
