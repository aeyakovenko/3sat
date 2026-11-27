"""Exact small free games, including unbounded-degree addresses and a bad partition."""

from collections import Counter
from fractions import Fraction
from itertools import product
from random import Random


def multiply(a, b, q):
    reduction = {2: 0b11, 4: 0b111, 8: 0b1011}[q]
    total = 0
    while b:
        if b & 1:
            total ^= a
        a <<= 1
        if a & q:
            a ^= reduction
        b >>= 1
    return total


def columns(q):
    return [[q * x + y for y in range(q)] for x in range(q)]


def lines(q, slope):
    return [[q * x + (multiply(slope, x, q) ^ c) for x in range(q)] for c in range(q)]


def overlap(queries):
    degrees = Counter(z for row in queries for z, v in row)
    addresses = [{z for z, v in row} for row in queries]
    return [[sum((Fraction(1, degrees[z]) for z in a & b), Fraction())
             for b in addresses] for a in addresses]


def base_gap(queries):
    addresses = sorted({z for row in queries for z, v in row})
    def failed(values):
        proof = dict(zip(addresses, values))
        return sum(any(proof[z] != v for z, v in row) for row in queries)
    return Fraction(min(failed(bits) for bits in product((0, 1), repeat=len(addresses))),
                    len(queries))


def line_rejections(queries, left, right):
    # Each local test has one acceptable assignment. A collection of left
    # columns can all pass exactly when they agree on the relevant addresses.
    q = len(left)
    rejected = 0
    for line in right:
        requested = {z for s in line for z, v in queries[s]}
        relevant = [[(z, v) for s in col for z, v in queries[s] if z in requested]
                    for col in left]
        best = 0
        for mask in range(1 << q):
            size = mask.bit_count()
            if size <= best:
                continue
            records = {(z, v) for i in range(q) if mask & (1 << i) for z, v in relevant[i]}
            if not any((z, 1-v) in records for z, v in records):
                best = size
        rejected += q - best
    return rejected


def audit(queries, q):
    n, width = q * q, max(len(row) for row in queries)
    kernel = overlap(queries)
    assert max(map(sum, kernel)) <= width
    left, gap = columns(q), base_gap(queries)
    energies = []
    for slope in range(q):
        right = lines(q, slope)
        assert all(len(set(i) & set(j)) == 1 for i in left for j in right)
        loads = [sum(kernel[s][v] for s in j for v in i) for i in left for j in right]
        energy = sum(x*x for x in loads)
        energies.append(energy)
        bad = line_rejections(queries, left, right)
        assert (gap * n / 2) ** 2 <= bad * sum((width + x)**2 for x in loads)
        if energy <= 2 * width**2 * n:
            assert Fraction(bad, n) >= gap**2 / (24 * width**2)
        merged_left = [left[i] + left[i + 1] for i in range(0, q, 2)]
        merged_right = [right[i] + right[i + 1] for i in range(0, q, 2)]
        coarse_bad = line_rejections(queries, merged_left, merged_right)
        assert 4 * coarse_bad >= bad
    assert sum(energies)/q <= 2 * width**2 * n


def transpose(q):
    queries = [[] if x == y else [((min(x,y), max(x,y)), int(x < y))]
               for x in range(q) for y in range(q)]
    left = columns(q)
    counts = [line_rejections(queries, left, lines(q,a)) for a in range(q)]
    assert counts[0] == q
    # Every nonidentity permutation has at most one fixed point. The identity
    # line, if present, can occur for at most one intercept at a nonzero slope.
    assert all(n * 2 >= (q-1)**2 for n in counts[1:])
    return counts


def main():
    rng = Random(271)
    first = [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]
    count = 0
    for assignment in product(first, repeat=4):
        audit([[item] for item in assignment], 2)
        count += 1
    for _ in range(80):
        queries = [[(z, rng.randrange(2)) for z in rng.sample(range(7), rng.randrange(1,4))]
                   for s in range(16)]
        audit(queries, 4)
        count += 1
    print(f"{count} PCP instances checked against exact rejections, energies and two-bin merges")
    for q in (2,4,8):
        print(f"GF({q}) transpose rejecting cells by slope: {transpose(q)} / {q*q}")


if __name__ == "__main__":
    main()
