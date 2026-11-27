"""Exact four-dimensional checks for quadratic forms from linearized polynomials.

The field is GF(2)[X]/(X^4 + X + 1). The low coefficient gives the linear
functional. These checks concern only dimension four and t in {1, 2}.
"""

from collections import Counter
from itertools import combinations, permutations


DIM = 4
FIELD_SIZE = 1 << DIM
MODULUS = 0b10011
COORDS = tuple(1 << bit for bit in range(DIM))


def product(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & FIELD_SIZE:
            a ^= MODULUS
    return result


def pivots(rows):
    """Return a basis of the binary row span using integer bit masks."""
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return tuple(basis.values())


def row_masks(t):
    """Mask bit 4j+k is B(x,y) for the seed with a_j = X^k alone."""
    quad_values = [[] for _ in range(FIELD_SIZE)]
    for x in range(FIELD_SIZE):
        power = x
        for _ in range(2 * t):
            for k in COORDS:
                q = product(x, product(k, power))
                quad_values[x].append(q & 1)
            power = product(power, power)
    qmask = [sum(bit << i for i, bit in enumerate(bits)) for bits in quad_values]
    return [[qmask[x] ^ qmask[y] ^ qmask[x ^ y] for y in range(FIELD_SIZE)]
            for x in range(FIELD_SIZE)]


def rectangular_test(masks, t, ordered_bases):
    for basis in ordered_bases:
        xs, ys = basis[:t], basis[t:]
        rows = [masks[x][y] for x in xs for y in ys]
        assert len(pivots(rows)) == t * (DIM - t), (xs, ys)
    # A rectangle with fewer y's is a coordinate projection of a tested
    # rectangle since its independent directions can be completed to a basis.


def cut_histogram(masks, t):
    pairs = list(combinations(range(DIM), 2))
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    # A coordinate vector of the seed space maps to one alternating form.
    columns = []
    for seed_bit in range(DIM * 2 * t):
        columns.append(sum(((masks[COORDS[i]][COORDS[j]] >> seed_bit) & 1) << k
                           for k, (i, j) in enumerate(pairs)))
    forms = [0]
    for vector in pivots(columns):
        forms += [form ^ vector for form in forms]
    histogram = Counter()
    for form in forms:
        ranks = []
        # A cut and its complement have transposed cross matrices.
        for rest in range(1, DIM):
            side = (0, rest)
            other = [j for j in range(DIM) if j not in side]
            rows = []
            for i in side:
                row = 0
                for column, j in enumerate(other):
                    bit = pair_index[tuple(sorted((i, j)))]
                    row |= ((form >> bit) & 1) << column
                rows.append(row)
            ranks.append(len(pivots(rows)))
        histogram[min(ranks)] += 1
    return len(forms), dict(sorted(histogram.items()))


if __name__ == "__main__":
    assert all(any(product(a, b) == 1 for b in range(1, FIELD_SIZE))
               for a in range(1, FIELD_SIZE))
    bases = [basis for basis in permutations(range(1, FIELD_SIZE), DIM)
             if len(pivots(basis)) == DIM]
    assert len(bases) == 20160
    for t in (1, 2):
        masks = row_masks(t)
        rectangular_test(masks, t, bases)
        num_forms, histogram = cut_histogram(masks, t)
        print(f"t={t}: all {len(bases)} ordered bases passed; "
              f"{num_forms} distinct forms; minimum balanced coordinate-cut "
              f"rank counts {histogram}")
