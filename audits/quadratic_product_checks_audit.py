"""Finite checks for quadratic Boolean equations on the matrix product graph."""

import argparse
from itertools import combinations, product


def bit_positions(mask):
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length() - 1
        mask ^= lowest


def binary_product(left, right, side):
    """Packed GF(2) matrices in row-major order."""
    result = 0
    for index in bit_positions(left):
        row, shared = divmod(index, side)
        right_row = (right >> (shared * side)) & ((1 << side) - 1)
        result ^= right_row << (row * side)
    return result


def kernel_basis(rows, width):
    """Eliminate downward, then solve pivot coordinates from lowest to highest."""
    pivots = {}
    for row in rows:
        while row:
            high = row.bit_length() - 1
            if high not in pivots:
                pivots[high] = row
                break
            row ^= pivots[high]
    solutions = []
    for free in range(width):
        if free not in pivots:
            vector = 1 << free
            for pivot, row in sorted(pivots.items()):
                if (row & vector).bit_count() % 2:
                    vector |= 1 << pivot
            solutions.append(vector)
    return solutions


def span(basis):
    vectors = {0}
    for v in basis:
        vectors |= {v ^ existing for existing in vectors}
    return vectors


def graph_quadric_audit(side, exhaustive):
    count = side * side
    variables = range(3 * count)
    monomials = [(), *((i,) for i in variables), *combinations(variables, 2)]
    bit = {monomial: 1 << i for i, monomial in enumerate(monomials)}

    def feature_row(left, right):
        claim = binary_product(left, right, side)
        ones = list(bit_positions(left | (right << count) | (claim << (2 * count))))
        return 1 | sum(bit[(i,)] for i in ones) | sum(bit[pair] for pair in combinations(ones, 2))

    residuals = []
    for i, j in product(range(side), repeat=2):
        output = bit[(2 * count + side * i + j,)]
        terms = (bit[(side * i + k, count + side * k + j)] for k in range(side))
        residuals.append(output | sum(terms))
    expected = span(residuals)
    assert len(expected) == 1 << count

    def check(inputs, label):
        rows = (feature_row(a, b) for a, b in product(inputs, repeat=2))
        basis = kernel_basis(rows, len(monomials))
        assert len(basis) == count
        assert span(basis) == expected
        print(f"d={side} {label}: {len(inputs)**2} graph points, {len(monomials)} monomials, "
              f"rank {len(monomials) - count}, all {len(expected)} kernel elements matched")

    matrices = range(1 << count)
    check([a for a in matrices if a.bit_count() <= 2], "weight <= 2 per input")
    if exhaustive:
        check(matrices, "unrestricted inputs")


def field_tables(modulus):
    """Small GF(2^e) in its polynomial basis using an irreducible modulus."""
    size = 1 << (modulus.bit_length() - 1)

    def multiply(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            a <<= 1
            if a & size:
                a ^= modulus
            b >>= 1
        return result

    times = [[multiply(a, b) for b in range(size)] for a in range(size)]
    inverses = [0] + [times[a].index(1) for a in range(1, size)]
    return times, inverses


def solve_square(matrix, vector, times, inverses):
    rows = [list(row) + [value] for row, value in zip(matrix, vector)]
    dim = len(rows)
    for i in range(dim):
        pivot = next(j for j in range(i, dim) if rows[j][i])
        rows[i], rows[pivot] = rows[pivot], rows[i]
        scale = inverses[rows[i][i]]
        rows[i] = [times[scale][x] for x in rows[i]]
        for j in range(dim):
            if j != i and rows[j][i]:
                factor = rows[j][i]
                rows[j] = [x ^ times[factor][y] for x, y in zip(rows[j], rows[i])]
    return tuple(row[-1] for row in rows)


def xor_sum(values):
    result = 0
    for value in values:
        result ^= value
    return result


def syndrome_audit(side, modulus):
    times, inverses = field_tables(modulus)
    full = [[1] * side]
    for _ in range(1, side):
        full.append([times[value][alpha] for alpha, value in enumerate(full[-1])])
    column_masks = range(1 << side)
    syndromes = [tuple(xor_sum(row[i] for i in bit_positions(mask)) for row in full)
                 for mask in column_masks]
    for r in range(1, side + 1):
        invisible = [mask for mask in column_masks if mask and not any(syndromes[mask][:r])]
        assert all(mask.bit_count() > r for mask in invisible)
        for active in combinations(range(side), r):
            vandermonde = [[row[i] for i in active] for row in full[:r]]
            for values in product((0, 1), repeat=r):
                mask = sum(bit << i for i, bit in zip(active, values))
                assert solve_square(vandermonde, syndromes[mask][:r], times, inverses) == values
        minimum = min((mask.bit_count() for mask in invisible), default="no nonzero kernel")
        print(f"d={side} r={r}: all {1 << side} binary columns checked, "
              f"minimum invisible weight {minimum}; all restricted rows recovered")

    def column(matrix, j):
        return sum(((matrix >> (i * side + j)) & 1) << i for i in range(side))

    # Exhaust every pair of binary matrices at side two. At larger sides test
    # all pairs of elementary matrices, which span both inputs of this identity.
    matrices = range(1 << (side * side)) if side == 2 else [1 << j for j in range(side * side)]
    for left, right in product(matrices, repeat=2):
        projected_left = [syndromes[column(left, k)] for k in range(side)]
        expected = binary_product(left, right, side)
        for j in range(side):
            support = tuple(bit_positions(column(right, j)))
            actual = tuple(xor_sum(projected_left[k][a] for k in support) for a in range(side))
            assert actual == syndromes[column(expected, j)]
    print(f"d={side}: L(AB)=(LA)B checked on {len(matrices)**2} input pairs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-three", action="store_true",
                        help="also eliminate on all 262144 input pairs at side three")
    args = parser.parse_args()
    graph_quadric_audit(2, exhaustive=True)
    graph_quadric_audit(3, exhaustive=args.full_three)
    for side in (2, 3, 4):
        syndrome_audit(side, 0b111)  # GF(4), modulo x^2+x+1

    # In characteristic two c+a^2 b has zero formal mixed a,b derivative.
    # On binary inputs it vanishes on c=ab, but on GF(4) it fails there.
    times, _ = field_tables(0b111)
    assert all(not (times[a][b] ^ times[times[a][a]][b]) for a, b in product((0, 1), repeat=2))
    assert times[2][1] ^ times[times[2][2]][1]
    print("c+a^2 b passes the binary graph and fails at a=2, b=1 in GF(4)")


if __name__ == "__main__":
    main()
