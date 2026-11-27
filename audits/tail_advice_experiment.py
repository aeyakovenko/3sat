"""Check rank loss when binary polynomial coefficients lie in a known interval."""

from collections import Counter
from itertools import combinations

from coded_diagonal_experiment import binary_dot, irreducibles, residue


def normal(modulus, mask, width):
    return sum(binary_dot(mask, residue(1 << j, modulus)) << j for j in range(width))


def eliminate(rows):
    """Return rank and, if present, one nonzero XOR relation between the rows."""
    pivots = {}
    relation = 0
    for i, value in enumerate(rows):
        provenance = 1 << i
        while value:
            index = value.bit_length() - 1
            if index not in pivots:
                pivots[index] = value, provenance
                break
            pivot, source = pivots[index]
            value ^= pivot
            provenance ^= source
        else:
            relation = provenance
    return len(pivots), relation


def rank(rows):
    return eliminate(rows)[0]


def public_group(degree, moduli, width, offset, size):
    interval = ((1 << size) - 1) << offset
    basis_rows = [normal(f, 1 << j, width) for f in moduli for j in range(degree)]
    assert rank(basis_rows) == len(basis_rows)
    _, dependency = eliminate(row & interval for row in basis_rows)
    mask_bits = (1 << degree) - 1
    masks = [(dependency >> (degree * k)) & mask_bits for k in range(len(moduli))]
    assert all(masks)
    rows = [normal(f, mask, width) for f, mask in zip(moduli, masks)]
    assert rank(rows) == len(moduli)
    assert rank(row & interval for row in rows) == len(moduli) - 1
    combined = 0
    for row in rows:
        combined ^= row
    assert combined & interval == 0


def check_construction():
    total = 0
    for degree in (4, 5):
        moduli = irreducibles(degree)
        for count in range(3, len(moduli) + 1):
            for group in combinations(moduli, count):
                width = degree * count + 2
                for size in range(degree * (count - 1), degree * count):
                    for offset in range(width - size + 1):
                        public_group(degree, group, width, offset, size)
                        total += 1
    print(f"Verified the one-bit gain on {total} modulus groups and intervals")


def check_obstruction():
    degree, width, size, offset = 4, 14, 8, 3
    interval = ((1 << size) - 1) << offset
    rows = [normal(f, mask, width) for f in irreducibles(degree)
            for mask in range(1, 1 << degree)]
    ranks = Counter()
    for four in combinations(rows, 4):
        if rank(four) == 4:
            ranks[rank(row & interval for row in four)] += 1
    assert min(ranks) == 3 and max(ranks) == 4
    print(f"Exhausted all {len(rows)} masks in groups of four; restricted ranks {dict(ranks)}")


if __name__ == "__main__":
    check_construction()
    check_obstruction()
