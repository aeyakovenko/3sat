"""Finite checks for simultaneous interval packing and sampled Boolean word lookups."""

from itertools import combinations_with_replacement, product
from math import isqrt


def check_packing(d):
    shapes = list(combinations_with_replacement(range(d + 1), d))
    # A row stores the length of its initial interval of missing cells.
    # For each side and start record the bit set of possible next starts.
    transitions = {}
    for shape in shapes:
        for h in range(1, d + 1):
            q = d - h + 1
            transitions[shape, h] = tuple(
                sum(1 << col for col in range(q) if col >= shape[row + h - 1])
                for row in range(q)
            )
    for masks in product(shapes, repeat=3):
        h = d - isqrt(sum(sum(mask) for mask in masks))
        if h <= 0:
            continue
        ab, bc, ca = (transitions[mask, h] for mask in masks)
        assert any(
            ab[i] & (1 << j) and bc[j] & (1 << k) and ca[k] & (1 << i)
            for i, j, k in product(range(len(ab)), repeat=3)
        )
    for h in range(1, d + 1):
        q = d - h + 1
        extremal = (0,) * (h - 1) + (q,) * q
        assert sum(extremal) == q * q and not any(transitions[extremal, h])
    return len(shapes) ** 3


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def cube(table, x, u, v, w):
    return (table[x] ^ table[x ^ u] ^ table[x ^ v] ^ table[x ^ w]
            ^ table[x ^ u ^ v] ^ table[x ^ u ^ w] ^ table[x ^ v ^ w]
            ^ table[x ^ u ^ v ^ w])


def check_lookup(r):
    n = 1 << r
    table = [int(x == n - 1) for x in range(n)]
    signatures = range(1, n)
    rows = []
    for u in signatures:
        bits = bytearray((n - 1) ** 2)
        for j, v in enumerate(signatures):
            for k, w in enumerate(signatures):
                bits[j * (n - 1) + k] = cube(table, 0, u, v, w)
        # Embedding each binary column into a separate byte preserves rank.
        rows.append(int.from_bytes(bits, 'little'))
    assert binary_rank(rows) == n - r - 2


if __name__ == '__main__':
    count = sum(check_packing(d) for d in range(1, 5))
    for width in range(3, 8):
        check_lookup(width)
    print(f'{count:,} Ferrers triples through side four; AND flattenings through seven bits')
