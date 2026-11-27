"""Check cut ranks and the sparse implementation of the complement quadratic."""

from itertools import combinations
from math import isqrt
from random import Random


def graph(size):
    side = 2 * (isqrt(size) // 2)
    adj = [0] * size
    for i in range(side):
        for j in range(side):
            a = side * i + j
            for sign in (-1, 1):
                for b in (0, 1):
                    for v in (side * ((i + sign * (2 * j + b)) % side) + j,
                              side * i + (j + sign * (2 * i + b)) % side):
                        if v != a:
                            adj[a] |= 1 << v
    assert all(mask.bit_count() <= 8 for mask in adj)
    assert all((mask >> b) & 1 == (adj[b] >> a) & 1
               for a, mask in enumerate(adj) for b in range(size))
    return adj


def rank(rows):
    basis = {}
    for row in rows:
        while row:
            lead = row.bit_length() - 1
            if lead not in basis:
                basis[lead] = row
                break
            row ^= basis[lead]
    return len(basis)


def cut_ranks(adj, left):
    full = (1 << len(adj)) - 1
    right = full ^ sum(1 << v for v in left)
    sparse = rank([adj[v] & right for v in left])
    dense = rank([(~adj[v]) & right for v in left])
    assert abs(dense - sparse) <= 1
    return sparse, dense


def check_quadratic(adj):
    total = 0
    for data in range(1 << len(adj)):
        p = e = sparse = dense = 0
        for i, edges in enumerate(adj):
            bit = (data >> i) & 1
            e ^= p & bit
            p ^= bit
            if bit:
                earlier = data & ((1 << i) - 1)
                sparse ^= (edges & earlier).bit_count() & 1
                dense ^= ((~edges) & earlier).bit_count() & 1
        assert dense == (e ^ sparse)
        assert e == ((data.bit_count() * (data.bit_count() - 1) // 2) & 1)
        total += 1
    return total


def main():
    rng = Random(93407)
    cuts = 0
    summary = []
    for size in (4, 10, 16, 18, 36, 50, 64):
        adj = graph(size)
        if size <= 18:
            lefts = combinations(range(size), size // 2)
        else:
            lefts = (rng.sample(range(size), size // 2) for _ in range(250))
        ranks = [cut_ranks(adj, left) for left in lefts]
        summary.append((size, min(pair[1] for pair in ranks)))
        cuts += len(ranks)
    n = check_quadratic(graph(16))
    print(f"{cuts:,} cuts with rank change at most one; {n:,} complementary quadratics checked")
    print(f"Minimum tested complement ranks by size: {summary}")


if __name__ == "__main__":
    main()
