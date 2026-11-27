"""Check the sparse cut estimates using exact counts and Walsh signs."""

from itertools import combinations, product
from math import comb


def parity(x):
    return x.bit_count() % 2


def image(matrix, y):
    return sum(parity(row & y) << i for i, row in enumerate(matrix))


def check_cosets():
    checked = 0
    for m in (1, 2, 3):
        length = 1 << m
        rank_counts = [0] * (m+1)
        for mat in product(range(length), repeat=m):
            outputs = [image(mat, y) for y in range(length)]
            code = set(outputs)
            k = len(code).bit_length() - 1
            ones = sum(row.bit_count() for row in mat)
            rank_counts[k] += 3 ** (m*m - ones)
            for p in range(m+1):
                ball = {x for x in range(length) if x.bit_count() <= p}
                counts = [0] * length
                for z in outputs:
                    for j in ball:
                        counts[z ^ j] += 1
                bound = sum(comb(k, i) for i in range(min(k, p)+1))
                for v, count in enumerate(counts):
                    intersection = len({v ^ u for u in code} & ball)
                    assert count == (length // len(code)) * intersection
                    assert intersection <= bound
                if code == set(range(1 << k)):
                    assert max(counts) == length // len(code) * bound
                # The Gram matrix depends only on the difference of its indices.
                gram = [sum((-1)**parity(delta & (z ^ j))
                            for z in outputs for j in ball) for delta in range(length)]
                for v in range(length):
                    eigen = sum(g * (-1)**parity(delta & v) for delta, g in enumerate(gram))
                    assert eigen == length * counts[v]
                checked += 1
        assert sum(rank_counts) == 4 ** (m*m)
        for d in range(1, m+1):
            left = sum(rank_counts[:m-d+1])
            assert left * 4 ** (d*d) <= 4 ** (m*m) * comb(m,d) * 3 ** (d*d)
    return checked


def check_tensor():
    total = 0
    for m in (1, 2, 3, 4):
        for x, y, i, j in product(range(1 << m), repeat=4):
            lifted = parity(x & y) ^ parity(i & y) ^ parity(x & j)
            factored = parity((x ^ i) & (y ^ j)) ^ parity(i & j)
            assert lifted == factored
            total += 1
    return total


def check_covers():
    checked = 0
    for m in range(1, 9):
        length = 1 << m
        for p in range(m+1):
            ball = {j for j in range(length) if j.bit_count() <= p}
            missing = set(range(length)) - ball
            generators = []
            while missing:
                old = len(missing)
                new, g = min((sum(y ^ x in missing for y in missing), x)
                             for x in range(length))
                assert new * length <= old * old
                missing = {y for y in missing if y ^ g in missing}
                assert len(missing) == new
                generators.append(g)
            code = {0}
            for g in generators:
                code |= {x ^ g for x in code}
            assert all(any(x ^ z in ball for z in code) for x in range(length))
            assert 2**len(generators)*len(ball) <= 4 * (m+1) * length
            checked += 1
    return checked


def check_free_edge():
    n = 4
    edges = list(combinations(range(n), 2))
    checked = 0
    for graph in range(1 << len(edges)):
        pairs = [e for i,e in enumerate(edges) if graph >> i & 1]
        table = [sum((x >> i & 1) * (x >> j & 1) for i,j in pairs) % 2
                 for x in range(1 << n)]
        for free in range(1 << n):
            for fixed in range(1 << n):
                if fixed & free:
                    continue
                if any(free >> i & free >> j & 1 for i,j in pairs):
                    values = {v for x,v in enumerate(table) if x & ~free == fixed}
                    assert values == {0, 1}
                checked += 1
    return checked


def check_adaptive_states():
    n = 4
    universe = (1 << n) - 1
    candidates = list(combinations(range(n), 2))
    checked = 0
    for graph in range(1 << len(candidates)):
        edges = [pair for i, pair in enumerate(candidates) if (graph >> i) & 1]
        neighbors = [sum(1 << (b if v == a else a) for a,b in edges if v in (a,b))
                     for v in range(n)]
        values = [sum((x >> a & 1) * (x >> b & 1) for a,b in edges) % 2
                  for x in range(1 << n)]
        for alternate in (1, 2, 3):
            # First read pin zero, then choose an address from its returned bit.
            leaves = {}
            for x in range(1 << n):
                second = alternate if (x & 1) else 1
                mask = 1 | (1 << second)
                leaves.setdefault((mask, x & mask), []).append(x)
            for flags in range(1, 1 << len(leaves)):
                group = [item for i,item in enumerate(leaves.items()) if flags >> i & 1]
                prior = 0
                data = []
                for (mask, _), points in group:
                    prior |= mask
                    data.extend(points)
                outside = universe ^ prior
                for future in range(1 << n):
                    relation = {(x & future, values[x]) for x in data}
                    if len(relation) != len({key for key, _ in relation}):
                        continue
                    rows = [neighbors[v] & outside for v in range(n)
                            if (prior & ~future) >> v & 1]
                    column_span = {image(rows, y) for y in range(1 << n)}
                    assert len(data) * len(column_span) <= 1 << n
                    checked += 1
    return checked


if __name__ == '__main__':
    print(f'{check_cosets()} cut-matrix/radius spectra, {check_tensor()} tensor entries, '
          f'{check_covers()} covering codes, {check_free_edge()} graph/subcube pairs, '
          f'{check_adaptive_states()} adaptive resumable states')
