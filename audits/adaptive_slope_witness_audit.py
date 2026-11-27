"""Check exact kernels and lifted binary matrices for adaptive slope tests."""

from itertools import combinations, product
from random import Random


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            i = row.bit_length() - 1
            if i not in pivots:
                pivots[i] = row
                break
            row ^= pivots[i]
    return len(pivots)


def rows_from_mask(side, mask):
    low = (1 << side) - 1
    return [(mask >> (i * side)) & low for i in range(side)]


def slope_reply(rows, slope):
    result = 0
    for i, row in enumerate(rows):
        while row:
            low = row & -row
            j = low.bit_length() - 1
            result ^= 1 << (i + slope * j)
            row ^= low
    return result


def switch(slopes):
    rows = [1]
    for q in slopes:
        new = [0] * (len(rows) + q)
        for i, value in enumerate(rows):
            new[i] ^= value << 1
            new[i + q] ^= value
        rows = new
    return rows


def parity(value):
    return value.bit_count() & 1


def nonzero_kernel(equations, width):
    """Eliminate the high pivot, then set a free bit and back-substitute."""
    pivots = {}
    for value in equations:
        while value:
            i = value.bit_length() - 1
            if i not in pivots:
                pivots[i] = value
                break
            value ^= pivots[i]
    free = next(i for i in range(width) if i not in pivots)
    solution = 1 << free
    for i, equation in sorted(pivots.items()):
        if parity(solution & equation):
            solution |= 1 << i
    assert all(not parity(row & solution) for row in equations)
    return solution


def multiply_binary(a, b):
    out = 0
    while a:
        low = a & -a
        out ^= b << (low.bit_length() - 1)
        a ^= low
    return out


def exhaustive():
    cases = 0
    for d in range(1, 5):
        allowed = range(1, d + 1)
        subsets = [s for k in range(d + 1) for s in combinations(allowed, k)]
        masses = {s: 0 for s in subsets}
        minima = {}
        for bits in range(1 << (d * d)):
            rows = rows_from_mask(d, bits)
            invisible = tuple(q for q in allowed if not slope_reply(rows, q))
            matrix_rank = rank(rows)
            for k in range(len(invisible) + 1):
                for s in combinations(invisible, k):
                    masses[s] += 1
                    if bits:
                        minima[s] = min(minima.get(s, d), matrix_rank)
        for s in subsets:
            dimension = max(d - sum(s), 0) * max(d - len(s), 0)
            assert masses[s] == 1 << dimension
            assert minima.get(s) == (len(s) + 1 if dimension else None)
            if dimension:
                ghost = switch(s)
                assert rank(ghost) == len(s) + 1
                assert parity(ghost[0]) and all(not slope_reply(ghost, q) for q in s)
            cases += 1
    return cases


def mixed_checks():
    rng = Random(41272)
    cases = 0
    for d, slopes in product((17, 31, 48), ((), (1,), (2, 3), (1, 3, 4))):
        base = switch(slopes)
        k = len(slopes)
        left = [rng.getrandbits(d) for _ in range(2)]
        right = [rng.getrandbits(d) for _ in range(2)]
        scalars = [[rng.getrandbits(d) for _ in range(d)] for _ in range(3)]
        a, b = d - sum(slopes), d - k
        if a <= len(left) * (k + 1) + len(scalars) or b <= len(right) * (k + 1):
            continue
        eq_q = [(v >> j) & ((1 << b) - 1) for v in right for j in range(k + 1)]
        q_poly = nonzero_kernel(eq_q, b)
        rows = [multiply_binary(row, q_poly) for row in base]

        def conditions(shift):
            values = []
            for u in left:
                merged = 0
                for i, row in enumerate(base):
                    if (u >> (i + shift)) & 1:
                        merged ^= row
                values.extend((merged >> j) & 1 for j in range(k + 1))
            values.extend(sum(parity(row & test[i + shift]) for i, row in enumerate(rows)) % 2
                          for test in scalars)
            return values

        eq_r = [sum(bit << t for t, bit in enumerate(condition))
                for condition in zip(*(conditions(t) for t in range(a)))]
        r_poly = nonzero_kernel(eq_r, a)
        final = [0] * d
        for t in range(a):
            if r_poly & (1 << t):
                for i, row in enumerate(rows):
                    final[t + i] ^= row
        assert rank(final) == k + 1
        assert all(not slope_reply(final, q) for q in slopes)
        assert all(not parity(row & v) for row in final for v in right)
        assert all(sum((u >> i & 1) * (row >> j & 1) for i, row in enumerate(final)) % 2 == 0
                   for u in left for j in range(d))
        assert all(sum(parity(row & mask) for row, mask in zip(final, test)) % 2 == 0
                   for test in scalars)
        cases += 1
    return cases


if __name__ == '__main__':
    print(f'{exhaustive()} complete slope kernels at sides 1 through 4')
    print(f'{mixed_checks()} constructed witnesses against simultaneous full-vector and scalar tests')
