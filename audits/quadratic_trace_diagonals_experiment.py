"""Exhaustive small checks for quadratic-trace-diagonals.md. Uses only Python."""

from collections import Counter, defaultdict
from itertools import product


def parity(value):
    return value.bit_count() % 2


def matvec(rows, x):
    return sum(parity(row & x) << i for i, row in enumerate(rows))


def transpose(rows, width):
    return [sum(((row >> j) & 1) << i for i, row in enumerate(rows)) for j in range(width)]


def diagonal(rows):
    return sum((row & (1 << i)) for i, row in enumerate(rows))


def span(vectors):
    values = {0}
    for v in vectors:
        values.update([x ^ v for x in values])
    return values


def all_symmetric(n):
    positions = [(i, j) for i in range(n) for j in range(i, n)]
    for bits in range(1 << len(positions)):
        rows = [0] * n
        for k, (i, j) in enumerate(positions):
            if bits & (1 << k):
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        yield rows


def check_quadratics():
    for rows in product(range(8), repeat=3):
        agrees = all(parity(s & matvec(rows, s)) == parity(s & diagonal(rows)) for s in range(8))
        assert agrees == (list(rows) == transpose(rows, 3))
    return 8**3


def check_fibers():
    n = 4
    # Entries in a cached row are the only information available to the query algorithm.
    data = [(diagonal(rows), [matvec(rows, x) for x in range(1 << n)]) for rows in all_symmetric(n)]
    count = 0
    for first, second in product(range(1 << n), repeat=2):
        for adaptive in (False, True):
            fibers = defaultdict(Counter)
            for diag, answers in data:
                reply = answers[first]
                chosen = (second ^ reply) if adaptive else second
                fibers[(reply, chosen, answers[chosen])][diag] += 1
            for (_, chosen, _), histogram in fibers.items():
                assert len(histogram) * len(span([first, chosen])) == 1 << n
                assert len(set(histogram.values())) == 1
            count += 1
    return count


def combine(vectors, selector):
    value = 0
    for i, vector in enumerate(vectors):
        if selector & (1 << i):
            value ^= vector
    return value


def check_blocks():
    count = 0
    for rows in product(range(8), repeat=2):
        transposed = transpose(rows, 3)
        size = len(span(rows))
        for left in product(range(8), repeat=2):
            y = [matvec(rows, x) for x in left]
            if len(span(y)) != size:
                continue
            for right in product(range(4), repeat=2):
                z = [matvec(transposed, x) for x in right]
                if len(span(z)) != size:
                    continue
                # A projected vector identifies its image uniquely, even when
                # more than one combination of sample columns represents it.
                recover = {}
                for selector in range(4):
                    vec = combine(y, selector)
                    key = matvec(right, vec)
                    assert recover.setdefault(key, vec) == vec
                for x in range(8):
                    assert recover[matvec(z, x)] == matvec(rows, x)
                count += 1
    return count


def gf4_mul(x, y):
    # Binary polynomial basis; bit 1 is a and a²=a+1.
    doubled = (x << 1) ^ (0b111 if x & 2 else 0)
    return (x if y & 1 else 0) ^ (doubled if y & 2 else 0)


def gf4_pow(x, exponent):
    value = 1
    for _ in range(exponent):
        value = gf4_mul(value, x)
    return value


def gf4_rank(matrix):
    rows = [row[:] for row in matrix]
    rank = 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[pivot], rows[rank] = rows[rank], rows[pivot]
        scale = gf4_pow(rows[rank][j], 2)  # nonzero elements have order dividing 3
        rows[rank] = [gf4_mul(scale, u) for u in rows[rank]]
        for i in range(rank + 1, len(rows)):
            scale = rows[i][j]
            rows[i] = [u ^ gf4_mul(scale, v) for u, v in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def check_critical_point():
    alphabet = (0, 1, 2)
    theta = 3
    monomials = [(i, j) for i in range(4) for j in range(4 - i)]
    evaluations = [
        [gf4_mul(gf4_pow(x, i), gf4_pow(y, j)) for i, j in monomials]
        for x, y in product(alphabet, repeat=2)
    ]
    first = [gf4_pow(theta, i + j - 1) if i % 2 else 0 for i, j in monomials]
    second = [gf4_pow(theta, i + j - 1) if j % 2 else 0 for i, j in monomials]
    rank = gf4_rank(evaluations)
    # Both derivative functionals vanish on every polynomial that vanishes
    # on the grid, since adding their rows leaves the evaluation rank fixed.
    assert rank == gf4_rank(evaluations + [first, second]) == 8
    # Enumerate the field-linear span, in two-bit packed coordinates, and
    # verify the exact minimum nonzero Hamming weight on the nine points.
    words = {0}
    for col in zip(*evaluations):
        words_generated = [sum(gf4_mul(a, v) << (2 * i) for i, v in enumerate(col))
                           for a in range(4)]
        if words_generated[1] not in words:
            words = {old ^ new for old in words for new in words_generated}
    assert len(words) == 4**rank
    even_bits = sum(1 << (2 * i) for i in range(9))
    weight = min(((word | (word >> 1)) & even_bits).bit_count() for word in words if word)
    assert weight == 2
    # y*x*(x+1) meets this weight and its y derivative at theta is nonzero.
    assert gf4_mul(theta, theta ^ 1) != 0
    return rank, weight


if __name__ == "__main__":
    print(f"quadratic matrices checked: {check_quadratics()}")
    print(f"two-query strategies and all their fibers checked: {check_fibers()}")
    print(f"full-rank sketch pairs for 2-by-3 blocks checked: {check_blocks()}")
    grid_rank, min_weight = check_critical_point()
    print(f"GF(4) grid rank before and after adjoining both gradients: {grid_rank}")
    print(f"minimum nonzero weight among all {4**grid_rank} cubic grid functions: {min_weight}/9")
