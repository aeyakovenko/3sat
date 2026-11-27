"""Independent field evaluation and cross-row quadratic correlations for two F4 rows."""

from fractions import Fraction
from itertools import combinations, product
from random import Random


def f4mul(a, b):
    raw = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
    return raw ^ (7 if raw & 4 else 0)  # x^2+x+1


def field_sign(row):
    a, b, z = row & 3, (row >> 2) & 3, row >> 4
    v = f4mul(f4mul(a, b), z)
    trace = v ^ f4mul(v, v)
    assert trace in (0, 1)
    return 1 - 2 * trace


def transform(values):
    values = values[:]
    stride = 1
    while stride < len(values):
        for start in range(0, len(values), 2 * stride):
            for i in range(start, start + stride):
                a, b = values[i], values[i + stride]
                values[i], values[i + stride] = a + b, a - b
        stride *= 2
    return values


def rank_one_cross():
    # Enumerate all within-row quadratic terms in Gray order. Each pair of
    # Walsh values in the same spectrum corresponds to two arbitrary frequencies.
    masks = [(1 << i) | (1 << j) for i, j in combinations(range(6), 2)]
    toggle = [[x for x in range(64) if (x & m) == m] for m in masks]
    values = [field_sign(x) for x in range(64)]
    pairs = set()
    for t in range(1 << len(masks)):
        if t:
            for x in toggle[(t & -t).bit_length() - 1]:
                values[x] *= -1
        spectrum = set(transform(values))
        assert max(map(abs, spectrum)) <= 28
        pairs.update(product(spectrum, repeat=2))

    # For cross term l(x)m(y), the sign has four separable terms with
    # coefficients +1/2,+1/2,+1/2,-1/2. The two local quadratics are independent.
    peak = max(abs(a*c + b*c + a*e - b*e) for a, b in pairs for c, e in pairs)
    assert peak == 2 * 784
    return len(pairs)


def arbitrary_cross():
    rng = Random(420131)
    base = [field_sign(x) for x in range(64)]
    for _ in range(256):
        def local():
            rows = [rng.getrandbits(i) for i in range(6)]
            frequency = rng.randrange(64)
            return [s * (-1) ** (((frequency & x).bit_count() +
                                   sum((row & x).bit_count() for i, row in enumerate(rows)
                                       if (x >> i) & 1)) % 2)
                    for x, s in enumerate(base)]

        left, right = local(), transform(local())
        cross = [rng.randrange(64) for _ in range(6)]
        total = 0
        for x in range(64):
            frequency = 0
            for i, mask in enumerate(cross):
                if x & (1 << i):
                    frequency ^= mask
            total += left[x] * right[frequency]
        assert abs(total) <= 784
    # Independently enumerate all 4096 inputs at the maximizing zero quadratic.
    assert sum(field_sign(x) * field_sign(y) for x, y in product(range(64), repeat=2)) == 784


def recurrence():
    for q in (2, 4, 8, 16, 32):
        u = Fraction(1, q)
        a, b = (1-u)*u**3 + 2*u**2, u*(1-2*u)
        beta = (2-u)*u
        assert a + b*beta == beta**2 and beta > b


if __name__ == "__main__":
    pairs = rank_one_cross()
    arbitrary_cross()
    recurrence()
    print(f"F4 two-row maximum 784/4096 attained. Checked all local quadratics with rank-at-most-one cross coupling ({pairs} spectral pairs), plus 256 arbitrary cross couplings.")
