"""Exact rank-distance syndrome sizes and packed product formula in small binary fields."""

from itertools import product
from folded_product_band_audit import BinaryField, binary_rank, product_bits, xor


def field_power(x, exponent, field):
    result = 1
    while exponent:
        if exponent & 1:
            result = field.mul(result, x)
        x = field.mul(x, x)
        exponent >>= 1
    return result


def trace(x, d, field):
    value = 0
    for _ in range(d):
        value ^= x
        x = field.mul(x, x)
    assert value in (0, 1)
    return value


def syndrome(matrix, d, field):
    words = [(1 << a, 1 << b) for a in range(d) for b in range(d) if matrix >> (a*d+b) & 1]
    return [xor(field.mul(x, field_power(y, 1 << j, field)) for x, y in words)
            for j in range(d)]


def factor_syndrome(a, b, d, field):
    lhs = [sum((a >> (u*d+h) & 1) << u for u in range(d)) for h in range(d)]
    rhs = [(b >> (h*d)) & ((1 << d) - 1) for h in range(d)]
    values = []
    for _ in range(d):
        values.append(xor(field.mul(x, y) for x, y in zip(lhs, rhs)))
        rhs = [field.mul(y, y) for y in rhs]
    return values


def audit(d, modulus, generator):
    field = BinaryField(modulus, generator)
    size = 1 << (d*d)
    words = list(range(1 << d))
    dual = [next(x for x in words if all(trace(field.mul(x, 1 << i), d, field) == (i == j)
                                        for i in range(d))) for j in range(d)]
    kernels = [0] * (d+1)
    min_rank = [d+1] * d
    for e in range(size):
        coeff = syndrome(e, d, field)
        rowmask = (1 << d)-1
        rank = binary_rank([(e >> (i*d)) & rowmask for i in range(d)])
        for col, x in enumerate(dual):
            image = xor(field.mul(c, field_power(x, 1 << j, field)) for j, c in enumerate(coeff))
            assert image == sum((e >> (i*d+col) & 1) << i for i in range(d))
        for r in range(d+1):
            if not any(coeff[:r]):
                kernels[r] += 1
                if e:
                    assert rank > r
                    min_rank[r] = min(rank, min_rank[r])
    assert kernels == [1 << (d*(d-r)) for r in range(d+1)]
    assert min_rank == list(range(1, d+1))
    for a, b in product(range(size), repeat=2):
        assert factor_syndrome(a, b, d, field) == syndrome(product_bits(a, b, d), d, field)
    return kernels, size**2


if __name__ == '__main__':
    for settings in [(2, 0b111, 2), (3, 0b1011, 2)]:
        kernels, pairs = audit(*settings)
        print(f'd={settings[0]}: exact kernel sizes {kernels}, {pairs} ordered factor pairs')
