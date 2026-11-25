"""Verify public bit transposes and bit-sliced trace products using scalar field arithmetic."""

from random import Random


def transpose(rows):
    rows = rows.copy()
    side = len(rows)
    stride = 1
    while stride < side:
        low = sum(1 << j for j in range(side) if not j & stride)
        for i in range(side):
            if not i & stride:
                change = ((rows[i] >> stride) ^ rows[i + stride]) & low
                rows[i] ^= change << stride
                rows[i + stride] ^= change
        stride *= 2
    return rows


def word_polynomial_product(left, right):
    n = len(left)
    if n == 1:
        return [left[0] & right[0]]
    mid = n // 2
    a, b = left[:mid], left[mid:]
    c, d = right[:mid], right[mid:]
    low = word_polynomial_product(a, c)
    high = word_polynomial_product(b, d)
    mixed = word_polynomial_product([x ^ y for x, y in zip(a, b)],
                                    [x ^ y for x, y in zip(c, d)])
    result = [0] * (2 * n - 1)
    for i, (x, y, z) in enumerate(zip(low, mixed, high)):
        result[i] ^= x
        result[mid + i] ^= x ^ y ^ z
        result[n + i] ^= z
    return result


def field_multiply(a, b, modulus, h):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a >> h:
            a ^= modulus
        b >>= 1
    return result


def trace_word(x, mod, h):
    result = 0
    for _ in range(h):
        result ^= x
        x = field_multiply(x, x, mod, h)
    assert result in (0, 1)
    return result


def main():
    rng = Random(1041)
    checked = 0
    for h, mod in ((2, 7), (3, 11), (4, 19), (5, 37), (6, 67)):
        side = 1 << (h - 1).bit_length()
        weights = []
        power = 1
        for _ in range(3 * h - 2):
            weights.append(trace_word(power, mod, h))
            power = field_multiply(power, 2, mod, h)
        for _ in range(30):
            blocks = [[rng.randrange(1 << h) for _ in range(side)] for _ in range(3)]
            a, b, z = (transpose(rows) for rows in blocks)
            for rows, columns in zip(blocks, (a, b, z)):
                assert all(((columns[j] >> i) & 1) == ((rows[i] >> j) & 1)
                           for i in range(side) for j in range(side))
            ab = word_polynomial_product(a, b) + [0]
            abz = word_polynomial_product(ab, z + [0] * side)
            expected = [trace_word(field_multiply(field_multiply(x, y, mod, h), w, mod, h),
                                   mod, h) for x, y, w in zip(*blocks)]
            word = 0
            for coefficient, weight in zip(abz, weights):
                if weight:
                    word ^= coefficient
            assert [(word >> i) & 1 for i in range(side)] == expected
            checked += side
    print(f"{checked} public-address trace lanes and all transpose positions passed")


if __name__ == "__main__":
    main()
