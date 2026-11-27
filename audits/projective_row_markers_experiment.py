"""Finite checks for Frobenius normalization of the projective row markers."""

from itertools import product
from random import Random


class BinaryField:
    """Use the first primitive monic polynomial, in polynomial-basis order."""

    def __init__(self, bits):
        self.bits = bits
        self.size = 1 << bits
        self.order = self.size - 1
        for modulus in range(self.size + 1, 2 * self.size, 2):
            powers = []
            value = 1
            while True:
                powers.append(value)
                value <<= 1
                if value & self.size:
                    value ^= modulus
                if value == 1:
                    break
            if len(powers) == self.order:
                break
        self.exp = powers
        self.log = [0] * self.size
        for exponent, value in enumerate(powers):
            self.log[value] = exponent

    def multiply(self, a, b):
        return self.exp[(self.log[a] + self.log[b]) % self.order] if a and b else 0

    def power(self, x, exponent):
        if exponent == 0:
            return 1
        return self.exp[(self.log[x] * exponent) % self.order] if x else 0

    def frobenius(self, x, steps):
        return self.power(x, 1 << (steps % self.bits))

    def divide(self, a, b):
        assert b
        return self.exp[(self.log[a] - self.log[b]) % self.order] if a else 0


def affine_powers(field, a, b, degree):
    """Coefficient lists for (aW+b)^e, by repeated ordinary multiplication."""
    powers = [[1]]
    for _ in range(degree):
        prev = powers[-1]
        coeffs = [0] * (len(prev) + 1)
        for j, value in enumerate(prev):
            coeffs[j] ^= field.multiply(value, b)
            coeffs[j + 1] ^= field.multiply(value, a)
        powers.append(coeffs)
    return powers


def reduce_scaled_power(field, coeffs, weight, degree):
    """Reduce modulo u²+u and constants, taking roots in the finite field."""
    result = [0] * (degree + 1)
    for j, value in enumerate(coeffs):
        result[j] = field.multiply(weight, value)
    for j in range(degree - degree % 2, 0, -2):
        result[j // 2] ^= field.frobenius(result[j], -1)
        result[j] = 0
    # A field element uses at most one byte in the exhaustive small-field tests.
    return int.from_bytes(bytes(result[1:]), 'little')


def formal_audit(bits, degree, payload_length):
    field = BinaryField(bits)
    assert 17 <= degree and degree % 8 == 1 and 2 * payload_length + 9 <= degree
    marker = 2
    assert len({field.frobenius(marker, h) for h in range(bits)}) == bits
    payloads = tuple(product(range(field.size), repeat=payload_length))
    markers_seen = set()
    rows_tested = 0
    for a in range(1, field.size):
        for b in range(field.size):
            powers = affine_powers(field, a, b, degree)
            indices = [degree, degree - 2, degree - 6]
            indices.extend(2 * j + 1 for j in range(payload_length))
            reduced = {
                e: [reduce_scaled_power(field, powers[e], value, degree)
                    for value in range(field.size)]
                for e in indices
            }
            for weight in range(1, field.size):
                base = reduced[degree][weight] ^ reduced[degree - 2][weight]
                packed = base.to_bytes(degree, 'little')
                triple = tuple(packed[e - 1] for e in (degree, degree - 2, degree - 4))
                expected = (
                    field.multiply(weight, field.power(a, degree)),
                    field.multiply(weight, field.power(a, degree - 2)),
                    field.multiply(field.multiply(weight, field.power(a, degree - 4)),
                                   field.power(b, 2)),
                )
                assert triple == expected and triple not in markers_seen
                markers_seen.add(triple)
                # Triples already separate different choices of (a,b,weight).
                row_signatures = set()
                for h in range(bits):
                    twist = lambda x: field.multiply(weight, field.frobenius(x, -h))
                    high = base ^ reduced[degree - 6][twist(marker)]
                    for payload in payloads:
                        signature = high
                        for j, value in enumerate(payload):
                            signature ^= reduced[2 * j + 1][twist(value)]
                        assert signature not in row_signatures
                        row_signatures.add(signature)
                        rows_tested += 1
    assert len(markers_seen) == (field.size - 1)**2 * field.size
    return rows_tested


def pgl(field, matrix, z):
    a, b, c, d = matrix
    denominator = field.multiply(c, z) ^ d
    if not denominator:
        # Deleting infinity from this permutation cycle sends its predecessor
        # to the original image of infinity.
        return field.divide(a, c)
    return field.divide(field.multiply(a, z) ^ b, denominator)


def row_value(field, degree, marker, payload, x):
    value = field.power(x, degree) ^ field.power(x, degree - 2)
    value ^= field.multiply(marker, field.power(x, degree - 6))
    for j, coefficient in enumerate(payload):
        value ^= field.multiply(coefficient, field.power(x, 2 * j + 1))
    return value


def random_pgl(field, rng):
    while True:
        matrix = tuple(rng.randrange(field.size) for _ in range(4))
        a, b, c, d = matrix
        if field.multiply(a, d) != field.multiply(b, c):
            return matrix


def projective_audit(bits=16, trials=8):
    field = BinaryField(bits)
    rng = Random(7821)
    worst = 0
    for trial in range(trials):
        first = random_pgl(field, rng)
        # In half the trials the two normalized poles coincide. Frobenius
        # exponents can still differ. Left affine changes fix infinity.
        h, k = rng.randrange(bits), rng.randrange(bits)
        if trial % 2:
            a, b, c, d = (field.frobenius(x, k-h) for x in first)
            u, v = rng.randrange(1, field.size), rng.randrange(field.size)
            second = (field.multiply(u,a) ^ field.multiply(v,c),
                      field.multiply(u,b) ^ field.multiply(v,d), c, d)
        else:
            second = random_pgl(field, rng)
        payload = tuple(rng.randrange(field.size) for _ in range(2))
        other = (payload[0] ^ 1, payload[1])
        maps = [(first, h, payload), (second, k, other)]
        normalized = [
            (tuple(field.frobenius(x, -s) for x in mat),
             field.frobenius(2, -s), tuple(field.frobenius(x, -s) for x in p))
            for mat, s, p in maps
        ]
        weights = [rng.randrange(1, field.size) for _ in maps]
        bins = [0] * 4
        for z in range(field.size):
            selected = 0
            for j, (mat, s, p) in enumerate(maps):
                value = row_value(field, 17, 2, p, pgl(field, mat, field.frobenius(z, s)))
                norm_mat, norm_marker, norm_payload = normalized[j]
                norm_value = row_value(field, 17, norm_marker, norm_payload,
                                       pgl(field, norm_mat, z))
                assert field.frobenius(field.multiply(weights[j], value), -s) == (
                    field.multiply(field.frobenius(weights[j], -s), norm_value))
                selected = 2 * selected + (value >> (bits - 1))
            bins[selected] += 1
        worst = max(worst, *(abs(count - field.size // 4) for count in bins))
    return worst


if __name__ == '__main__':
    cases = [(3, 17, 2), (3, 25, 2), (4, 17, 1), (4, 33, 1)]
    for args in cases:
        print(f'b={args[0]} m={args[1]} s={args[2]} verified {formal_audit(*args)} signatures')
    print(f'b=16 eight projective pairs, largest joint-cell count error: {projective_audit()}')
