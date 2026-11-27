"""Exhaust small residual syndromes and compare factor evaluation with direct AB."""

from itertools import product


class BinaryField:
    def __init__(self, modulus, generator):
        self.modulus = modulus
        size = 1 << (modulus.bit_length() - 1)
        self.powers = [1]
        for _ in range(size - 2):
            self.powers.append(self.mul(self.powers[-1], generator))
        assert len(set(self.powers)) == size - 1
        assert self.mul(self.powers[-1], generator) == 1

    def mul(self, x, y):
        value = 0
        while y:
            if y & 1:
                value ^= x
            y >>= 1
            x <<= 1
            if x.bit_length() == self.modulus.bit_length():
                x ^= self.modulus
        return value

    def power(self, exponent):
        return self.powers[exponent % len(self.powers)]


def xor(values):
    value = 0
    for x in values:
        value ^= x
    return value


def binary_rank(rows):
    basis = {}
    for row in rows:
        while row:
            bit = row.bit_length() - 1
            if bit not in basis:
                basis[bit] = row
                break
            row ^= basis[bit]
    return len(basis)


def dot(left, right, field):
    return xor(field.mul(x, y) for x, y in zip(left, right))


def unit_syndromes(d, field):
    # A packed integer contains all (2d-1)*d extension-field values,
    # with the slope index outermost, so masking selects the first r slopes.
    width = field.modulus.bit_length() - 1
    return [sum(field.power(i * u + (i + t) * v) << (width * (i + (2*d-1)*t))
                for t in range(d) for i in range(2*d-1))
            for u in range(d) for v in range(d)]


def matrix_syndrome(matrix, units):
    return xor(word for pos, word in enumerate(units) if matrix >> pos & 1)


def rank_census(d, field):
    units = unit_syndromes(d, field)
    width = field.modulus.bit_length() - 1
    row_mask = (1 << d) - 1
    invisible = [0] * d
    sharp_leading_diagonals = 0
    for error in range(1, 1 << (d*d)):
        rank = binary_rank([(error >> (d * row)) & row_mask for row in range(d)])
        diagonals = [sum((error >> (u*d + k-u)) & 1
                         for u in range(max(0, k-d+1), min(k+1, d)))
                     for k in range(2*d-1)]
        leading = next(count for count in diagonals if count)
        assert leading <= rank
        sharp_leading_diagonals += leading == rank
        syndrome = matrix_syndrome(error, units)
        for r in range(1, d+1):
            if syndrome & ((1 << (width*(2*d-1)*r))-1) == 0:
                assert rank > r
                invisible[r-1] += 1
    return invisible, sharp_leading_diagonals


def product_bits(a, b, d):
    return sum((sum((a >> (u*d+h) & 1) * (b >> (h*d+v) & 1)
                    for h in range(d)) % 2) << (u*d+v)
               for u in range(d) for v in range(d))


def check_factorization(d, field):
    size = 1 << (d*d)
    units = unit_syndromes(d, field)
    width = field.modulus.bit_length() - 1
    for a, b in product(range(size), repeat=2):
        ab = product_bits(a, b, d)
        actual = 0
        for t in range(d):
            for i in range(2*d-1):
                left = [xor(field.power(u*i) for u in range(d) if a >> (u*d+h) & 1)
                        for h in range(d)]
                right = [xor(field.power(v*(i+t)) for v in range(d) if b >> (h*d+v) & 1)
                         for h in range(d)]
                actual |= dot(left, right, field) << (width * (i+(2*d-1)*t))
        assert actual == matrix_syndrome(ab, units)
        for c in range(size):
            assert actual ^ matrix_syndrome(c, units) == matrix_syndrome(ab ^ c, units)
    return size**3


def check_tiles():
    checks = 0
    for d in range(2, 101):
        for r in range(2, d+1):
            b = r//2
            rows_used, columns_used = set(), set()
            for start in range(0, d-2*b+1, 2*b):
                rows = set(range(start, start+b))
                columns = set(range(start+b, start+2*b))
                assert rows_used.isdisjoint(rows) and columns_used.isdisjoint(columns)
                assert all(0 <= j-i < r for i in rows for j in columns)
                rows_used.update(rows)
                columns_used.update(columns)
            assert len(rows_used) == b * (d // (2*b))
            checks += 1
    return checks


if __name__ == '__main__':
    field = BinaryField(0b10011, 2)
    for d in (2, 3, 4):
        invisible, sharp = rank_census(d, field)
        print(f'd={d}: {2**(d*d)-1} nonzero matrices; undetected by slope count {invisible}; '
              f'leading antidiagonal attained rank on {sharp}')
    print(f'{check_factorization(2, field)} factored triples at d=2; {check_tiles()} tile layouts')
