"""Exhaust small Vandermonde/inner-product tape generators and subcube covers."""

from collections import Counter
from fractions import Fraction
from itertools import combinations


MODULUS = {2: 0b111, 4: 0b10011, 8: 0b100011011}


def check_field(bits):
    polynomial = MODULUS[bits]
    assert polynomial.bit_length() == bits + 1
    for degree in range(1, bits // 2 + 1):
        for divisor in range(1 << degree, 2 << degree):
            remainder = polynomial
            while remainder.bit_length() > degree:
                remainder ^= divisor << (remainder.bit_length() - degree - 1)
            assert remainder != 0


def multiply(a, b, bits):
    value = 0
    while b:
        if b & 1:
            value ^= a
        b >>= 1
        a <<= 1
        if a >> bits:
            a ^= MODULUS[bits]
    return value


def column(position, k, h):
    """Concatenate the h binary coefficients of each of 1,i,...,i^(k-1)."""
    result = 0
    power = 1
    for j in range(k):
        result |= power << (j * h)
        power = multiply(power, position, h)
    return result


def evaluate(polynomial, x, bits):
    value = 0
    for j in reversed(range(polynomial.bit_length())):
        value = multiply(value, x, bits) ^ ((polynomial >> j) & 1)
    return value


def generate(columns, bits):
    field_size = 1 << bits
    table = [tuple(evaluate(c, x, bits) for c in columns) for x in range(field_size)]
    counts = Counter()
    for row in table:
        for y in range(field_size):
            tape = sum(((v & y).bit_count() % 2) << i for i, v in enumerate(row))
            counts[tape] += 1
    assert counts.total() == field_size**2
    return counts


def contained(tape, cube):
    mask, value = cube
    return tape & mask == value


def relative_lower(width, degree_bound, field_size):
    return max(Fraction(0), 1 - Fraction(((1 << width) - 1) * degree_bound, field_size))


def check_cubes(h, k, bits, positions):
    assert h.bit_count() == 1 and len(set(positions)) == len(positions)
    assert all(0 <= i < 1 << h for i in positions)
    field_size = 1 << bits
    degree_bound = h * k - 1
    columns = [column(i, k, h) for i in positions]
    counts = generate(columns, bits)
    smallest_ratio = Fraction(1)
    max_roots = parities = assignments = 0

    for width in range(1, k + 1):
        for indices in combinations(range(len(positions)), width):
            mask = sum(1 << i for i in indices)
            polynomial = 0
            for i in indices:
                polynomial ^= columns[i]
            assert polynomial != 0
            roots = sum(evaluate(polynomial, x, bits) == 0 for x in range(field_size))
            signed_sum = sum(n * (-1) ** ((t & mask).bit_count() % 2) for t, n in counts.items())
            assert signed_sum == field_size * roots
            assert roots <= polynomial.bit_length() - 1 <= degree_bound
            max_roots = max(max_roots, roots)
            parities += 1

            histogram = Counter()
            for tape, n in counts.items():
                histogram[tape & mask] += n
            lower = relative_lower(width, degree_bound, field_size)
            upper = 1 + Fraction(((1 << width) - 1) * degree_bound, field_size)
            for assignment in range(1 << width):
                value = sum(((assignment >> j) & 1) << i for j, i in enumerate(indices))
                ratio = Fraction(histogram[value] << width, counts.total())
                assert lower <= ratio <= upper
                smallest_ratio = min(smallest_ratio, ratio)
                assignments += 1

    print(f"h={h} k={k} l={bits}: {counts.total()} seeds, {parities} parities, "
          f"{assignments} assignments, max bias {Fraction(max_roots, field_size)}, "
          f"min seeded/fair {smallest_ratio} (bound {relative_lower(k, degree_bound, field_size)})")
    return counts


def check_cover(counts, h, k, bits, width):
    # Each tuple fixes nonadjacent tape bits. Two early leaves publish A,
    # a third publishes it late, and one publishes B. Some tapes never publish.
    leaves = [
        (1, "A", (0b0101, 0b0000)),
        (1, "A", (0b1001, 0b1001)),
        (2, "A", (0b1101, 0b1100)),
        (1, "B", (0b1001, 0b0001)),
    ]
    fair = Counter({tape: 1 for tape in range(1 << width)})
    for (mask, value), (other_mask, other_value) in combinations([cube for _, _, cube in leaves], 2):
        assert (value ^ other_value) & mask & other_mask
    for _, _, (mask, _) in leaves:
        assert mask.bit_count() <= k

    def mass(distribution, label, deadline):
        successes = 0
        for tape, n in distribution.items():
            if any(clock <= deadline and output == label and contained(tape, cube)
                   for clock, output, cube in leaves):
                successes += n
        return Fraction(successes, distribution.total())

    for deadline in (0, 1, 2):
        for label in ("A", "B"):
            lower = Fraction(0)
            fair_sum = Fraction(0)
            for clock, output, (mask, _) in leaves:
                if clock <= deadline and output == label:
                    w = mask.bit_count()
                    fair_sum += Fraction(1, 1 << w)
                    lower += relative_lower(w, h * k - 1, 1 << bits) / (1 << w)
            assert mass(fair, label, deadline) == fair_sum
            assert mass(counts, label, deadline) >= lower
    early, eventual = (mass(counts, "A", t) for t in (1, 2))
    other = mass(counts, "B", 2)
    assert early < eventual and eventual + other < 1
    assert mass(fair, "A", 1) == Fraction(1, 2) and mass(fair, "A", 2) == Fraction(5, 8)
    print(f"  disjoint cover: seeded A early {early}, eventual {eventual}; "
          f"B {other}, no publication {1-eventual-other}")


def main():
    for bits in MODULUS:
        check_field(bits)
    for h, k, bits, positions in [
        (2, 2, 4, (0, 1, 2, 3)),
        (2, 4, 8, (0, 1, 2, 3)),
        (4, 3, 8, (0, 1, 3, 6, 9, 10, 15)),
    ]:
        counts = check_cubes(h, k, bits, positions)
        if k >= 3:
            check_cover(counts, h, k, bits, len(positions))


if __name__ == "__main__":
    main()
