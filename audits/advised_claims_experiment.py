"""Exhaust the powering construction on GF(4) with up to three impulses."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product


def multiply(left, right):
    """Multiply modulo X² + X + 1."""
    result = 0
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
        if left & 4:
            left ^= 7
    return result


def output_word(abscissa, ordinate):
    power, word = 1, 0
    for degree in range(3):
        for bit in range(2):
            coordinate = multiply(ordinate, multiply(power, 1 << bit)) & 1
            word |= coordinate << (2 * degree + bit)
        power = multiply(power, abscissa)
    return word


def parity(word, mask):
    return (word & mask).bit_count() % 2


def xor_all(words):
    result = 0
    for word in words:
        result ^= word
    return result


def is_root(mask, abscissa):
    value = 0
    for degree in reversed(range(3)):
        value = multiply(value, abscissa) ^ ((mask >> (2 * degree)) & 3)
    return value == 0


def check():
    points = [output_word(u, v) for u in range(4) for v in range(4)]
    single = [sum(1 - 2 * parity(w, mask) for w in points) for mask in range(64)]
    assert max(abs(value) for value in single[1:]) == 8
    for mask in range(1, 64):
        assert single[mask] == 4 * sum(is_root(mask, u) for u in range(4))

    for count in (2, 3):
        histogram = Counter(xor_all(t) for t in product(points, repeat=count))
        total = len(points) ** count
        coefficients = [sum(freq * (1 - 2 * parity(word, a)) for word, freq in histogram.items())
                        for a in range(64)]
        assert coefficients == [value ** count for value in single]
        upper = Fraction(1, 4) + Fraction(3, 4) * Fraction(1, 2) ** count
        largest = Fraction(0)
        for a, b in combinations(range(1, 64), 2):
            cells = Counter()
            for word, freq in histogram.items():
                cells[parity(word, a), parity(word, b)] += freq
            largest = max(largest, Fraction(max(cells.values()), total))
        assert largest == upper
        print(f"{count} impulses: all {total} outcomes gave maximum two-label mass {largest}")


if __name__ == "__main__":
    check()
