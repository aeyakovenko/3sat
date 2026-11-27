"""Check the endpoint rounding in the rational-rate release construction."""

from fractions import Fraction
from math import ceil, floor, isqrt


def partition(order):
    return sorted({Fraction(num, den) for den in range(1, order + 1)
                   for num in range(3 * den, 4 * den + 1)})


def check_order(order, log_delay_error=6, early_power=2):
    m = 2**order
    radius = order**2
    root = isqrt(m - 1) + 1
    cuts = partition(order)
    guarded_count = 0
    for left, right in zip(cuts, cuts[1:]):
        assert right - left >= Fraction(1, order**2)
        lower, upper = floor(left * m), floor(right * m)
        middle = floor((left + right) * m / 2)
        shifted = floor(right * m) - root
        # Every possible publication exponent is in [E-log_delay_error,E].
        for exponent in (middle, shifted):
            assert lower < exponent - log_delay_error <= exponent <= upper
            assert exponent < upper - early_power * order
        # Check the extreme fine-cell exponents in this partition element.
        start = floor(left * m + radius) + 1
        last = ceil(right * m - radius) - 1
        if start <= last:
            assert lower < start - log_delay_error <= last <= upper
            guarded_count += last - start + 1
    skipped = m - guarded_count
    assert skipped <= len(cuts) * (2 * radius + 1)
    return len(cuts), skipped


if __name__ == '__main__':
    for order in (18, 20, 24, 32, 48, 64):
        cut_count, skipped = check_order(order)
        print(f'r={order}: {cut_count} rational boundaries, '
              f'{skipped}/{2**order} fine cells near a boundary')
