"""Finite checks of padding, allocation and the joint Kraft charge over savings."""
from fractions import Fraction
from itertools import product


def padded_length(size, gap, supplied):
    if size - gap <= supplied <= size - 2:
        return size - 1
    return supplied


def check_program_lengths():
    checked = 0
    for size, gap, supplied in product(range(1, 16), range(1, 18), range(20)):
        actual = padded_length(size, gap, supplied)
        assert (actual < size) == (supplied < size)
        assert actual >= supplied
        assert not size - gap <= actual <= size - 2
        for fallback in [None, *range(1, size + 2)]:
            lengths = [size, actual]
            if fallback is not None:
                lengths.append(fallback)
            shortest = min(lengths)
            has_short_fallback = fallback is not None and fallback < size
            if shortest < size and not has_short_fallback:
                assert shortest == size - 1 or shortest <= size - gap - 1
        checked += 1
    return checked


def check_dyadic_charges():
    checked = 0
    for size in range(1, 17):
        word = Fraction(1, 1 << size)
        for shortest in range(size + 2):
            for h in range(1, 11):
                paid = sum((1 << gap) * word for gap in range(1, size + 1)
                           if shortest <= size - gap - h)
                assert paid <= Fraction(2, (1 << h) * (1 << shortest))
                checked += 1
    return checked


def check_increment():
    checked = 0
    for size in range(1, 13):
        for late in range(1, size + 4):
            for early in range(late, size + 5):
                charges = [Fraction(2) ** (gap - size)
                           for gap in range(size - early, size - late)]
                assert sum(charges) == Fraction(1, 1 << late) - Fraction(1, 1 << early)
                checked += 1
    return checked


def check_literal_prefixes():
    checked = 0
    for counts in product(range(4), repeat=4):
        capacities = tuple(1 << j for j in range(3, 7))
        total = sum(Fraction(c, denominator) for c, denominator in zip(counts, capacities))
        if total > Fraction(1, 2):
            continue
        prefixes = []
        endpoint = Fraction()
        for j, number in zip(range(3, 7), counts):
            first = endpoint * (1 << j)
            assert first.denominator == 1
            for k in range(number):
                cell = format(int(first) + k, f'0{j}b')
                assert cell.startswith('0')
                assert all(not cell.startswith(p) for p in prefixes)
                prefixes.append(cell)
            endpoint += Fraction(number, 1 << j)
        assert endpoint == total
        checked += 1
    return checked


if __name__ == '__main__':
    print(f'{check_program_lengths()} padding cases, {check_dyadic_charges()} '
          f'word charges, {check_literal_prefixes()} literal-prefix schedules, '
          f'{check_increment()} clock increments')
