"""Compare exact Walsh histograms of quadratic Boolean maps to direct enumeration."""

from collections import Counter
from random import Random


def toggle(polynomial, monomial):
    if monomial in polynomial:
        polynomial.remove(monomial)
    else:
        polynomial.add(monomial)


def quadratic_gap(polynomial, variables):
    """Return the sum of (-1)^f over all assignments of the free variables."""
    residual = set(polynomial)
    factor = 1
    while True:
        pair = next((m for m in residual if m.bit_count() == 2), None)
        if pair is None:
            if any(residual - {0}):
                return 0
            return (-factor if 0 in residual else factor) << variables
        left = pair & -pair
        right = pair ^ left
        residual.remove(pair)
        left_terms = [m ^ left for m in residual if m & left]
        right_terms = [m ^ right for m in residual if m & right]
        residual = {m for m in residual if not m & pair}
        for a in left_terms:
            for b in right_terms:
                toggle(residual, a | b)
        variables -= 2
        factor *= 2


def histogram(coordinates, variables):
    values = []
    for mask in range(1 << len(coordinates)):
        phase = set()
        for i, coordinate in enumerate(coordinates):
            if mask & (1 << i):
                phase ^= coordinate
        values.append(quadratic_gap(phase, variables))
    stride = 1
    while stride < len(values):
        for start in range(0, len(values), 2 * stride):
            for j in range(start, start + stride):
                a, b = values[j], values[j + stride]
                values[j], values[j + stride] = a + b, a - b
        stride *= 2
    assert all(v >= 0 and v % len(values) == 0 for v in values)
    return [v // len(values) for v in values]


def direct_counts(coordinates, variables):
    counts = Counter()
    for x in range(1 << variables):
        bits = [sum(x & m == m for m in coordinate) % 2 for coordinate in coordinates]
        counts[sum(b << i for i, b in enumerate(bits))] += 1
    return [counts[y] for y in range(1 << len(coordinates))]


def main():
    rng = Random(249)
    cases = 0
    for variables in range(9):
        terms = [m for m in range(1 << variables) if m.bit_count() <= 2]
        for width in range(6):
            for _ in range(8):
                coords = [{m for m in terms if rng.getrandbits(1)} for _ in range(width)]
                assert histogram(coords, variables) == direct_counts(coords, variables)
                cases += 1
    print(f"{cases} exact histograms agreed with exhaustive enumeration.")


if __name__ == "__main__":
    main()
