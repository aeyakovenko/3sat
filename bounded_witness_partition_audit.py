"""Check the exact one-sided unambiguous OR query cost on a Hamming ball.

The oracle's marked set W is a subset of {0,...,M-1}, promised to have
at most K elements. A certificate queries every selected positive index
and every prescribed negative index. Only the accepting side is partitioned.
"""

from fractions import Fraction
from math import comb, prod


def predicted_cost(size, limit):
    if limit == 1:
        return 1
    even_limit = limit - limit % 2
    return max(limit, (size + even_limit) // 2)


def certificate(size, limit, positive):
    selected = [i for i in range(size) if positive & (1 << i)]
    if len(selected) > limit or len(selected) % 2 == 0:
        return None
    if any(i % 2 == j % 2 for i, j in zip(selected, selected[1:])):
        return None
    if len(selected) == limit:
        return positive, 0
    expected = selected[0] % 2
    negative = 0
    for i in range(size):
        if positive & (1 << i):
            expected ^= 1
        elif i % 2 == expected:
            negative |= 1 << i
    return positive, negative


def greedy_witness(marked, size):
    """Split sorted marks into maximal constant-parity runs."""
    first_in_block = []
    previous = None
    for i in range(size):
        if marked & (1 << i):
            if i % 2 != previous:
                first_in_block.append(i)
            previous = i % 2
    if len(first_in_block) % 2 == 0:
        first_in_block = first_in_block[1:]
    return sum(1 << i for i in first_in_block)


def check_partition(size, limit):
    certificates = []
    for positive in range(1, 1 << size):
        entry = certificate(size, limit, positive)
        if entry is not None:
            certificates.append(entry)
    observed_cost = max((pos | neg).bit_count() for pos, neg in certificates)
    assert observed_cost == predicted_cost(size, limit)
    checked = 0
    for marked in range(1 << size):
        if marked.bit_count() > limit:
            continue
        accepted = [
            pos for pos, neg in certificates
            if marked & pos == pos and marked & neg == 0
        ]
        expected = [greedy_witness(marked, size)] if marked else []
        assert accepted == expected, (size, limit, marked, accepted, expected)
        checked += 1
    return checked


def check_lower_bound(size, limit):
    # Width below K is excluded by the degree of OR on a K-dimensional cube.
    for width in range(limit, size + 1):
        total_samples = comb(size, width)
        coefficients = []
        for marks in range(limit + 1):
            # J counts marked indices in a uniform sample of exactly 'width'.
            # Solve the triangular system E[c_J | marks]=1[marks>0].
            counts = [
                comb(marks, j) * comb(size - marks, width - j)
                for j in range(marks + 1)
            ]
            residual = (total_samples if marks else 0) - sum(
                count * coefficient for count, coefficient in zip(counts, coefficients)
            )
            c = Fraction(residual, counts[-1])
            coefficients.append(c)
            rising = prod(size - width + j for j in range(marks))
            falling = prod(width - j for j in range(marks))
            assert c == 1 - (-1) ** marks * Fraction(rising, falling)
        assert all(c >= 0 for c in coefficients) == (width >= predicted_cost(size, limit))


def main():
    instances = 0
    promises = 0
    for size in range(1, 12):
        for limit in range(1, size + 1):
            promises += 1
            instances += check_partition(size, limit)
            check_lower_bound(size, limit)
    print(f"Checked all {promises} choices of 1 <= K <= M <= 11 and {instances:,} promised oracles.")
    print("The unique accepting certificate agrees with the greedy witness on every nonempty oracle.")
    print("Every maximum query count matches the exact nonnegative-coefficient threshold.")


if __name__ == "__main__":
    main()
