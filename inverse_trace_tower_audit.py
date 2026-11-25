"""Exhaust all inputs through degree 16 and check the tower's leaf-size law."""

from collections import Counter
from fractions import Fraction


def audit(degree, polynomial):
    size = 1 << degree
    order = size - 1
    powers = []
    logs = [-1] * size
    value = 1
    for exponent in range(order):
        assert logs[value] == -1
        logs[value] = exponent
        powers.append(value)
        value <<= 1
        if value & size:
            value ^= polynomial
    assert value == 1

    positive_leaves = Counter()
    zero_leaves = Counter()
    for original in range(size):
        # Compute the input's sign independently in the original field.
        reciprocal = powers[-logs[original] % order] if original else 0
        absolute_trace = 0
        for _ in range(degree):
            absolute_trace ^= reciprocal
            if reciprocal:
                reciprocal = powers[2 * logs[reciprocal] % order]
        assert absolute_trace in (0, 1)

        current = original
        dimension = degree
        transcript = []
        while dimension > 1:
            dimension //= 2
            subfield_size = 1 << dimension
            conjugate = powers[subfield_size * logs[current] % order] if current else 0
            quotient = current ^ conjugate
            transcript.append(quotient)
            if not quotient:
                current = 0
                break
            current = powers[(logs[current] + logs[conjugate] - logs[quotient]) % order]
        assert current == absolute_trace
        if current:
            positive_leaves[tuple(transcript)] += 1
        else:
            zero_leaves[tuple(transcript)] += 1

    observed = Counter()
    for multiplicity in positive_leaves.values():
        dimension = multiplicity.bit_length() - 1
        assert multiplicity == 1 << dimension
        observed[dimension] += multiplicity

    predicted = Counter({0: 1})
    lower_degree = 1
    while lower_degree < degree:
        lower_size = 1 << lower_degree
        following = Counter()
        for dimension, count in predicted.items():
            growing = lower_size >> dimension
            following[dimension + 1] += count * growing
            if growing < lower_size:
                following[dimension] += count * (lower_size - growing)
        predicted = following
        lower_degree *= 2
    assert observed == predicted
    assert sum(observed.values()) == size // 2
    zero_observed = Counter()
    for count in zero_leaves.values():
        saved = count.bit_length() - 1
        assert count == 1 << saved
        zero_observed[saved] += count
    zero_predicted = Counter()
    remaining = degree // 2
    stage = 0
    while remaining:
        mass = size >> remaining
        if stage:
            mass -= size >> (2 * remaining)
        by_rank = Counter({remaining: Fraction(mass)})
        for _ in range(max(0, stage - 1)):
            following = Counter()
            for saved, count in by_rank.items():
                growing = count / (1 << saved)
                following[saved + 1] += growing
                following[saved] += count - growing
            by_rank = following
        zero_predicted.update(by_rank)
        remaining //= 2
        stage += 1
    assert zero_observed == zero_predicted
    print(f"degree {degree}, trace-one inputs by saved rank: {dict(sorted(observed.items()))}")


if __name__ == "__main__":
    for field_degree, modulus in [(2, 0x7), (4, 0x13), (8, 0x11D), (16, 0x1100B)]:
        audit(field_degree, modulus)
