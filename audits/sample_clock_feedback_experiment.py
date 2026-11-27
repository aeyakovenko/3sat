"""Exact finite laws for a capped current-clock sampler at three consecutive stages."""

from fractions import Fraction
from itertools import product

Z = Fraction(0)
ONE = Fraction(1)
ALPHABET = (0, 1, 2)
TIMEOUT = 2


def tv(left, right):
    return sum(abs(x - y) for x, y in zip(left, right)) / 2


def evaluate(old, first, second, variant):
    """An answer can depend on each sample and on the stage's transition table."""
    if variant == 0:
        return old if first == TIMEOUT else (first + second) % 3
    if variant == 1:
        return int(first == second) if old == TIMEOUT else (1 + old + first) % 3
    return (first * (old + 1) + second + (old == TIMEOUT)) % 3


def transform(current_law, previous_law, variant):
    out = [Z] * 3
    for h, x, y in product(ALPHABET, repeat=3):
        out[evaluate(h, x, y, variant)] += previous_law[h] * current_law[x] * current_law[y]
    return out


def capped_stage(background, launch, previous_law, cap, variant):
    # A coefficient at n records exactly n same-stage F vertices. The law in
    # degree zero is the subprobability from draws that bypass the active branch.
    child = [background]
    completed = [Z] * 3
    for size in range(1, cap + 1):
        layer = [Z] * 3
        for left_size in range(size):
            left, right = child[left_size], child[size - 1 - left_size]
            for h, x, y in product(ALPHABET, repeat=3):
                layer[evaluate(h, x, y, variant)] += previous_law[h] * left[x] * right[y]
        completed = [a + b for a, b in zip(completed, layer)]
        child.append([launch * p for p in layer])

    truncated = ONE - sum(completed)
    completed[TIMEOUT] += truncated
    mu = [a + launch * q for a, q in zip(background, completed)]
    assert sum(mu) == 1 and min(mu) >= 0
    actual_transform = transform(mu, previous_law, variant)
    assert tv(completed, actual_transform) <= (1 + 2 * launch) * truncated
    for y in ALPHABET[:-1]:
        assert mu[y] + launch * (1 + 2 * launch) * truncated >= launch * actual_transform[y]
    return mu, completed, truncated


def run_checks():
    cases = 0
    strict = 0
    for cap in range(1, 9):
        for variant in ALPHABET:
            for launch in (Fraction(1, 32), Fraction(1, 16), Fraction(1, 8)):
                previous = [Z, Z, ONE]
                issued = [Z, Z]
                for stage in range(3):
                    zero = Fraction(3 + stage, 32) + issued[0]
                    one = Fraction(2 + 2 * stage, 32) + issued[1]
                    background = [zero, one, ONE - zero - one - launch]
                    mu, q, truncated = capped_stage(
                        background, launch, previous, cap, (variant + stage) % 3
                    )
                    strict += tv(q, transform(mu, previous, (variant + stage) % 3)) > 0
                    assert 0 < truncated < 1
                    for y in (0, 1):
                        issued[y] += launch * q[y]
                        assert mu[y] >= previous[y] + launch * q[y]
                    previous = mu
                    cases += 1
    print(f"{cases} exact stage laws passed; {strict} had nonzero truncation discrepancy.")


if __name__ == "__main__":
    run_checks()
