"""Check exact dyadic thresholds and consistency of replies on private histories."""

from fractions import Fraction
from itertools import product


def above_third(depths):
    if not depths:
        return False
    units = [0] * (max(depths) + 1)
    for depth in depths:
        units[depth] += 3
    remainder = False
    for depth in range(len(units) - 1, 0, -1):
        carry, digit = divmod(units[depth], 2)
        units[depth - 1] += carry
        remainder |= bool(digit)
    return units[0] > 1 or (units[0] == 1 and remainder)


def accepting_depth_lists(height):
    if height == 0:
        return [(), (0,)]
    children = accepting_depth_lists(height - 1)
    return [(0,)] + [
        tuple(1 + depth for depth in left + right)
        for left in children
        for right in children
    ]


def count_accepts(labels, first, last):
    accepted = 0
    for coin_a, coin_b, hidden in product(range(2), repeat=3):
        public = coin_a ^ coin_b
        reply = first[public]
        next_public = coin_b ^ reply
        answer = last[2 * public + next_public]
        index = 4 * coin_a + 2 * coin_b + hidden
        accepted += answer == labels[index]
    return accepted


def check_private_histories():
    different = 0
    for labels in product(range(2), repeat=8):
        # Replies to a private final bit may not depend on that bit.
        expected = sum(
            2 if labels[index] == labels[index + 1] else 1
            for index in range(0, 8, 2)
        )
        actual = max(
            count_accepts(labels, first, last)
            for first in product(range(2), repeat=2)
            for last in product(range(2), repeat=4)
        )
        assert actual == expected
        different += actual < 8
    return different


if __name__ == "__main__":
    trees = accepting_depth_lists(3)
    # Very deep leaves can put a dyadic sum arbitrarily close to one third.
    below = tuple(range(2, 1201, 2))
    trees.extend([below, below + (1200,), (10000,), (1, 10000)])
    for depths in trees:
        exact = sum((Fraction(1, 2**depth) for depth in depths), Fraction(0))
        assert above_third(depths) == (3 * exact > 1)
    different = check_private_histories()
    print(f"{len(trees)} dyadic mass checks and 256 two-turn games passed. "
          f"Allowing replies to depend on the hidden bit changes {different} games.")
