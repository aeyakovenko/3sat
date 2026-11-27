"""Check crossing endpoints and near-tight band mass using exact arithmetic."""

from fractions import Fraction
from itertools import combinations_with_replacement, product


def crossing(values, thresholds):
    return next(
        (i for i, (v, g) in enumerate(zip(values, thresholds)) if v >= g),
        len(values),
    )


def exhaust_crossings():
    checks = 0
    for n in range(1, 5):
        for truth in combinations_with_replacement(range(5), n):
            for g0 in range(8):
                for drop in (1, 2):
                    thresholds = [g0 - drop * i for i in range(n)]
                    reference = crossing(truth, thresholds)
                    observed = set()
                    for errors in product((-1, 0, 1), repeat=n):
                        empirical = [v + e for v, e in zip(truth, errors)]
                        index = crossing(empirical, thresholds)
                        assert abs(reference - index) <= 1
                        observed.add(index)
                        checks += 1
                    if drop == 2:
                        assert max(observed) - min(observed) <= 1
    return checks


def test_sharp_cases():
    # Error 2, drop 3. Two individually valid estimates cross two places apart.
    thresholds = (12, 9, 6)
    assert [crossing((v,) * 3, thresholds) for v in (12, 10, 8)] == [0, 1, 2]

    # With drop smaller than error, an estimate can miss by multiple places.
    thresholds = (7, 6, 5, 4)
    assert crossing((7,) * 4, thresholds) == 0
    assert crossing((4,) * 4, thresholds) == 3

    # Normalize p/128 to 1. Every increment is strictly less than 1.
    # The total entering the closed band [4,8] approaches 3 from above.
    for denominator in (16, 256, 4096):
        eps = Fraction(1, denominator)
        before = 4 - eps
        last = 7 + eps
        levels = [before * j / 5 for j in range(6)]
        levels.extend(before + (last - before) * j / 4 for j in range(1, 5))
        levels.append(8 + eps / 2)
        jumps = [(b, b - a) for a, b in zip(levels, levels[1:])]
        assert all(0 < jump < 1 for _, jump in jumps)
        mass = sum(jump for b, jump in jumps if 4 <= b <= 8)
        assert mass == 3 + 2 * eps


if __name__ == "__main__":
    count = exhaust_crossings()
    test_sharp_cases()
    print(f"{count} finite crossing checks passed; separation and band sharpness verified.")
