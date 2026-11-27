"""Exact upper certificate and finite obstruction for the mixed checkpoint rule."""

from fractions import Fraction as Q
from itertools import accumulate
from typing import NamedTuple


class Profile(NamedTuple):
    work: Q
    floor: Q


PUBLIC = Q(2, 3)  # p/A, for a packed linear-time SAT solver
ROUNDING = 10**20


def round_up(value):
    scaled = value * ROUNDING
    return Q(-(-scaled.numerator // scaled.denominator), ROUNDING)


def trade(c, levels, charge_endpoint=True):
    """List order is outside to inside. Floors are shifted down by p/A."""
    elapsed = Q(0)
    charges = []
    for work, floor in levels:
        assert work >= 0 and floor >= 0
        charges.append(elapsed + floor)
        elapsed += work
    floor = max(charges)
    balanced = (1 + sum(charges) - len(charges) * c + elapsed) / (len(charges) + 1)
    work = max(balanced, floor - c)
    if charge_endpoint:
        work = max(work, elapsed - PUBLIC - c)
    splits = [work + c - charge for charge in charges]
    assert min(splits) >= 0
    assert 1 - sum(splits) + elapsed <= work
    assert all(split - c + charge <= work for split, charge in zip(splits, charges))
    return Profile(work, floor)


def upper_certificate():
    c = Q("0.71828175")
    stages = []
    first = Profile(Q(1), Q(0))
    suffixes = [(), (0,), (1, 0), (2, 1, 0), (3, 2, 1, 0),
                (4, 3, 2, 1, 0), (5, 4, 3, 1, 0), (6, 5, 4, 3, 1, 0)]
    for stage, indices in enumerate(suffixes):
        suffix = [stages[i] for i in indices]
        previous = stages[-1] if stages else first
        start = trade(c, [previous, *suffix])
        current = Profile(previous.work, start.floor)
        for iteration in range(300):
            if stage or iteration:
                assert all(e <= PUBLIC + f for e, f in [current, *suffix])
            result = trade(c, [current, *suffix])
            assert result.floor == current.floor
            current = Profile(round_up(result.work), result.floor)
        stages.append(current)
        print(f"stage {stage}: work {float(current.work):.9f}, "
              f"shifted floor {float(current.floor):.9f}")
    final = trade(c, [stages[-1]] * 11)
    assert final.work < -Q(1, 200)
    print(f"final exact normalized work {final.work} < -1/200")


def lower_certificate():
    c = Q(2873, 4000)
    times = [Q(1127, 4000), Q(127, 1000), Q(143, 2000),
             Q(6, 125), Q(121, 3000)]
    floors = list(accumulate(times, initial=Q(0)))[:-1]
    envelope = list(map(Profile, times, floors))
    assert all(earlier.work > later.work and earlier.floor < later.floor
               for earlier, later in zip(envelope, envelope[1:]))
    assert envelope[0].work <= 1 and envelope[0].floor == 0

    def visit(levels, largest_index, elapsed):
        checked = 0
        if levels:
            # An optimistic rule ignoring a potentially larger endpoint charge.
            result = trade(c, levels, charge_endpoint=False)
            assert any(e <= result.work and f <= result.floor for e, f in envelope), (
                levels, result)
            checked = 1
        for i in range(largest_index, -1, -1):
            row = envelope[i]
            if elapsed + row.floor < c:
                checked += visit([*levels, row], i, elapsed + row.work)
        return checked

    checked = visit([], len(envelope) - 1, Q(0))
    assert checked == 718
    print(f"exact obstruction: {checked} admissible sorted tuples at c={c}")


if __name__ == "__main__":
    upper_certificate()
    lower_certificate()
