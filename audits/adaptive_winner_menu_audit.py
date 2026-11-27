"""Check adaptive naming risk, tolerant-name schedules, and the clean-pool recurrence."""

from fractions import Fraction
from functools import cache
from itertools import combinations, permutations
from math import comb


def check_planted_rows():
    cases = traces = 0
    for names in (2, 3):
        for width in range(1, 6):
            cells = tuple((name, pos) for name in range(names) for pos in range(width))
            for budget in range(min(4, width) + 1):
                for count in range(1, width + 1):
                    tables = [
                        (name, frozenset((name, pos) for pos in marks))
                        for name in range(names) for marks in combinations(range(width), count)
                    ]
                    best = len(tables)
                    for probes in combinations(cells, budget):
                        for name in range(names):
                            traces += 1
                            missed = sum(row == name and marks.isdisjoint(probes)
                                         for row, marks in tables)
                            best = min(best, missed)
                    assert Fraction(best, len(tables)) == Fraction(
                        comb(width - budget, count), names * comb(width, count)
                    )
                    cases += 1
    return cases, traces


def check_tolerant_rule():
    cases = 0
    for size in range(1, 7):
        threshold = (size + 1) // 2
        for mask in range(1 << size):
            for winners in permutations(range(size)):
                pool = {r for r in range(size) if mask & (1 << r)}
                previous_second = None
                errors = []
                portfolio_errors = [[], []]
                for date, winner in enumerate(winners):
                    second = min(pool, default=None)
                    if size - date >= threshold and len(pool) >= 3:
                        firsts = sorted(pool - {second, previous_second})
                        actual = winners[date:date + 2]
                        if actual == (firsts[0], second):
                            errors.append(date)
                        if len(pool) >= 4:
                            for expert, first in enumerate(firsts[:2]):
                                if actual == (first, second):
                                    portfolio_errors[expert].append(date)
                    previous_second = second
                    pool.discard(winner)
                assert all(b >= a + 2 for a, b in zip(errors, errors[1:]))
                cap = (size - threshold) // 2 + 1
                assert len(errors) <= cap
                joint = sorted(portfolio_errors[0] + portfolio_errors[1])
                assert all(b >= a + 2 for a, b in zip(joint, joint[1:]))
                assert len(joint) <= cap and min(map(len, portfolio_errors)) <= cap // 2
                cases += 1
    return cases


@cache
def phase_outcomes(pool, outsiders):
    """Track remaining pool and counts of both-wins, lost-responses, and direct preemptions."""
    outcomes = {(pool, 0, 0, 0)}
    if outsiders:
        outcomes.update((left, both, lost, direct + 1)
                        for left, both, lost, direct in phase_outcomes(pool, outsiders - 1))
    if pool >= 2:
        outcomes.update((left, both + 1, lost, direct)
                        for left, both, lost, direct in phase_outcomes(pool - 2, outsiders))
        if outsiders:
            outcomes.update((left, both, lost + 1, direct) for left, both, lost, direct
                            in phase_outcomes(pool - 1, outsiders - 1))
    return outcomes


def check_phases():
    checked = 0
    for pool in range(17):
        for outsiders in range(9):
            outcomes = phase_outcomes(pool, outsiders)
            for left, both, lost, direct in outcomes:
                assert left == pool - 2 * both - lost
                assert lost + direct <= outsiders
                if left < (pool + outsiders + 1) // 2:
                    assert 4 * (both + outsiders) > pool + outsiders
                checked += 1
            if not outsiders:
                assert outcomes == {(pool - 2*f, f, 0, 0) for f in range(pool // 2 + 1)}
    return checked


if __name__ == '__main__':
    cases, traces = check_planted_rows()
    print(f'{cases} planted-row parameters and {traces} empty-table traces')
    print(f'{check_tolerant_rule()} pool layouts and retirement orders for the tolerant rule')
    print(f'{check_phases()} phase outcomes, including the clean chronological recurrence')
