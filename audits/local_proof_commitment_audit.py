"""Finite minimax and adaptive-anchor checks for local-proof-commitments.md."""

from functools import lru_cache
from itertools import combinations, product


def masks_by_size(count):
    for size in range(count + 1):
        for choice in combinations(range(count), size):
            yield sum(1 << i for i in choice)


def dot(left, right):
    return (left & right).bit_count() % 2


def failed_sets(rows, rhs, variables):
    return [
        sum((dot(row, x) ^ ((rhs >> i) & 1)) << i for i, row in enumerate(rows))
        for x in range(1 << variables)
    ]


def blocker_cost(failures, tests, colors):
    groups = {}
    for failed, color in zip(failures, colors):
        groups.setdefault(color, []).append(failed)
    return max(
        next(s.bit_count() for s in tests if all(s & failed for failed in group))
        for group in groups.values()
    )


def all_partitions(length, max_colors):
    def extend(prefix, count):
        if len(prefix) == length:
            yield tuple(prefix)
            return
        for color in range(min(count + 1, max_colors)):
            yield from extend(prefix + [color], max(count, color + 1))

    yield from extend([], 0)


def adaptive_optima(variables, failures, tests):
    @lru_cache(maxsize=None)
    def best(domain, remaining):
        result = next(s.bit_count() for s in tests if all(s & failures[x] for x in domain))
        if remaining:
            for parity in range(1, 1 << variables):
                zero = tuple(x for x in domain if not dot(x, parity))
                one = tuple(x for x in domain if dot(x, parity))
                if zero and one:
                    result = min(result, max(best(zero, remaining - 1), best(one, remaining - 1)))
        return result

    return [best(tuple(range(1 << variables)), p) for p in range(3)]


def audit_minimax():
    cases = 0
    variables = 2
    nonlinear = {h: list(all_partitions(1 << variables, h)) for h in range(1, 5)}
    linear = {
        p: [
            [tuple(dot(row, x) for row in sketch) for x in range(1 << variables)]
            for sketch in product(range(1 << variables), repeat=p)
        ]
        for p in range(3)
    }
    # Include duplicate and zero left-hand sides, short contradictions, and triangles.
    for rows in combinations(range(8), 4):
        matrix = [r % 4 for r in rows]
        tests = tuple(masks_by_size(len(rows)))
        for rhs in range(1 << len(rows)):
            failures = failed_sets(matrix, rhs, variables)
            if 0 in failures:
                continue
            distance = blocker_cost(failures, tests, [0] * len(failures))
            for p, optimum in enumerate(adaptive_optima(variables, failures, tests)):
                assert optimum == (distance + (1 << p) - 1) // (1 << p)
            for h, choices in nonlinear.items():
                optimum = min(blocker_cost(failures, tests, c) for c in choices)
                assert optimum == (distance + h - 1) // h
            for p, choices in linear.items():
                optimum = min(blocker_cost(failures, tests, c) for c in choices)
                assert optimum == (distance + p) // (p + 1)
            cases += 1
    return cases


def audit_projections():
    # A cycle has one full parity contradiction. For up to two selected rows its
    # odd boundary has at least as many vertices as there are selected rows.
    n = 7
    rows = [(1 << i) | (1 << ((i + 1) % n)) for i in range(n)]
    t = 1
    combinations_to_test = []
    for z in masks_by_size(n):
        if z.bit_count() > 2 * t:
            continue
        boundary = 0
        for i, row in enumerate(rows):
            if (z >> i) & 1:
                boundary ^= row
        assert boundary.bit_count() >= z.bit_count()
        if z.bit_count() <= t:
            combinations_to_test.append((z, boundary))
    # We also check larger supports where closure actually holds. Derive all
    # short consequences and retain supports for which their preimages form a space.
    cases = 0
    for rhs in (0, 1, 23, 37, 127):
        feasible = {}
        for support in masks_by_size(n):
            equations = [(z, image) for z, image in combinations_to_test if not image & ~support]
            preimages = {z for z, _ in equations}
            if any(z ^ other not in preimages for z in preimages for other in preimages):
                continue
            feasible[support] = {
                x & support for x in range(1 << n)
                if all(dot(x, image) == dot(z, rhs) for z, image in equations)
            }
            assert feasible[support]
        for small, labels in feasible.items():
            for large, extended in feasible.items():
                if not small & ~large:
                    assert {x & small for x in extended} == labels
                    cases += 1
    return cases


if __name__ == '__main__':
    print(f'{audit_minimax()} inconsistent systems passed all commitment optima')
    print(f'{audit_projections()} nested supports preserved feasible projections')
