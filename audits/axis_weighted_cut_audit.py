"""Exact exponent arithmetic and exhaustive offset checks for rectangular tape cuts."""

from fractions import Fraction as F
from itertools import combinations, product
from math import prod


def positive(x):
    return max(x, 0)


def conditions(c, omega, motion):
    return (c * (1 + omega) < 1 + 1 / c and
            c + sum(positive(c * mu - 1 / c) for mu in motion) < 1 + 1 / c)


def subset_conditions(c, omega, motion, one_pass=False):
    right = 2 if one_pass else c + 1
    return (c*c*(1 + omega) < right and
            all(c*c * (1 + sum(group)) < right + k
                for k in range(len(motion) + 1) for group in combinations(motion, k)))


def exponent_checks():
    checks = 0
    for d in (1, 2, 3):
        for c in (F(1), F(11, 10), F(6, 5), F(3, 2)):
            for omega in (F(0), F(1, 4), F(1, 2), F(1)):
                for motion in product((F(0), F(1, 2), F(1), 1 + omega), repeat=d):
                    assert conditions(c, omega, motion) == subset_conditions(c, omega, motion)
                    checks += 1
                for rho in (0, omega/2, omega):
                    old = ((d + 1 + d*rho)*c*c < c + d + 1 and
                           (1 + omega)*c*c < c + 1)
                    assert conditions(c, omega, (1 + rho,)*d) == old
                    checks += 1

    c, omega, motion = F(11, 10), F(1, 2), (F(3, 2), F(1, 2))
    x, y = F(99, 100), F(9, 10)
    z = tuple(positive(c*mu - y) for mu in motion)
    assert z == (F(3, 4), 0)
    assert all(c*mu - side <= y for mu, side in zip(motion, z))
    assert max(c*(1 + omega), c + sum(z)) < x + y
    assert not conditions(c, omega, (max(motion),)*2)
    assert not subset_conditions(c, omega, motion, one_pass=True)
    e, steps = c, 0
    while e >= 1:
        g = max(c*y, e*x)
        assert g == e*x < e
        e, steps = g, steps + 1
    assert steps == 10
    assert max(c*y, 1*x) < 1
    return checks, steps


def inspect_offsets(positions, weights, sides, cap):
    volume = prod(sides)
    axes = range(len(sides))
    motion = [sum(weights[t] for t in range(1, len(weights))
                  if positions[t-1][i] != positions[t][i]) for i in axes]
    expected_spatial = sum(F(mass, side) for mass, side in zip(motion, sides))
    bound = expected_spatial + F(sum(weights) + volume*len(weights), cap)
    spatial_sum, cost_sum, best = 0, 0, None
    for shift in product(*(range(u) for u in sides)):
        tiles = [tuple((pos[i] - shift[i]) // sides[i] for i in axes) for pos in positions]
        crossings = {t for t in range(1, len(tiles)) if tiles[t] != tiles[t-1]}
        spatial_sum += sum(weights[t] for t in crossings)
        visits = {}
        for t, tile in enumerate(tiles):
            visits.setdefault(tile, []).append(t)
        for residue in range(cap):
            cuts = set()
            for times in visits.values():
                edges = [j for j in range(1, len(times)) if j % cap == residue]
                cuts.update(times[j] for j in edges)
                endpoints = [0, *edges, len(times)]
                assert all(b-a <= cap for a, b in zip(endpoints, endpoints[1:]))
            cost = sum(weights[t] for t in crossings | cuts) + volume*len(cuts)
            cost_sum += cost
            best = cost if best is None else min(best, cost)
    assert F(spatial_sum, volume) == expected_spatial
    assert best <= F(cost_sum, volume*cap) <= bound
    return volume * cap


def offset_checks():
    cases = choices = 0
    moves = ((-1, 0), (1, 0), (0, -1), (0, 1), (0, 0))
    for path in product(moves, repeat=4):
        positions = [(0, 0)]
        for dx, dy in path:
            x, y = positions[-1]
            positions.append((x+dx, y+dy))
        for weights in ((1, 2, 3, 2, 1), (1, 1, 2, 2, 3)):
            for sides, cap in (((1, 3), 2), ((3, 2), 3)):
                choices += inspect_offsets(positions, weights, sides, cap)
                cases += 1
    return cases, choices


if __name__ == '__main__':
    comparisons, rounds = exponent_checks()
    cases, choices = offset_checks()
    print(f'{comparisons} exact exponent comparisons; planar example crosses 1 in {rounds} rounds')
    print(f'{cases} weighted path/box/cap cases; {choices} offset/residue choices checked')
