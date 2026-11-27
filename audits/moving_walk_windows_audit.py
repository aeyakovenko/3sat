"""Check the moving binary cube and time-varying moments on the actual MGG labels."""

from fractions import Fraction
from itertools import product
from math import isqrt, prod
from random import Random

from packed_row_queries import MGG_STEPS, mgg_segment, mgg_step, mgg_transition


def shift(columns, vertex, offset):
    side = isqrt(columns)
    y, x = divmod(vertex, side)
    return side * y + (x + offset) % side


def follow(columns, start, labels):
    for label in labels:
        start = mgg_step(columns, start, label)
    return start


def packed(labels):
    return sum(label << (4 * index) for index, label in enumerate(labels))


def lifted_transition(center_moves, was_shifted, becomes_shifted):
    # Forward translation uses labels 2,1 and its inverse uses 0,3.
    before = [0, 3] if was_shifted else [8, 8]
    after = [2, 1] if becomes_shifted else [8, 8]
    labels = before + center_moves + after
    assert len(labels) == MGG_STEPS
    return packed(labels)


def check_cubes():
    rng = Random(81722)
    edge_checks = cube_checks = 0
    for columns in (4, 16, 64):
        for start in range(columns):
            assert follow(columns, start, [2, 1]) == shift(columns, start, 1)
            assert follow(columns, start, [0, 3]) == shift(columns, start, -1)
            moves = [rng.randrange(16) for _ in range(MGG_STEPS - 4)]
            end = follow(columns, start, moves)
            for a, b in product((0, 1), repeat=2):
                label = lifted_transition(moves, a, b)
                assert mgg_transition(columns, shift(columns, start, a), label) == shift(columns, end, b)
                edge_checks += 1
        for _ in range(3):
            centers = [rng.randrange(columns)]
            steps = []
            for _ in range(3):
                moves = [rng.randrange(16) for _ in range(MGG_STEPS - 4)]
                centers.append(follow(columns, centers[-1], moves))
                steps.append(moves)
            pairs = [(v, shift(columns, v, 1)) for v in centers]
            padding = [sum(1 << v for v in sorted(set(range(columns)) - set(pair))[:columns // 2 - 1])
                       for pair in pairs]
            selectors = {}
            for choices in product((0, 1), repeat=4):
                seed = pairs[0][choices[0]]
                for i, moves in enumerate(steps):
                    seed += columns * (lifted_transition(moves, choices[i], choices[i + 1])
                                       << (4 * MGG_STEPS * i))
                selectors[choices] = mgg_segment(columns, 4, seed)
                assert selectors[choices] == tuple(pair[bit] for pair, bit in zip(pairs, choices))
            for payload in product((0, 1), repeat=4):
                masks = [other | (1 << pair[bit]) for other, pair, bit in zip(padding, pairs, payload)]
                assert all(mask.bit_count() == columns // 2 for mask in masks)
                for choices, walk in selectors.items():
                    assert all(mask & (1 << v) for mask, v in zip(masks, walk)) == (choices == payload)
                    cube_checks += 1
    return edge_checks, cube_checks


def exact_moment(columns, sets, transition, denominator):
    weights = [1] * columns
    for i, observed in enumerate(sets):
        if i:
            weights = [sum(multiplicity * value for multiplicity, value in zip(counts, weights))
                       for counts in transition]
        weights = [value * (1 + (v in observed)) for v, value in enumerate(weights)]
    return Fraction(sum(weights), columns * denominator ** (len(sets) - 1))


def check_moments():
    rng = Random(27342)
    count = 0
    for columns in (4, 16):
        # Build exact transition counts, including labels with the same endpoint.
        incoming = [[mgg_step(columns, v, label) for label in range(16)] for v in range(columns)]
        power = MGG_STEPS - 4
        transition = []
        for target in range(columns):
            paths = [int(v == target) for v in range(columns)]
            for _ in range(power):
                paths = [sum(paths[v] for v in neighbors) for neighbors in incoming]
            transition.append(paths)
        denominator = 16 ** power
        assert all(sum(row) == denominator for row in transition)
        for _ in range(40):
            cells = [set(rng.sample(range(columns), rng.randrange(columns // 2 + 1)))
                     for _ in range(rng.randrange(2, 9))]
            hits = [row | {shift(columns, v, -1) for v in row} for row in cells]
            moment = exact_moment(columns, hits, transition, denominator)
            bound = prod(Fraction(columns + 2 * len(hit), columns) for hit in hits)
            assert 1 <= moment <= bound
            count += 1
    return count


if __name__ == "__main__":
    edges, cube_entries = check_cubes()
    moments = check_moments()
    print(f"{edges} shifted 160-step edges, {cube_entries} moving-cube equality entries, "
          f"{moments} exact time-varying moment bounds")
