"""Solve the exact individual-direction matrix agreement equations over F_2."""

from collections import Counter
from fractions import Fraction


def dot(x, y):
    return (x & y).bit_count() % 2


def apply_matrix(w, v, d):
    mask = (1 << d) - 1
    return sum(dot((w >> (i * d)) & mask, v) << i for i in range(d))


def affine_row(B, constant, left, d):
    row = constant
    for i in range(d):
        if left >> i & 1:
            row ^= (B >> (i * d)) & ((1 << d) - 1)
    return row


def verify(d):
    inputs = 1 << (d * d)
    equations = {}
    fibers = []
    for v in range(1, 1 << d):
        by_x = [[] for _ in range(1 << d)]
        for B in range(inputs):
            by_x[apply_matrix(B, v, d)].append(B)
        for group in by_x:
            fibers.append((v, group))
            for B in group[1:]:
                relation = (v << (group[0] * d)) ^ (v << (B * d))
                while relation:
                    pivot = relation.bit_length() - 1
                    if pivot not in equations:
                        equations[pivot] = relation
                        break
                    relation ^= equations[pivot]
    nullity = d * inputs - len(equations)
    models = [[affine_row(B, c, left, d) for B in range(inputs)]
              for c in range(1 << d) for left in range(1 << d)]
    assert nullity == 2 * d
    assert len({tuple(h) for h in models}) == 1 << nullity
    assert all(len({dot(h[B], v) for B in group}) == 1
               for h in models for v, group in fibers)

    distances = []
    for edits in (1, 2, 3):
        h = [int(B < edits) for B in range(inputs)]
        distance = Fraction(min(sum(a != b for a, b in zip(h, target))
                                for target in models), inputs)
        failures = 0
        for v, group in fibers:
            counts = Counter(dot(h[B], v) for B in group)
            failures += 2 * counts[0] * counts[1]
        error = Fraction(failures, len(fibers) * len(fibers[0][1]) ** 2)
        assert distance == Fraction(edits, inputs)
        assert 0 < error <= 2 * distance
        distances.append((str(distance), str(error)))
    print(f"d={d}: one-row kernel dimension {nullity}, (distance, rejection) {distances}")


if __name__ == "__main__":
    for dimension in (2, 3):
        verify(dimension)
