"""Finite grid check with signed coordinates, multiple moving heads and canonical shifts."""

from itertools import product


def moves(dim):
    return [(0,) * dim] + [tuple(sign if i == axis else 0 for i in range(dim))
                           for axis in range(dim) for sign in (-1, 1)]


def walk(start, steps):
    positions = [start]
    for delta in steps:
        positions.append(tuple(x + y for x, y in zip(positions[-1], delta)))
    return positions


def cube(pos, shift, side):
    return tuple((x - shift) // side for x in pos)


def histogram(path, side):
    counts = [0] * side
    for p, q in zip(path, path[1:]):
        changed = [i for i, (x, y) in enumerate(zip(p, q)) if x != y]
        if changed:
            assert len(changed) == 1
            i = changed[0]
            counts[max(p[i], q[i]) % side] += 1
    actual = [sum(cube(p, r, side) != cube(q, r, side) for p, q in zip(path, path[1:]))
              for r in range(side)]
    assert counts == actual
    return counts


def main():
    walks = list(product(moves(2), repeat=3))
    checked = 0
    for side in (2, 3, 4):
        first = [(walk((-2, 1), steps), histogram(walk((-2, 1), steps), side)) for steps in walks]
        second = [(walk((1, -1), steps), histogram(walk((1, -1), steps), side)) for steps in walks]
        for (a, ah), (b, bh) in product(first, second):
            total = [x + y for x, y in zip(ah, bh)]
            threshold = 6 // side
            shift = next(i for i, count in enumerate(total) if count <= threshold)
            assert all(count > threshold for count in total[:shift])
            boundaries = {0, len(a) - 1}
            boundaries.update(range(side, len(a), side))
            for time in range(1, len(a)):
                if any(cube(p[time], shift, side) != cube(p[time - 1], shift, side) for p in (a, b)):
                    boundaries.add(time)
            ordered = sorted(boundaries)
            for start, end in zip(ordered, ordered[1:]):
                assert end - start <= side
                for p in (a, b):
                    assert len({cube(pos, shift, side) for pos in p[start:end]}) == 1
            checked += 1
    print(f'{checked} two-head paths and side lengths passed the scalar-shift and segment checks')


if __name__ == '__main__':
    main()
