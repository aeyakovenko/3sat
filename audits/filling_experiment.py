"""Check the local equations and cut width of both parity-filling constructions."""

from itertools import product


def inspect(bottom, height, horizontal, vertical):
    """Number gaps from 0 at the left or bottom to width or height at the opposite side."""
    width = len(bottom)
    for j in range(height):
        assert horizontal(0, j) == horizontal(width, j) == 0
    for i, charge in enumerate(bottom):
        assert vertical(i, 0) == charge
        assert vertical(i, height) == 0
        for j in range(height):
            assert horizontal(i, j) ^ horizontal(i + 1, j) == vertical(i, j) ^ vertical(i, j + 1)
    cuts = [sum(horizontal(gap, j) for j in range(height)) for gap in range(width + 1)]
    parity = 0
    for i, charge in enumerate(bottom):
        parity ^= charge
        assert cuts[i + 1] % 2 == parity
    return cuts


def grouped(bits, probes):
    n = len(bits)
    groups = (n + probes - 1) // probes

    def horizontal(gap, row):
        lo, hi = row * probes, min((row + 1) * probes, n)
        return sum(bits[i] for i in range(lo, hi) if (i < gap) != (i + n < gap)) % 2

    def vertical(i, gap):
        return bits[i % n] if gap <= (i % n) // probes else 0

    return inspect(bits * 2, groups, horizontal, vertical)


def matchings(points):
    if not points:
        yield []
        return
    left = points[0]
    for j in range(1, len(points)):
        for remaining in matchings(points[1:j] + points[j + 1:]):
            yield [(left, points[j])] + remaining


def paired(n, pairs):
    mate = {endpoint: other for i, j in pairs for endpoint, other in ((i, j), (j, i))}
    bottom = tuple(int(i in mate) for i in range(n))

    def horizontal(gap, row):
        return int(row in mate and row < gap <= mate[row])

    def vertical(i, gap):
        return int(i in mate and gap <= min(i, mate[i]))

    return inspect(bottom, n, horizontal, vertical)


def main():
    group_checks = pair_checks = 0
    for n in range(1, 8):
        for b in range(1, n + 1):
            worst = 0
            for bits in product((0, 1), repeat=n):
                cuts = grouped(bits, b)
                assert max(cuts) <= (n + b - 1) // b
                worst = max(worst, cuts[n])
                group_checks += 1
            assert worst == (n + b - 1) // b
        for bits in product((0, 1), repeat=n):
            points = [i for i, bit in enumerate(bits) if bit]
            if len(points) % 2 == 0:
                for pairs in matchings(points):
                    paired(n, pairs)
                    pair_checks += 1
    print(f'Checked {group_checks} grouped fillings and {pair_checks} pairings.')


if __name__ == '__main__':
    main()
