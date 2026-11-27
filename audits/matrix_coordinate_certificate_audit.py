"""Compare monochromatic cubes and Boolean derivatives for all binary 2×2 triples."""

from collections import Counter
from functools import cache
from itertools import combinations, product


def edges(i, k, j):
    return 1 << (2 * i + k), 1 << (4 + 2 * k + j), 1 << (8 + 2 * j + i)


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub - 1) & mask


def main():
    dimension = 12
    full = (1 << dimension) - 1
    triangles = [sum(edges(i, k, j)) for i, k, j in product(range(2), repeat=3)]
    values = [sum(x & t == t for t in triangles) % 2 for x in range(full + 1)]

    @cache
    def mono(free, fixed):
        if not free:
            return values[fixed]
        low = free & -free
        a = mono(free ^ low, fixed)
        if a == -1:
            return -1
        b = mono(free ^ low, fixed | low)
        return a if a == b else -1

    @cache
    def sensitive(x):
        return sum(1 << i for i in range(dimension) if values[x] != values[x ^ (1 << i)])

    # An incident pair has the closing bit itself as its second difference.
    closing = []
    for triangle in triangles:
        three = [1 << i for i in range(dimension) if triangle & (1 << i)]
        for first, second in combinations(three, 2):
            closing.append((first | second, triangle ^ first ^ second))

    cube_count = 0
    for free in range(full + 1):
        has_triangle = any(free & t == t for t in triangles)
        closing_bits = 0
        for pair, bit in closing:
            if free & pair == pair:
                closing_bits |= bit
        for fixed in submasks(full ^ free):
            predicted = not (has_triangle or fixed & closing_bits or free & sensitive(fixed))
            assert predicted == (mono(free, fixed) != -1)
            cube_count += 1

    sizes = Counter()
    greedy_total = 0
    for x in range(full + 1):
        inactive = full ^ sensitive(x)
        best = max(free.bit_count() for free in submasks(inactive) if mono(free, x & ~free) != -1)
        sizes[dimension - best] += 1
        free = 0
        for k in range(2):
            left = sum(edges(i, k, 0)[0] for i in range(2)) & inactive
            right = sum(edges(0, k, j)[1] for j in range(2)) & inactive
            free |= max((left, right), key=int.bit_count)
        assert mono(free, x & ~free) == values[x]
        assert free.bit_count() <= best
        greedy_total += 8 + sum(bool((1 << i) & sensitive(x)) for i in range(8, 12))
    assert greedy_total == 38 * 1024  # Eight mandatory bits plus four dot products of mean 3/8.
    print(f"{cube_count} partial matrices checked; certificate-size census {sorted(sizes.items())}")
    print(f"Fixed two-block algorithm: {greedy_total}/{full + 1} input-bit probes on average")


if __name__ == "__main__":
    main()
