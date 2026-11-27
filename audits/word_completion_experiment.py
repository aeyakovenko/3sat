"""Exhaustive finite checks for per-word prices, truncated allocation, and hidden shifts."""
from fractions import Fraction
from itertools import combinations, product


def check_prices():
    checked = 0
    # Scaled target sets of sizes 2, 4 and 8. Masks can certify any subset.
    sizes = (2, 4, 8)
    for masks in product(*(range(1 << size) for size in sizes)):
        deficiencies = [Fraction(size - mask.bit_count(), size)
                        for size, mask in zip(sizes, masks)]
        ordered = sorted(range(len(sizes)), key=lambda i: (deficiencies[i], i))
        for h in range(1, len(sizes) + 1):
            cost = sum(deficiencies[i] for i in ordered[:h])
            optimum = min(sum(deficiencies[i] for i in subset)
                          for subset in combinations(range(len(sizes)), h))
            assert cost == optimum
            checked += 1
    return checked


def check_allocation():
    checked = 0
    depths = (1, 3, 4, 6)
    base = 1 << depths[-1]
    for counts in product(range(6), repeat=len(depths)):
        endpoint = 0
        cells = set()
        requested = 0
        for depth, count in zip(depths, counts):
            width = base >> depth
            requested += count * width
            assert endpoint % width == 0
            first = endpoint // width
            funded = min(count, (base - endpoint) // width)
            for rank in range(funded):
                cell = first + rank
                leaves = set(range(cell * width, (cell + 1) * width))
                assert not cells.intersection(leaves)
                cells.update(leaves)
                for leaf in leaves:
                    assert leaf // width - first == rank
            endpoint += funded * width
        assert len(cells) == min(requested, base) == endpoint
        checked += 1
    return checked


def check_hidden_keys():
    checked = 0
    for bits in range(1, 7):
        size = 1 << bits
        universe = set(range(size))
        for k in range(size // 2 + 1):
            common = universe.copy()
            for key in universe:
                def transform(x):
                    return (x - 1 if x < 2 * k and x % 2 else x) ^ key
                image = {transform(x) for x in universe}
                paid = {(2 * rank + 1) ^ key for rank in range(k)}
                assert len(image) == size - k and paid == universe - image
                common.intersection_update(image)
                checked += 1
            assert common == (universe if k == 0 else set())
    return checked


def check_common_phases():
    checked = 0
    different_windows = False
    for arrivals in product(range(3), repeat=3):
        cleared = []
        for needs in product(range(4), repeat=3):
            available = 0
            spent = []
            for incoming, requested in zip(arrivals, needs):
                available += incoming
                paid = min(available, requested)
                spent.append(paid)
                available -= paid
            if available == 0:
                assert sum(spent) == sum(arrivals)
                cleared.append(tuple(spent))
        for left, right in combinations(cleared, 2):
            assert sum(left) == sum(right)
            different_windows |= left != right
            checked += 1
    assert different_windows
    return checked


if __name__ == "__main__":
    print(f"{check_prices()} optimal selections, {check_allocation()} allocations, "
          f"{check_hidden_keys()} hidden-key maps, {check_common_phases()} cleared phase pairs")
