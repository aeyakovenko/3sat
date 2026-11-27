"""Exhaust menus, histogram reconstruction, and perturbations of actual maxima."""

from collections import defaultdict, deque
from itertools import combinations, permutations, product
from math import comb, factorial, prod


def histogram(names, width):
    counts = [0] * width
    for name in names:
        counts[name] += 1
    return tuple(counts)


def decode(menus, counts):
    """Decode a histogram in the common-order model, or reject it."""
    width = len(counts)
    if sum(counts) != len(menus) or any(h < 0 for h in counts):
        return None
    incidence = [[] for _ in counts]
    for row, menu in enumerate(menus):
        if not menu:
            return None
        for label in menu:
            incidence[label].append(row)
    degree = list(map(len, incidence))
    left = list(counts)
    if any(h > d for h, d in zip(left, degree)):
        return None
    queue = deque(v for v in range(width) if left[v] == degree[v] > 0)
    names = [None] * len(menus)
    while queue:
        v = queue.popleft()
        if degree[v] == 0 or left[v] != degree[v]:
            continue
        for row in incidence[v]:
            if names[row] is not None:
                continue
            names[row] = v
            left[v] -= 1
            for u in menus[row]:
                degree[u] -= 1
                if left[u] > degree[u]:
                    return None
                if u != v and left[u] == degree[u] > 0:
                    queue.append(u)
    return tuple(names) if all(v is not None for v in names) else None


def verify_noise(menus, actual, proposal, width):
    first = histogram(actual, width)
    second = histogram(proposal, width)
    distance = sum(max(0, a - b) for a, b in zip(first, second))
    illegal = sum(v not in menu for v, menu in zip(proposal, menus))
    wrong = sum(a != b for a, b in zip(actual, proposal))
    upper = (width - 1) * distance + width * illegal
    assert wrong <= upper
    return wrong, upper


def check_fibers():
    hist_tests = noise_tests = 0
    for width, rows in ((1, 2), (2, 3), (3, 3), (4, 2)):
        labels = range(width)
        subsets = [tuple(x for x in labels if mask & (1 << x))
                   for mask in range(1, 1 << width)]
        histograms = {histogram(xs, width) for xs in product(labels, repeat=rows)}
        for menus in product(subsets, repeat=rows):
            fibers = defaultdict(list)
            for allocation in product(*menus):
                fibers[histogram(allocation, width)].append(allocation)
            extrema = {tuple(max(menu, key=order.index) for menu in menus)
                       for order in permutations(labels)}
            for h in histograms:
                decoded = decode(menus, h)
                if len(fibers[h]) == 1:
                    assert decoded == fibers[h][0] and decoded in extrema
                else:
                    assert decoded is None
                    assert all(word not in extrema for word in fibers[h])
                hist_tests += 1
            actual = tuple(map(max, menus))
            for proposed in product(labels, repeat=rows):
                verify_noise(menus, actual, proposed, width)
                noise_tests += 1
    return hist_tests, noise_tests


def sharp_examples():
    tests = 0
    for width in range(2, 9):
        for distance, illegal in product(range(5), repeat=2):
            menus = []
            actual = []
            proposed = []
            for hi in range(1, width):
                for _ in range(distance + illegal):
                    menus.append((hi - 1, hi))
                    actual.append(hi)
                    proposed.append(hi - 1)
            for _ in range(illegal):
                menus.append((0,))
                actual.append(0)
                proposed.append(width - 1)
            got, bound = verify_noise(menus, actual, proposed, width)
            assert got == bound == (width - 1) * distance + width * illegal
            tests += 1
    return tests


def suffixes():
    tests = 0
    for j in range(1, 10):
        length = 1 << j
        for sign in (0, 1):
            replies = [sign ^ (i % 2) for i in range(length)]
            assert histogram(replies, 2) == (length // 2, length // 2)
            for i, reply in enumerate(replies):
                assert sign == reply ^ (i % 2)
                tests += 1
    return tests


def adaptive_tables():
    trials = 0
    for width in range(2, 6):
        labels = range(width)
        menus = [tuple(i for i in labels if mask & (1 << i))
                 for mask in range(1, 1 << width)]
        for sizes in ((1, 2), (2, 1, 1), (2, 2)):
            column_options = [{histogram(word, width) for word in product(labels, repeat=size)}
                              for size in sizes]
            table_counts = defaultdict(int)
            for table in product(*column_options):
                table_counts[tuple(map(sum, zip(*table)))] += 1
            for seed in range(6):
                seen = defaultdict(dict)
                for order in permutations(labels):
                    replies = ()
                    table = []
                    for batch, size in enumerate(sizes):
                        state = seed + batch + sum((i + 1) * (v + 1) for i, v in enumerate(replies))
                        batch_menus = [menus[(state * (i + 2) + 3 * i) % len(menus)]
                                       for i in range(size)]
                        winners = tuple(max(menu, key=order.index) for menu in batch_menus)
                        column = histogram(winners, width)
                        assert decode(batch_menus, column) == winners
                        table.append(column)
                        replies += winners
                    margin = histogram(replies, width)
                    assert seen[margin].setdefault(tuple(table), replies) == replies
                    trials += 1
                for margin, histories in seen.items():
                    assert len(histories) <= table_counts[margin]
                    assert table_counts[margin] <= prod(comb(h + len(sizes) - 1, len(sizes) - 1)
                                                        for h in margin)
    return trials


def group_removal():
    for width, rounds in ((4, 2), (6, 2), (6, 3), (6, 6)):
        histories = set()
        for order in permutations(range(width)):
            groups = [set(range(i, i + rounds)) for i in range(0, width, rounds)]
            replies = []
            for _ in range(rounds):
                for group in groups:
                    winner = max(group, key=order.index)
                    group.remove(winner)
                    replies.append(winner)
            assert histogram(replies, width) == (1,) * width
            histories.add(tuple(replies))
        assert len(histories) == factorial(rounds) ** (width // rounds)


def sample_and_pointer_counts():
    sample_tests = pointer_tests = 0
    for width in range(1, 7):
        labels = range(width)
        orders = list(permutations(labels))
        # Relabeling a common observed reply reduces any nonempty fiber to this one.
        for size in range(width + 1):
            for observed in combinations(labels, size):
                fiber = [v for v in orders if all(v[i] == i for i in observed)]
                furthest = max(sum(i != x for i, x in enumerate(v)) for v in fiber)
                assert furthest == (width - size if width - size >= 2 else 0)
                sample_tests += 1
        paths = set()
        for tail in permutations(range(1, width)):
            cycle = (0,) + tail
            successor = dict(zip(cycle, cycle[1:] + (0,)))
            memory = [successor[j] for j in labels]
            address = 0
            path = []
            for _ in labels:
                path.append(address)
                address = memory[address]
            assert address == 0 and tuple(path) == cycle
            paths.add(tuple(path))
            pointer_tests += 1
        assert len(paths) == factorial(width - 1)
    return sample_tests, pointer_tests


def two_round_matchings():
    tests = 0
    for width, rows in ((2, 2), (3, 2), (4, 2), (5, 2), (4, 3), (5, 3)):
        labels = range(width)
        menus = [tuple(i for i in labels if mask & (1 << i))
                 for mask in range(1, 1 << width)]
        orders = list(permutations(labels))
        winners = {menu: [max(menu, key=order.index) for order in orders] for menu in menus}
        assignments = {subset: list(permutations(subset)) for subset in combinations(labels, rows)}
        largest = 0
        for first in product(menus, repeat=rows):
            possible = {tuple(sorted(out)) for out in zip(*(winners[menu] for menu in first))
                        if len(set(out)) == rows}
            unique = {subset for subset, matchings in assignments.items()
                      if sum(all(x in menu for x, menu in zip(match, first)) for match in matchings) == 1}
            assert possible == unique
            largest = max(largest, len(unique))
            tests += 1
        if rows == 2:
            assert largest == width ** 2 // 3
        remaining = width - rows + 2
        assert largest * comb(remaining, 2) <= comb(width, rows) * (remaining ** 2 // 3)
    return tests


if __name__ == "__main__":
    fiber_count, noise_count = check_fibers()
    print(f"{fiber_count} exact histogram decoding and fiber tests")
    print(f"{noise_count} perturbations of ordered menu maxima")
    print(f"{sharp_examples()} jointly sharp configurations")
    print(f"{suffixes()} suffix sign recoveries")
    print(f"{adaptive_tables()} hidden-order trials with adaptive batch decoding and table bounds")
    group_removal()
    print("Grouped removal counts verified for four choices of width and rounds")
    samples, paths = sample_and_pointer_counts()
    print(f"{samples} position samples and {paths} fixed-start pointer paths")
    print(f"{two_round_matchings()} first-batch menu families checked against unique matchings")
