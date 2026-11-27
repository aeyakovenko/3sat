"""Exhaust small one-way missing-image examples over binary vector spaces."""

from collections import Counter
from itertools import combinations, product


def dot(a, b):
    return (a & b).bit_count() & 1


def linear(rows, value):
    return sum(dot(row, value) << bit for bit, row in enumerate(rows))


def no_antiperiod(red):
    """A balanced coloring passes when no nonzero translation swaps its colors."""
    for shift in range(1, 16):
        same = [x for x in range(16) if (x in red) == ((x ^ shift) in red)]
        if not same:
            return False
        assert any(x in red for x in same)
        assert any(x not in red for x in same)
    return True


def audit_coloring():
    colors = []
    for members in combinations(range(16), 8):
        red = frozenset(members)
        if no_antiperiod(red):
            colors.append(red)
    assert len(colors) == 10080
    red = colors[0]
    answer_sizes = Counter()
    for rows in product(range(16), repeat=3):
        red_image = {linear(rows, u) for u in red}
        blue_image = {linear(rows, u) for u in range(16) if u not in red}
        assert len(red_image) < 8 and len(blue_image) < 8
        answer_sizes[(8 - len(red_image), 8 - len(blue_image))] += 1
    assert sum(answer_sizes.values()) == 4096
    print(f"{len(colors)} ordered balanced colorings have no antiperiod; example {sorted(red)}")
    print(f"4096 full maps from 4 bits to 3, both images omit an output: {sorted(answer_sizes.items())}")


def audit_systematic_maps():
    dimension, middle = 4, 3
    inputs = range(1 << dimension)
    uniformity = [Counter() for _ in inputs]
    bob_maps = set()
    balanced_counts = Counter()
    # An eight-point graph with a nonlinear high bit.
    graph = [x | (((x & 3) == 3) << 3) for x in range(8)]
    for diagonals in range(1 << (dimension + middle - 1)):
        rows = tuple((diagonals >> shift) & 15 for shift in range(middle))
        outputs = [linear(rows, u) for u in inputs]
        for u in inputs:
            uniformity[u][outputs[u]] += 1
        injective = len({outputs[u] for u in graph}) == len(graph)
        halves = [{outputs[u] for u in graph if outputs[u] & 1 == side} for side in (0, 1)]
        balanced = min(map(len, halves)) >= 3
        balanced_counts[(injective, balanced)] += 1
        shared_projections = 0
        for second_row in range(1 << middle):
            table = tuple((t & 1) + 2 * dot(second_row, t) for t in outputs)
            bob_maps.add(table)
            assert all((table[u] & 1) == dot(diagonals & 15, u) for u in inputs)
            covers_halves = all({dot(second_row, t) for t in half} == {0, 1} for half in halves)
            assert covers_halves == ({table[u] for u in graph} == {0, 1, 2, 3})
            shared_projections += covers_halves
        if injective and balanced:
            assert shared_projections != 0
    assert balanced_counts[True, True] == 6
    assert len(bob_maps) == 212
    assert all(set(count) == set(range(8)) and set(count.values()) == {8} for count in uniformity[1:])

    # Check the smallest size where every subset is covered by one structured
    # Bob choice. Monotonicity then covers all larger subsets at this dimension.
    for size in range(4, 17):
        failed = 0
        for subset in combinations(inputs, size):
            if not any(len({table[u] for u in subset}) == 4 for table in bob_maps):
                failed += 1
        if failed == 0:
            assert size == 4
            print(f"{len(bob_maps)} distinct systematic maps; every {size}-point subset has a map covering four outputs")
            break
    else:
        raise AssertionError("a full-rank systematic map must cover the full domain")
    print(f"all 15 nonzero differences hash uniformly; {balanced_counts[True, True]} injective balanced hashes")


if __name__ == "__main__":
    audit_coloring()
    audit_systematic_maps()
