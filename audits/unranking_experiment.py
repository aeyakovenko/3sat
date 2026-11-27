"""Exhaustively check attainable unions and bounded rank choices on four slots."""
from itertools import combinations_with_replacement, permutations, product


def fill(mask, interval, rank=1):
    lo, hi = interval
    for slot in range(lo, hi + 1):
        if not (mask & (1 << slot)):
            rank -= 1
            if not rank:
                return mask | (1 << slot)
    return mask


def sorted_envelope(mask, intervals):
    for interval in sorted(intervals, key=lambda pair: pair[1]):
        mask = fill(mask, interval)
    return mask


def check_unions(intervals):
    schedules = set(permutations(intervals))
    for initial in range(16):
        union = initial
        for schedule in schedules:
            mask = initial
            for interval in schedule:
                mask = fill(mask, interval)
            union |= mask
        assert union == sorted_envelope(initial, intervals)


def check_rank_bounds(tokens):
    expanded = [interval for interval, k in tokens for _ in range(k)]
    schedules = set(permutations(tokens))
    for initial in range(16):
        envelope = sorted_envelope(initial, expanded)
        for schedule in schedules:
            ranks = [range(1, k+1) for _, k in schedule]
            for choices in product(*ranks):
                mask = initial
                for (interval, _), rank in zip(schedule, choices):
                    mask = fill(mask, interval, rank)
                assert mask & ~envelope == 0


def consume(mask, row):
    for position in row:
        if not mask & (1 << position):
            return mask | (1 << position)
    return mask


def sweep(mask, order):
    for row in order:
        mask = consume(mask, row)
    return mask


def check_arbitrary_sweeps(rows):
    orders = set(permutations(rows))
    for initial in range(8):
        reached = initial
        for order in orders:
            reached |= sweep(initial, order)
        for order in orders:
            envelope = initial
            for _ in range(len(rows).bit_length()):
                envelope = sweep(envelope, order)
            assert reached & ~envelope == 0


def check_tree_delay(height):
    count = 1 << height
    nodes = {}
    cursor = 0
    for depth in range(height + 1):
        size = count >> min(height, depth + 1)
        for node in range(1 << depth):
            nodes[depth, node] = tuple(range(cursor, cursor + size))
            cursor += size
    rows = [tuple(position for depth in range(height + 1)
                  for position in nodes[depth, token >> (height-depth)])
            for token in range(count)]
    left_leaf = nodes[height, 0][0]
    occupied = 0
    for _ in range(height):
        occupied = sweep(occupied, rows)
        assert not occupied & (1 << left_leaf)
    assert sweep(occupied, rows) & (1 << left_leaf)


if __name__ == "__main__":
    windows = [(lo, hi) for lo in range(4) for hi in range(lo, 4)]
    interval_families = list(combinations_with_replacement(windows, 4))
    for intervals in interval_families:
        check_unions(intervals)
    ranked_tokens = [(window, k) for window in windows for k in (1, 2)]
    ranked_families = list(combinations_with_replacement(ranked_tokens, 3))
    for tokens in ranked_families:
        check_rank_bounds(tokens)
    print(f"{len(interval_families)} deadline-order families and "
          f"{len(ranked_families)} ranked families, with all 16 initial sets.")
    arbitrary = list(combinations_with_replacement(permutations(range(3)), 3))
    for rows in arbitrary:
        check_arbitrary_sweeps(rows)
    for height in range(1, 9):
        check_tree_delay(height)
    print(f"{len(arbitrary)} arbitrary-list families, every schedule and sweep "
          "order, and exact tree delays through height 8.")
