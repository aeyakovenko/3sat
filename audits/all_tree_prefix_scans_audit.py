"""Small exact checks for all-tree-prefix-scans.md; only the standard library is used."""

from functools import cache
from itertools import combinations, permutations, product
from random import Random


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            top = row.bit_length() - 1
            if top not in pivots:
                pivots[top] = row
                break
            row ^= pivots[top]
    return len(pivots)


def bits(mask):
    return [i for i in range(mask.bit_length()) if mask & (1 << i)]


def switches(order, left, right):
    labels = [bool(left & (1 << i)) for i in order if (left | right) & (1 << i)]
    return sum(a != b for a, b in zip(labels, labels[1:]))


def cross_rank(order, left, right):
    position = {item: index for index, item in enumerate(order)}
    a, b = bits(left), bits(right)
    ab = [sum(1 << j for j, v in enumerate(b) if position[u] < position[v]) for u in a]
    ba = [sum(1 << i for i, u in enumerate(a) if position[v] < position[u]) for v in b]
    return rank(ab) + rank(ba)


def split_cost(order, left, right):
    natural = range(len(order))
    bound = switches(natural, left, right) + switches(order, left, right)
    assert cross_rank(natural, left, right) + cross_rank(order, left, right) == bound
    return bound


def minimum_total(order):
    @cache
    def best(node):
        size = node.bit_count()
        if size == 1:
            return 0
        elements = bits(node)
        costs = []
        for rest in combinations(elements[1:], size // 2 - 1):
            left = (1 << elements[0]) + sum(1 << i for i in rest)
            right = node ^ left
            costs.append(split_cost(order, left, right) + best(left) + best(right))
        return min(costs)

    return best((1 << len(order)) - 1)


def record_merges(order, leaves):
    if len(leaves) == 1:
        return []
    middle = len(leaves) // 2
    left = set(leaves[:middle])
    directions = tuple(i not in left for i in order)
    return ([directions]
            + record_merges([i for i in order if i in left], leaves[:middle])
            + record_merges([i for i in order if i not in left], leaves[middle:]))


def decode_merges(records, leaf_positions):
    if len(leaf_positions) == 1:
        return list(leaf_positions)
    directions = next(records)
    mid = len(leaf_positions) // 2
    streams = [iter(decode_merges(records, leaf_positions[:mid])),
               iter(decode_merges(records, leaf_positions[mid:]))]
    return [next(streams[direction]) for direction in directions]


def check_orders():
    four = tuple(range(4))
    costs = []
    for p in permutations(four):
        costs.append(minimum_total(p))
        for tree in permutations(four):
            first = decode_merges(iter(record_merges(four, tree)), four)
            second = decode_merges(iter(record_merges(p, tree)), four)
            named = {leaf: label for label, leaf in enumerate(first)}
            assert tuple(named[leaf] for leaf in second) == p
    rng = Random(26011)
    costs_eight = [minimum_total(tuple(rng.sample(range(8), 8))) for _ in range(30)]
    print("Exact minimum summed cross ranks over all balanced trees:",
          f"n=4 all 24 orders {min(costs)}..{max(costs)};",
          f"n=8 for 30 seeded orders {min(costs_eight)}..{max(costs_eight)}.")


def scanned_mask(items, order):
    result = 0
    for which, sequence in enumerate((range(len(items)), order)):
        prefix = 0
        for i in sequence:
            prefix ^= items[i][2 * which]
            result ^= prefix & items[i][2 * which + 1]
    return result


def direct_mask(items, order):
    result = 0
    for which, sequence in enumerate((range(len(items)), order)):
        for j, v in enumerate(sequence):
            for u in sequence[:j + 1]:
                result ^= items[u][2 * which] & items[v][2 * which + 1]
    return result


def largest_zero_rectangle(order):
    inputs = list(product(range(2), repeat=4))
    zero_cols = [sum(1 << j for j, b in enumerate(inputs)
                     if scanned_mask((a, b), order) == 0)
                 for a in inputs]
    intersections = [(1 << len(inputs)) - 1]
    maximum = 0
    for subset in range(1, 1 << len(inputs)):
        low = subset & -subset
        common = intersections[subset ^ low] & zero_cols[low.bit_length() - 1]
        intersections.append(common)
        maximum = max(maximum, subset.bit_count() * common.bit_count())
    r = split_cost(order, 1, 2)
    assert maximum <= len(inputs) ** 2 >> r
    return maximum


def add_gate(clauses, last, a, b, operation):
    out = last + 1
    for first, second in product(range(2), repeat=2):
        good = operation(first, second)
        clauses.append((-a if first else a, -b if second else b, out if good else -out))
    return out


def physical_example(items, order):
    # Two groups with two offsets each. IDs 100,101,110,111 hold the four masks.
    mask_id = lambda value: 100 + 10 * (value & 1) + ((value >> 1) & 1)
    fixed = [tuple(-i if pattern & (1 << (i - 1)) else i for i in (1, 2, 3))
             for pattern in range(1, 8)]
    group, offset = 4, 5
    library = {mask_id(value) for value in range(4)}
    fixed.extend((-i, 1, 2) for i in range(6, 112) if i not in library)
    for value in range(4):
        for bit in range(2):
            literal = mask_id(value) if value & (1 << bit) else -mask_id(value)
            fixed.append((offset if bit == 0 else -offset, literal, 1))
    data = []
    for i, masks in enumerate(items):
        clauses = []
        for channel, payload in enumerate(masks):
            value = 112 + 4 * i + channel
            for grp in range(2):
                name = mask_id((payload >> (2 * grp)) & 3)
                guard = group if grp == 0 else -group
                clauses.extend(((guard, -value, name), (guard, value, -name)))
        data.append(clauses)

    last = 111 + 4 * len(items)
    finals = []
    for which, sequence in enumerate((range(len(items)), order)):
        prefix, accum = 1, 2    # Two forced-zero anchors.
        for i in sequence:
            x = 112 + 4 * i + 2 * which
            prefix = add_gate(fixed, last, prefix, x, lambda a, b: a ^ b)
            edge = add_gate(fixed, prefix, prefix, x + 1, lambda a, b: a & b)
            accum = add_gate(fixed, edge, accum, edge, lambda a, b: a ^ b)
            last = accum
        finals.append(accum)
    last = add_gate(fixed, last, *finals, lambda a, b: a ^ b)
    fixed.append((last, 1, 2))
    width = 512
    format_rows = lambda rows: "".join(f"{a} {b} {c} 0\n" for a, b, c in rows)
    prefix_text = (f"p cnf {last} {len(fixed) + sum(map(len, data))}\n"
                   + format_rows(fixed))
    prefix_text += " " * (-len(prefix_text) % width)
    packets = [format_rows(clauses) for clauses in data]
    assert all(len(packet) <= width for packet in packets)
    dimacs = prefix_text + "".join(packet.ljust(width) for packet in packets)
    rows = [tuple(map(int, line.split()[:-1])) for line in dimacs.splitlines()[1:]
            if line.strip()]
    assert len(rows) == len(fixed) + sum(map(len, data))
    assert all(len(row) == len(set(map(abs, row))) == 3 for row in rows)
    return rows, last


def forced_model(rows, variables, group, offset):
    env = {1: False, 2: False, 3: False, 4: bool(group), 5: bool(offset)}
    while True:
        assigned = len(env)
        for row in rows:
            missing = []
            for literal in row:
                ident = abs(literal)
                if ident not in env:
                    missing.append(literal)
                elif env[ident] == (literal > 0):
                    break
            else:
                if not missing:
                    return False
                if len(missing) == 1:
                    env[abs(missing[0])] = missing[0] > 0
        if len(env) == assigned:
            assert len(env) == variables
            return True


def check_inputs():
    for order in ((0, 1), (1, 0)):
        for numbers in product(range(4), repeat=8):
            items = (numbers[:4], numbers[4:])
            assert scanned_mask(items, order) == direct_mask(items, order)
        print(f"n=2, order {order}, largest one-lane rejecting rectangle:",
              largest_zero_rectangle(order), "of 256 inputs")

    rng = Random(5982)
    checked = 0
    for size in (2, 4):
        for _ in range(30):
            items = [rng.choices(range(16), k=4) for _ in range(size)]
            order = rng.sample(range(size), size)
            rows, variables = physical_example(items, order)
            expected = direct_mask(items, order)
            for lane in range(4):
                assert forced_model(rows, variables, lane // 2, lane % 2) == bool(
                    expected & (1 << lane)
                )
                checked += 1
    print("Verified 131,072 packed scans and", checked, "DIMACS lane choices.")


if __name__ == "__main__":
    check_orders()
    check_inputs()
