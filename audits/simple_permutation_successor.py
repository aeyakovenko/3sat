"""A 3-colorability-preserving map from two paths to a simple permutation."""

from collections import Counter
from itertools import permutations


def valid_order(order):
    seen = bytearray(len(order))
    for value in order:
        if not 0 <= value < len(order) or seen[value]:
            return False
        seen[value] = 1
    return True


def successor(order):
    """The red order is implicit. Return blue vertex IDs in their blue order."""
    if not valid_order(order):
        raise ValueError("expected a permutation of range(len(order))")
    n = len(order)
    padding = 2 + n % 2
    cycle = list(order) + list(range(n, n + padding))
    size = len(cycle)
    x, y = 0, 7 * size + 1

    # Red order within vertex i: s,a,b,m,c,d,t at offsets 0,...,6.
    # The even cycle alternately uses terminal s (spare b) and t (spare c).
    low = []
    for j, left in enumerate(cycle):
        right = cycle[(j + 1) % size]
        terminal, spare = (0, 2) if j % 2 == 0 else (6, 4)
        start, end = 1 + 7 * left, 1 + 7 * right
        low.extend((start + spare, start + terminal, end + terminal, end + spare))

    # Both orders work. The choice records how many padding vertices to remove.
    high = []
    vertices = range(size) if padding == 2 else reversed(range(size))
    for vertex in vertices:
        start = 1 + 7 * vertex
        high.extend((start + 1, start + 3, start + 5))
    return tuple(low + [x, y] + high)


def predecessor(order):
    """Recognize a rendered successor and recover its input, without a history."""
    size, remainder = divmod(len(order) - 2, 7)
    if remainder or size < 2 or size % 2:
        return None
    high = order[4 * size + 2:]
    padding = 2 if high[0] == 2 else 3
    if padding > size:
        return None
    cycle = [(order[4 * i + 1] - 1) // 7 for i in range(size)]
    old = tuple(cycle[:size - padding])
    if valid_order(old) and successor(old) == tuple(order):
        return old
    return None


def simple(order):
    """Independent quadratic test used only for the small census."""
    for start, first in enumerate(order):
        least = greatest = first
        for end in range(start + 1, len(order)):
            least = min(least, order[end])
            greatest = max(greatest, order[end])
            if greatest - least == end - start and end - start + 1 < len(order):
                return False
    return True


def red_coloring_masks(n):
    """Use bitsets for the colorings of the identity path modulo its first edge."""
    colorings = [(0,)]
    for _ in range(n - 1):
        colorings = [row + (v,) for row in colorings for v in range(3) if row[-1] != v]
    if n > 1:
        colorings = [row for row in colorings if row[1] == 1]
    masks = {(i, j): sum(1 << k for k, row in enumerate(colorings) if row[i] != row[j])
             for i in range(n) for j in range(n)}
    return (1 << len(colorings)) - 1, masks


def census(n):
    all_colors, masks = red_coloring_masks(n)
    counts = Counter()
    for order in permutations(range(n)):
        if simple(order):
            colors = all_colors
            for edge in zip(order, order[1:]):
                colors &= masks[edge]
            counts[bool(colors)] += 1
    return counts[True], counts[False]


def simple_negative_extensions(order, all_colors, masks):
    """Insert a fresh entry at each red and blue position, preserving old orders."""
    count = 0
    for value in range(len(order) + 1):
        shifted = tuple(x + (x >= value) for x in order)
        for pos in range(len(order) + 1):
            trial = shifted[:pos] + (value,) + shifted[pos:]
            if simple(trial):
                colors = all_colors
                for edge in zip(trial, trial[1:]):
                    colors &= masks[edge]
                count += not colors
    return count


def coloring_dimacs(order):
    """Fixed fields keep distinct permutation entries in distinct literal slots."""
    size = len(order)
    pin = 3 * size + 1
    width = 1 + len(str(pin))
    pos = [str(i).rjust(width) for i in range(pin + 1)]
    neg = [str(-i).rjust(width) for i in range(pin + 1)]
    lines = [f"p cnf {pin} {size + 12 * max(0, size - 1)}"]
    for i in range(size):
        lines.append(" ".join(pos[3 * i + c] for c in (1, 2, 3)) + " 0")
    for path in (range(size), order):
        for a, b in zip(path, path[1:]):
            for c in (1, 2, 3):
                pair = neg[3 * a + c] + " " + neg[3 * b + c] + " "
                lines.extend((pair + pos[pin] + " 0", pair + neg[pin] + " 0"))
    return ("\n".join(lines) + "\n").encode("ascii")


def switch_positions_audit():
    from two_hamilton_paths_sat_audit import switchable_edges, switched_order

    for rim in (3, 5, 7):
        edges = [(i, (i + 1) % rim) for i in range(rim)] + [(i, rim) for i in range(rim)]
        encoding, switches = switchable_edges(rim + 1, edges)
        old = encoding.permutation()
        baseline = successor(old)
        padded = (len(baseline) - 2) // 7
        assert len(baseline) == 1141 * rim + 121
        used = set()
        used_bytes = set()
        if rim == 3:
            baseline_file = coloring_dimacs(baseline)
        for j, positions in enumerate(switches):
            changed = successor(switched_order(old, switches, [j]))
            affected = {k for k, (a, b) in enumerate(zip(baseline, changed)) if a != b}
            expected = set()
            for pos in positions:
                previous = (pos - 1) % padded
                expected.update((4 * pos, 4 * pos + 1, 4 * previous + 2, 4 * previous + 3))
            assert affected == expected and len(affected) == 8 and used.isdisjoint(affected)
            used.update(affected)
            if rim == 3:
                changed_file = coloring_dimacs(changed)
                assert len(changed_file) == len(baseline_file)
                edits = {j for j, (a, b) in enumerate(zip(baseline_file, changed_file)) if a != b}
                assert edits and used_bytes.isdisjoint(edits)
                used_bytes.update(edits)


def audit():
    expected = [(1, 0), (2, 0), (0, 0), (0, 2), (6, 0), (46, 0),
                (266, 72), (2694, 232)]
    for n, known in enumerate(expected, start=1):
        assert census(n) == known
        print(f"{n} entries: {known[0]} colorable simple orders, {known[1]} uncolorable")
    seed = (1, 3, 5, 2, 6, 0, 4)
    assert simple_negative_extensions(seed, *red_coloring_masks(8)) == 0
    for n in range(7):
        for order in permutations(range(n)):
            new = successor(order)
            assert valid_order(new) and simple(new) and predecessor(new) == order
            assert all(abs(i - j) != 1 for i, j in zip(new, new[1:]))
    switch_positions_audit()
    print("Disjoint switch positions pass on the three-, five- and seven-rim wheels.")
    print("Successor simplicity, edge disjointness and decoding pass through six entries.")


if __name__ == "__main__":
    audit()
