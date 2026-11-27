"""Verify the bounded-reread branching programs for three addressed tables."""

from functools import cache
from itertools import product


def build_program(width, repeats):
    """Use exactly the high 'repeats' bits of i as the allowed repeat set."""
    side = 1 << width
    low_width = width - repeats
    nodes = [None, None]  # Reject and accept sinks.
    unique = {}

    def test(bit, negative, positive):
        if negative == positive:
            return positive
        key = (bit, negative, positive)
        if key not in unique:
            unique[key] = len(nodes)
            nodes.append(key)
        return unique[key]

    def select(bank, bits, finish, prefix=0):
        if not bits:
            return finish(prefix)
        position, *rest = bits
        left = select(bank, rest, finish, 2 * prefix)
        right = select(bank, rest, finish, 2 * prefix + 1)
        return test((bank, position), left, right)

    full = tuple(reversed(range(width)))
    low = tuple(reversed(range(low_width)))
    high = tuple(bit for bit in full if bit >= low_width)

    @cache
    def final_lookup(i_low, j):
        def finish(i_high):
            i = (i_high << low_width) | i_low
            return test(("Z", j * side + i), 0, 1)

        return select("i", high, finish)

    @cache
    def middle_lookup(i_low, k):
        def finish(j):
            return test(("B", k * side + j), 0, final_lookup(i_low, j))

        return select("j", full, finish)

    def initial_lookup(i_low, k):
        def finish(i_high):
            i = (i_high << low_width) | i_low
            return test(("A", i * side + k), 0, middle_lookup(i_low, k))

        return select("i", high, finish)

    def read_k(i_low):
        return select("k", full, lambda k: initial_lookup(i_low, k))

    return nodes, select("i", low, read_k)


def check_all_path_restrictions(nodes, root, width, repeats):
    """Use suffix unions, checking all syntactic paths without enumerating them."""
    allowed = {("i", bit) for bit in range(width - repeats, width)}
    future = [set(), set()]
    repeatable = [set(), set()]
    for bit, left, right in nodes[2:]:
        later = future[left] | future[right]
        doubled = repeatable[left] | repeatable[right]
        if bit in later:
            assert bit in allowed
            assert bit not in doubled  # At most two tests on every path.
            doubled.add(bit)
        future.append(later | {bit})
        repeatable.append(doubled)
    side = 1 << width
    assert len(future[root]) == 3 * (side * side + width)
    assert repeatable[root] == allowed


def evaluate(nodes, root, assignment):
    node = root
    while node >= 2:
        (bank, bit), left, right = nodes[node]
        node = right if (assignment[bank] >> bit) & 1 else left
    return node


def test_program(width, repeats):
    nodes, root = build_program(width, repeats)
    check_all_path_restrictions(nodes, root, width, repeats)
    side = 1 << width
    assert len(nodes) <= 12 * (side**2 + side**3 // (1 << repeats))
    checks = 0
    for i, k, j in product(range(side), repeat=3):
        target = (i * side + k, k * side + j, j * side + i)
        if width == 1:
            arrays = product(range(1 << (side * side)), repeat=3)
        else:
            # For each selected edge, toggle its bit against both constant backgrounds.
            arrays = (
                tuple(background ^ (toggle << edge) for toggle, edge in zip(toggles, target))
                for background in (0, (1 << (side * side)) - 1)
                for toggles in product((0, 1), repeat=3)
            )
        for a, b, z in arrays:
            assignment = dict(i=i, k=k, j=j, A=a, B=b, Z=z)
            expected = all((data >> edge) & 1 for data, edge in zip((a, b, z), target))
            assert evaluate(nodes, root, assignment) == expected
            checks += 1
    return len(nodes), checks


def check_triangle_matchings(side):
    """Each edge's complementary pairs are a matching, and two edges determine a triangle."""
    incident = {}
    extension = {}
    for i, k, j in product(range(side), repeat=3):
        triple = (("A", i, k), ("B", k, j), ("Z", j, i))
        for position, edge in enumerate(triple):
            a, b = triple[(position + 1) % 3], triple[(position + 2) % 3]
            seen = incident.setdefault(edge, set())
            assert a not in seen and b not in seen
            seen.update((a, b))
            pair = frozenset((a, b))
            assert pair not in extension
            extension[pair] = edge
    assert len(incident) == 3 * side**2
    assert len(extension) == 3 * side**3


if __name__ == "__main__":
    checks = 0
    for width in range(1, 5):
        check_triangle_matchings(1 << width)
        sizes = []
        for repeats in range(width + 1):
            size, tests = test_program(width, repeats)
            sizes.append(size)
            checks += tests
        print(f"d={1 << width}, nodes including sinks in increasing repeat budget: {sizes}")
    print(f"Checked {checks:,} verdicts and every DAG's syntactic repeat sets.")
