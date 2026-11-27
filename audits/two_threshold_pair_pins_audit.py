"""Check majority-closed two-pin relations and the two-threshold extremal example."""

from itertools import combinations, product
from math import comb
from random import Random


def pin_cubes(v):
    return [
        sum(1 << x for x in range(1 << v)
            if ((x >> i) & 1, (x >> j) & 1) == values)
        for i, j in combinations(range(v), 2)
        for values in product(range(2), repeat=2)
    ]


def words(relation):
    while relation:
        least = relation & -relation
        yield least.bit_length() - 1
        relation ^= least


def inspect_relation(relation, v, cubes):
    """Return whether it is a 2-CNF and whether each word is privately pinned."""
    full = (1 << (1 << v)) - 1
    possible = full
    isolated = 0
    for cube in cubes:
        hit = relation & cube
        if not hit:
            possible &= ~cube
        elif hit & (hit - 1) == 0:
            isolated |= hit
    return possible == relation, isolated == relation


def check_graph(relation, v):
    points = list(words(relation))
    adjacency = {x: set() for x in points}
    for x, y in combinations(points, 2):
        if not any(z != x and z != y and not ((x ^ z) & (y ^ z)) for z in points):
            adjacency[x].add(y)
            adjacency[y].add(x)
    if not points:
        return
    assert max(map(len, adjacency.values())) <= 2
    endpoints = [x for x in points if len(adjacency[x]) < 2]
    if not endpoints:
        assert len(points) == 4
        return
    previous = None
    current = endpoints[0]
    changed = 0
    visited = 1
    while choices := adjacency[current] - {previous}:
        assert len(choices) == 1
        following = next(iter(choices))
        bundle = current ^ following
        assert bundle & changed == 0
        changed |= bundle
        previous, current = current, following
        visited += 1
    assert visited == len(points) <= v + 1
    if len(points) == v + 1:
        assert changed == (1 << v) - 1


def all_small_relations():
    closed = certifiable = 0
    for v in (2, 3, 4):
        cubes = pin_cubes(v)
        for relation in range(1 << (1 << v)):
            is_closed, is_isolated = inspect_relation(relation, v, cubes)
            points = list(words(relation))
            is_majority_closed = all(
                relation & (1 << ((x & y) | (x & z) | (y & z)))
                for x, y, z in combinations(points, 3)
            )
            assert is_closed == is_majority_closed
            if is_closed:
                closed += 1
                if is_isolated:
                    check_graph(relation, v)
                    certifiable += 1
    return closed, certifiable


def larger_examples():
    rng = Random(194321)
    tested = 0
    for v in range(5, 10):
        cubes = pin_cubes(v)
        full = (1 << (1 << v)) - 1
        for _ in range(60):
            relation = full
            for cube in rng.sample(cubes, rng.randint(v, 4*v)):
                relation &= ~cube
            is_closed, is_isolated = inspect_relation(relation, v, cubes)
            assert is_closed
            if is_isolated:
                check_graph(relation, v)
                tested += 1

        # Translate and permute a full chain; the complement is exactly
        # the union of its adjacent inversions, with a private word for each.
        order = list(range(v))
        rng.shuffle(order)
        origin = rng.randrange(1 << v)
        x = origin
        chain = 1 << x
        for i in order:
            x ^= 1 << i
            chain |= 1 << x
        check_graph(chain, v)
        adjacent = [
            sum(1 << y for y in range(1 << v)
                if not ((y ^ origin) >> i & 1) and (y ^ origin) >> j & 1)
            for i, j in zip(order, order[1:])
        ]
        union = 0
        for cube in adjacent:
            union |= cube
        assert union == full ^ chain
        for i, cube in enumerate(adjacent):
            private = cube
            for j, other in enumerate(adjacent):
                if j != i:
                    private &= ~other
            assert private

        # Check both physical weight thresholds and all the forcing pins.
        singles = {1 << i for i in range(v)}
        pairs = {(1 << i) | (1 << j) for i, j in combinations(range(v), 2)}
        for active, queries in [({0} | singles | pairs, pairs),
                                ({0} | singles, singles)]:
            for mask in queries:
                assert [x for x in active if x & mask == mask] == [mask]
        assert len(singles | pairs) == comb(v, 2) + v
    for v in range(9, 400):
        assert (v + 1) * (comb(v, 2) + 1) < 2**v
    return tested


def irredundant_clause_checks():
    """Trim actual 2-CNF definitions of paths and squares in random orders."""
    rng = Random(3809)
    tests = 0
    for v in range(3, 10):
        full = (1 << (1 << v)) - 1
        cubes = pin_cubes(v)
        for trial in range(100):
            order = list(range(v))
            rng.shuffle(order)
            count = rng.randint(0, v)
            dynamic = order[:count]
            origin = rng.randrange(1 << v)
            points = {origin}
            if trial % 2 and count >= 2:
                split = rng.randrange(1, count)
                left = sum(1 << i for i in dynamic[:split])
                right = sum(1 << i for i in dynamic[split:])
                points.update((origin ^ left, origin ^ right, origin ^ left ^ right))
            else:
                x = origin
                for j, i in enumerate(dynamic):
                    x ^= 1 << i
                    if j == len(dynamic) - 1 or rng.randrange(2):
                        points.add(x)
            relation = sum(1 << x for x in points)
            definition = [cube for cube in cubes if not relation & cube]
            rng.shuffle(definition)
            for candidate in definition.copy():
                remaining = 0
                for cube in definition:
                    if cube != candidate:
                        remaining |= cube
                if remaining == full ^ relation:
                    definition.remove(candidate)
            union = 0
            for cube in definition:
                union |= cube
            assert union == full ^ relation
            assert len(definition) + len(points) <= 2*v
            tests += 1
    return tests


if __name__ == "__main__":
    closed, private = all_small_relations()
    print(f"{closed} majority-closed relations through dimension four; "
          f"{private} have two-pin certificates for every word")
    print(f"{larger_examples()} larger two-pin relations; "
          "chain inversions and both forcing thresholds checked through dimension nine")
    print(f"{irredundant_clause_checks()} irredundant 2-CNF clause bounds "
          "on paths, squares and singletons")
