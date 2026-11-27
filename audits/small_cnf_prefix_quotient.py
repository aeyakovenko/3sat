"""Exact semantic prefix states of proper 3-CNF, with a slice count for five variables."""

from collections import Counter
from itertools import combinations, permutations


def faces(v, width):
    """Each clause forbids the assignments agreeing with a pattern on its variables."""
    result = []
    for support in combinations(range(v), width):
        for signs in range(1 << width):
            mask = 0
            for x in range(1 << v):
                if all((x >> i & 1) == (signs >> j & 1) for j, i in enumerate(support)):
                    mask |= 1 << x
            result.append(mask)
    return result


def interiors(cubes, v):
    result = []
    for state in range(1 << (1 << v)):
        covered = 0
        for face in cubes:
            if state & face == face:
                covered |= face
        result.append(covered)
    return result


def breadth_first(cubes):
    layer, visited, histogram = {0}, set(), []
    while layer:
        histogram.append(len(layer))
        visited.update(layer)
        layer = {s | f for s in layer for f in cubes} - visited
    return sorted(visited), histogram


def suffix_profile(states, cubes, v):
    full = (1 << (1 << v)) - 1
    index = {s: i for i, s in enumerate(states)}
    rows = [tuple(index[s | f] for f in cubes) for s in states]
    classes = [int(s == full) for s in states]
    counts = [len(set(classes))]
    while counts[-1] < len(states):
        names = {}
        refined = []
        for i, row in enumerate(rows):
            key = (classes[i], *(classes[j] for j in row))
            refined.append(names.setdefault(key, len(names)))
        assert len(names) > counts[-1]
        counts.append(len(names))
        classes = refined
    return counts


def edge_cover_histogram():
    """Independent shortest-prefix count via maximum matchings of induced Q4 subgraphs."""
    vertices = range(16)
    adjacent = [sum(1 << (v ^ (1 << j)) for j in range(4)) for v in vertices]
    matching = [0] * (1 << 16)
    lengths = Counter({0: 1})
    for state in range(1, 1 << 16):
        first = state & -state
        v = first.bit_length() - 1
        rest = state ^ first
        possible = rest & adjacent[v]
        best = matching[rest]
        while possible:
            mate = possible & -possible
            best = max(best, 1 + matching[rest ^ mate])
            possible ^= mate
        matching[state] = best
        if all(state & adjacent[u] for u in vertices if state & (1 << u)):
            lengths[state.bit_count() - best] += 1
    return [lengths[j] for j in range(max(lengths) + 1)]


def symmetry_classes(states, v):
    """Signed coordinate permutations. Split the bit permutation into two table lookups."""
    half = 1 << (v - 1)
    table_size = 1 << half
    transforms = []
    for perm in permutations(range(v)):
        permuted = [sum((x >> j & 1) << perm[j] for j in range(v)) for x in range(1 << v)]
        for signs in range(1 << v):
            bit = [1 << (x ^ signs) for x in permuted]
            lo, hi = [0] * table_size, [0] * table_size
            for s in range(1, table_size):
                pos = (s & -s).bit_length() - 1
                lo[s] = lo[s & (s - 1)] | bit[pos]
                hi[s] = hi[s & (s - 1)] | bit[half + pos]
            transforms.append((lo, hi))

    seen, representatives = set(), {}
    for state in states:
        if state not in seen:
            orbit = {lo[state & (table_size - 1)] | hi[state >> half] for lo, hi in transforms}
            assert not seen.intersection(orbit)
            seen.update(orbit)
            representatives[state] = len(orbit)
    assert seen == set(states)
    return representatives


def lift(v, states, reps, core3):
    core2 = interiors(faces(v, 2), v)
    residual = {s: s ^ core2[s] for s in states}
    counts = Counter()
    for u, multiplicity in reps.items():
        missing_u = residual[u]
        weight_u = u.bit_count()
        for other in states:
            required = missing_u | residual[other]
            if required & ~core3[u & other] == 0:
                counts[weight_u + other.bit_count()] += multiplicity
    two_states = sum(core2[s] == s for s in states)
    return counts, two_states**2


def main():
    for v, expected in [(3, 256), (4, 43146)]:
        clauses = faces(v, 3)
        states, depth = breadth_first(clauses)
        core3 = interiors(clauses, v)
        assert states == [s for s, interior in enumerate(core3) if s == interior]
        assert len(states) == expected
        if v == 4:
            assert depth == edge_cover_histogram()
        print(f"v={v}, clauses {len(clauses)}, states {len(states)}, shortest prefixes {depth}")
        print("suffix classes", suffix_profile(states, clauses, v))
        reps = symmetry_classes(states, v)
        counts, fresh_only = lift(v, states, reps, core3)
        if v == 3:
            direct, _ = breadth_first(faces(4, 3))
            assert counts == Counter(s.bit_count() for s in direct)
        print(f"{len(reps)} symmetry classes; v={v+1} states {sum(counts.values())}, "
              f"with a representation using only clauses on the new variable {fresh_only}")
        print("counts by number of forbidden assignments",
              [counts[j] for j in range((1 << (v + 1)) + 1)])


if __name__ == "__main__":
    main()
