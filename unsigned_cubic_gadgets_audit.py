"""Enumerate simple trivalent Boolean gadgets with E or any tap position of R."""

from collections import Counter, defaultdict
from itertools import combinations, product

# A mode 0, 1 or 2 designates the R tap; mode 3 means exact-one.
# The first wire labels are boundary ports. Each other wire is an internal edge.
TRIANGLE = [(0, 3, 5), (1, 4, 3), (2, 5, 4)]
DIAMOND = [(0, 2, 3), (1, 4, 5), (2, 4, 6), (3, 5, 6)]
PARITY = [(3, 4, 5), (6, 7, 8), (0, 3, 6), (1, 4, 7), (2, 5, 8)]
CUBE_CORNER = [(3, 4, 5), (0, 3, 6), (6, 7, 8), (1, 7, 9),
               (9, 10, 11), (2, 4, 10), (5, 8, 11)]
UNARY = [(0, 1, 2), (1, 3, 4), (2, 5, 6), (3, 5, 7), (4, 6, 7)]


def allowed(mode, values):
    if mode == 3:
        return sum(values) == 1
    a, b = values[(mode+1) % 3], values[(mode+2) % 3]
    return a == b and values[mode] <= a


def validate(ports, boundary):
    ends = defaultdict(list)
    for vertex, triple in enumerate(ports):
        assert len(triple) == len(set(triple)) == 3
        for wire in triple:
            ends[wire].append(vertex)
    assert set(ends) == set(range(len(ends)))
    assert all(len(ends[j]) == (1 if j < boundary else 2) for j in ends)
    pairs = [tuple(vs) for vs in ends.values() if len(vs) == 2]
    assert len(set(pairs)) == len(pairs)
    seen = {0}
    for _ in ports:
        seen.update(u for pair in pairs if seen.intersection(pair) for u in pair)
    assert len(seen) == len(ports)
    return len(ends)


def census(ports, boundary):
    wires = validate(ports, boundary)
    assignments = tuple(product(range(2), repeat=wires))
    boundary_masks = [sum(1 << i for i, row in enumerate(assignments) if row[:boundary] == bits)
                      for bits in product(range(2), repeat=boundary)]
    vertex_masks = [[sum(1 << i for i, row in enumerate(assignments)
                         if allowed(mode, tuple(row[j] for j in triple)))
                     for mode in range(4)] for triple in ports]
    result = Counter()
    by_modes = {}
    for modes in product(range(4), repeat=len(ports)):
        rows = (1 << len(assignments))-1
        for masks, mode in zip(vertex_masks, modes):
            rows &= masks[mode]
        signature = tuple((rows & mask).bit_count() for mask in boundary_masks)
        result[signature] += 1
        by_modes[modes] = signature
    return result, by_modes


def signature(ports, modes, boundary):
    """Independent local-word traversal; returns the number of full completions per boundary."""
    wires = validate(ports, boundary)
    counts = Counter()
    choices = [[vals for vals in product(range(2), repeat=3) if allowed(mode, vals)]
               for mode in modes]

    def extend(i, assigned):
        if i == len(ports):
            assert len(assigned) == wires
            counts[tuple(assigned[j] for j in range(boundary))] += 1
            return
        for values in choices[i]:
            local = dict(zip(ports[i], values))
            if all(assigned.get(wire, bit) == bit for wire, bit in local.items()):
                extend(i+1, assigned | local)

    extend(0, {})
    return tuple(counts[x] for x in product(range(2), repeat=boundary))


def topologies(vertices, boundary):
    """Count labeled internal simple graphs with exactly the required number of half-edges."""
    edges = list(combinations(range(vertices), 2))
    if (3*vertices-boundary) < 0 or (3*vertices-boundary) % 2:
        return 0
    count = 0
    for subset in combinations(edges, (3*vertices-boundary)//2):
        degree = Counter(v for edge in subset for v in edge)
        if all(degree[v] <= 3 for v in range(vertices)):
            count += 1
    return count


if __name__ == '__main__':
    # In any simple gadget the deficient vertices determine where the ports are.
    assert [topologies(v, 3) for v in range(4)] == [0, 1, 0, 1]
    assert [topologies(v, 2) for v in range(5)] == [0, 0, 0, 0, 6]
    assert [topologies(v, 1) for v in range(6)] == [0, 0, 0, 0, 0, 30]
    copy = (1, 0, 0, 0, 0, 0, 0, 1)
    negation, implication = (0, 1, 1, 0), (1, 1, 0, 1)
    assert all(signature([(0, 1, 2)], (mode,), 3) != copy for mode in range(4))
    triangle_counts, triangles = census(TRIANGLE, 3)
    diamond_counts, diamonds = census(DIAMOND, 2)
    unary_counts, unary = census(UNARY, 1)
    parity_counts, parity_modes = census(PARITY, 3)
    even = (1, 0, 0, 1, 0, 1, 1, 0)
    for ports, modes, boundary, target, table in [
        (TRIANGLE, (2, 2, 2), 3, copy, triangles),
        (PARITY, (0, 3, 3, 3, 3), 3, even, parity_modes),
        (DIAMOND, (1, 1, 0, 3), 2, negation, diamonds),
        (DIAMOND, (0, 1, 0, 1), 2, implication, diamonds),
        (UNARY, (1, 1, 0, 1, 0), 1, (1, 1), unary),
        (UNARY, (0, 0, 3, 0, 1), 1, (1, 0), unary),
        (UNARY, (1, 0, 1, 0, 3), 1, (0, 1), unary),
    ]:
        assert signature(ports, modes, boundary) == table[modes] == target

    # Restoring boundary vertex 7 literally gives the three-dimensional cube:
    # each edge toggles one coordinate in this binary labeling of the vertices.
    restored = CUBE_CORNER + [(0, 1, 2)]
    cube_labels = (0, 1, 3, 7, 6, 4, 2, 5)
    for wire in range(12):
        u, v = (j for j, triple in enumerate(restored) if wire in triple)
        assert (cube_labels[u] ^ cube_labels[v]).bit_count() == 1
    patterns = tuple(product(range(2), repeat=3))
    for modes, predicate in [
        ((0, 3, 0, 1, 3, 2, 3), lambda x, y, z: x or y or z),
        ((0, 3, 1, 3, 1, 3, 3), lambda x, y, z: x != y or y != z),
        ((0, 3, 1, 3, 2, 3, 2), lambda x, y, z: z == x*y),
        ((0, 3, 3, 3, 3, 1, 0), lambda x, y, z: z == x^y),
    ]:
        assert signature(CUBE_CORNER, modes, 3) == tuple(int(predicate(*v)) for v in patterns)

    # Assemble the proposed 9-vertex pin from its primitive E/R vertices.
    # Triangle external wires 1,2 meet an E and wire 6 goes to the terminator.
    wired = TRIANGLE + [(1, 2, 6)]
    wired += [tuple(6 + wire for wire in triple) for triple in UNARY]
    modes = (2, 2, 2, 3, 1, 1, 0, 1, 0)
    assert signature(wired, modes, 1) == (1, 0)
    # Supply this pin as the third input to E, exposing two new boundary ports.
    not_wired = [(0, 1, 2)] + [tuple(wire+2 for wire in triple) for triple in wired]
    assert signature(not_wired, (3,) + modes, 2) == negation
    print('triangle modes yielding COPY:', triangle_counts[copy], '/ 64')
    print('diamond modes yielding NOT, implication:', diamond_counts[negation],
          diamond_counts[implication], '/ 256')
    print('subdivided K4 modes yielding free, zero, one:', unary_counts[(1, 1)],
          unary_counts[(1, 0)], unary_counts[(0, 1)], '/ 1024')
    print('K2,3 modes yielding even parity:', parity_counts[even], '/ 1024')
    print('cube missing one corner: parsimonious OR, NAE, AND, XOR')
    print('composed primitive graphs: 9-vertex zero pin; 10-vertex NOT')
