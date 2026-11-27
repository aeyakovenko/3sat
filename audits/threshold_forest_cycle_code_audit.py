"""Compare rank, cycle-code projections and disjoint support packing in all short chains."""
from functools import lru_cache
from itertools import combinations, product


def edge_slots(types):
    # Fixed public slots: the spanning path, followed by three chords per block.
    tree = [(i, i+1) for i in range(7*len(types)-1)]
    chords = []
    for block, kind in enumerate(types):
        start = 7*block
        local = ((0, 2), (2, 4), (4, 6)) if kind == 'A' else ((0, 4), (2, 4), (2, 6))
        chords.extend((start+u, start+v) for u, v in local)
    return tree + chords, len(tree)


def prefix_partitions(order, edges):
    classes = list(range(order))
    partitions = [tuple(classes)]
    ranks = [0]
    for u, v in edges:
        old, new = max(classes[u], classes[v]), min(classes[u], classes[v])
        classes = [new if label == old else label for label in classes]
        partitions.append(tuple(classes))
        ranks.append(order - len(set(classes)))
    return partitions, ranks


def even_supports(edges):
    # Gray walk over *all* edge subsets; toggling an edge flips its two endpoints.
    endpoints = [(1 << u) | (1 << v) for u, v in edges]
    code = [0]
    odd_vertices = 0
    for step in range(1, 1 << len(edges)):
        changed = (step & -step).bit_length() - 1
        odd_vertices ^= endpoints[changed]
        if odd_vertices == 0:
            code.append(step ^ (step >> 1))
    return code


def from_chords(edges, tree_count):
    # Given all chord bits, the vertex-parity equation at the left end of
    # each remaining path edge forces that edge. Check the last endpoint too.
    code = []
    for bits in range(1 << (len(edges)-tree_count)):
        mask = bits << tree_count
        odd = 0
        for j, (u,v) in enumerate(edges[tree_count:]):
            if bits & (1 << j):
                odd ^= (1 << u) | (1 << v)
        for j, (u,v) in enumerate(edges[:tree_count]):
            assert (u,v) == (j,j+1)
            if odd & (1 << u):
                mask |= 1 << j
                odd ^= (1 << u) | (1 << v)
        assert odd == 0
        code.append(mask)
    return code


def simple_cycle(mask, edges):
    adjacency = {}
    for i, (u, v) in enumerate(edges):
        if mask & (1 << i):
            adjacency.setdefault(u, []).append(v)
            adjacency.setdefault(v, []).append(u)
    if not adjacency or any(len(neighbors) != 2 for neighbors in adjacency.values()):
        return False
    reached = set()
    todo = [next(iter(adjacency))]
    while todo:
        u = todo.pop()
        if u not in reached:
            reached.add(u)
            todo.extend(adjacency[u])
    return len(reached) == len(adjacency)


def packing(supports):
    @lru_cache(maxsize=None)
    def best(used):
        return max((1 + best(used | s) for s in supports if not (used & s)), default=0)
    return best(0)


def one_block_cover(code, width):
    # For each proposed piece intersect every binary constraint satisfied by
    # that piece, then test all ambient assignments for extraneous models.
    # Unary pins are also determined by binary projections when width >= 2.
    pairs = list(combinations(range(width), 2))
    pieces = []
    for mask in range(1, 1 << len(code)):
        selected = {word for i, word in enumerate(code) if mask & (1 << i)}
        projections = [{(word >> i & 1, word >> j & 1) for word in selected}
                       for i, j in pairs]
        models = {word for word in range(1 << width)
                  if all((word >> i & 1, word >> j & 1) in allowed
                         for (i,j), allowed in zip(pairs, projections))}
        if models == selected:
            pieces.append(mask)
    full = (1 << len(code)) - 1
    reachable = {0}
    for count in range(1, len(code)+1):
        reachable = {covered | new for covered in reachable for new in pieces}
        if full in reachable:
            return count, max(mask.bit_count() for mask in pieces)
    raise AssertionError('individual assignments always give a cover')


def one_block_encoding(kind, code):
    # Variables 1..6 are path edges, 7..9 are the three chords.
    # B uses one auxiliary bit z=10 to change the central chord by an XOR.
    clauses = []

    def equal(a, b):
        clauses.extend([(-a, b), (a, -b)])

    def xor(a, b, output):
        for x, y in product((0, 1), repeat=2):
            bad = (x, y, 1 ^ x ^ y)
            clauses.append(tuple(-v if value else v for v, value in zip((a, b, output), bad)))

    for a, b in [(1,2), (3,4), (5,6), (1,7), (5,9)]:
        equal(a, b)
    if kind == 'A':
        equal(3, 8)
    else:
        xor(1, 5, 10)
        xor(3, 10, 8)
    assert all(len(c) <= 2 or (kind == 'B' and 10 in map(abs,c)) for c in clauses)

    def holds(bits):
        return all(any(((bits >> (abs(lit)-1)) & 1) == (lit > 0) for lit in clause)
                   for clause in clauses)

    projected = {bits & 511 for bits in range(1 << (9 if kind == 'A' else 10)) if holds(bits)}
    assert projected == set(code)


def main():
    for g in (1, 2, 3):
        reference = None
        projection_reference = None
        degree_reference = None
        maxima = {}
        for types in product('AB', repeat=g):
            n = 7*g
            edges, tree_count = edge_slots(types)
            assert tree_count == n-1 and len(edges) == 10*g-1
            profile = prefix_partitions(n, edges)
            if reference is None:
                reference = profile
            assert profile == reference
            parts, ranks = profile
            assert ranks == [min(i, n-1) for i in range(len(edges)+1)]
            assert len(set(parts[tree_count])) == 1
            # The n-1 zero-weight edges form a tree: this is the only
            # spanning tree of weight zero, whereas any other uses a chord.
            degrees = tuple(sum(v in edge for edge in edges) for v in range(n))
            if degree_reference is None:
                degree_reference = degrees
            assert degree_reference == degrees
            code = from_chords(edges, tree_count)
            if g <= 2:
                assert set(code) == set(even_supports(edges))
            assert len(code) == 1 << (3*g)
            packing_number = 3*g - types.count('B')
            assert packing(code[1:]) == packing_number
            assert packing([x for x in code if simple_cycle(x, edges)]) == packing_number
            maxima[''.join(types)] = packing_number
            tree_mask = (1 << tree_count) - 1
            projections = ({x & tree_mask for x in code}, {x >> tree_count for x in code})
            # Even the JOINT projection keeping all tree bits and both outer
            # chord slots in every block loses the distinction.
            hide = sum(1 << (tree_count+3*b+1) for b in range(g))
            projections += ({x & ~hide for x in code},)
            if projection_reference is None:
                projection_reference = projections
            assert projection_reference == projections
            assert len(projections[0]) == len(projections[1]) == 8**g
            for j in range(len(edges)):
                unary = {x >> j & 1 for x in code}
                is_bridge = j < tree_count and j % 7 == 6
                assert unary == ({0} if is_bridge else {0, 1})
            for bidx, kind in enumerate(types):
                edge35 = tree_count + 3*bidx + 1
                edge34 = 7*bidx + 2
                assert edges[edge35] == (7*bidx+2, 7*bidx+4)
                assert edges[edge34] == (7*bidx+2, 7*bidx+3)
                pinned = [x for x in code if not (x >> edge35 & 1) and x >> edge34 & 1]
                assert len(pinned) == (2 * 8**(g-1) if kind == 'B' else 0)
            if g == 1:
                one_block_encoding(types[0], code)
                cover, largest = one_block_cover(code, len(edges))
                assert (cover, largest) == ((1,8) if types[0] == 'A' else (2,4))
                # A proper slot prefix can split a tie, unlike a threshold.
                # Chord 13 or 15 creates a cycle including 34 only in B.
                first_chord = even_supports(edges[:tree_count+1])
                assert any(x & (1 << 2) for x in first_chord) == (types[0] == 'B')
        print(f'g={g}: all {2**g} mixtures, ranks/projections and packings {maxima}')


if __name__ == '__main__':
    main()
