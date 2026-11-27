"""Check the prism/K3,3 blow-ups with a common Hamiltonian zero-weight tree."""
from collections import Counter, deque
from itertools import combinations, product


def vertex(base, twin):
    # Bases 0..5 correspond to the paper's 1..6. Consecutive integers give
    # a Hamiltonian path visiting the entire six-cycle at each twin index.
    return 6*twin + base


def edge(u, v):
    return (u, v) if u < v else (v, u)


def slots(s, prism):
    common_cycle = [(b, (b+1) % 6) for b in range(6)]
    extra = [(0, 2), (1, 4), (3, 5)] if prism else [(0, 3), (1, 4), (2, 5)]
    path = [(i, i+1) for i in range(6*s-1)]
    tree = set(path)
    complete = [edge(vertex(a,i), vertex(b,j)) for a,b in common_cycle + extra
                for i,j in product(range(s), repeat=2)]
    assert len(set(complete)) == 9*s*s and tree.issubset(complete)
    return path + [uv for uv in complete if uv not in tree]


def adjacency(n, edges):
    graph = [set() for _ in range(n)]
    for u,v in edges:
        graph[u].add(v)
        graph[v].add(u)
    return graph


def connected(n, edges):
    graph = adjacency(n, edges)
    seen = {0}
    todo = [0]
    while todo:
        v = todo.pop()
        fresh = graph[v] - seen
        todo.extend(fresh)
        seen.update(fresh)
    return len(seen) == n


def min_cut(n, edges):
    # Every nontrivial cut separates this root from some sink. Compute each
    # unit-capacity undirected s-t min-cut via integral augmenting paths.
    graph = adjacency(n, edges)
    answer = len(graph[0])
    for sink in range(1, n):
        residual = [{v: 1 for v in row} for row in graph]
        flow = 0
        while flow < answer:
            parent = {0: -1}
            todo = deque([0])
            while todo and sink not in parent:
                u = todo.popleft()
                for v, capacity in residual[u].items():
                    if capacity > 0 and v not in parent:
                        parent[v] = u
                        todo.append(v)
            if sink not in parent:
                break
            v = sink
            while v != 0:
                u = parent[v]
                residual[u][v] -= 1
                residual[v][u] += 1
                v = u
            flow += 1
        answer = min(answer, flow)
    return answer


def square_partition(left, right):
    assert len(left) % 2 == 0 and len(right) % 2 == 0
    for i in range(0, len(left), 2):
        for j in range(0, len(right), 2):
            yield (left[i], right[j], left[i+1], right[j+1])


def decomposition(s, prism):
    def fiber(b):
        return [vertex(b,j) for j in range(s)]
    if prism:
        for a,b,c in ((0,1,2), (3,4,5)):
            for i,j in product(range(s), repeat=2):
                yield (vertex(a,i), vertex(b,j), vertex(c,(i+j) % s))
        for a,b in [(0,5), (1,4), (2,3)]:
            yield from square_partition(fiber(a), fiber(b))
    else:
        left = [v for b in (0,2,4) for v in fiber(b)]
        right = [v for b in (1,3,5) for v in fiber(b)]
        yield from square_partition(left, right)


def cycle_edges(cycle):
    assert len(set(cycle)) == len(cycle)
    return [edge(u,v) for u,v in zip(cycle, cycle[1:] + cycle[:1])]


def check_graph(s, prism):
    n = 6*s
    edges = slots(s, prism)
    graph = adjacency(n, edges)
    assert all(len(row) == 3*s for row in graph)
    assert connected(n, edges[:n-1])
    # Connectivity of the complement characterizes full projection of even
    # supports onto the removed coordinates. s=2 is also tested directly.
    assert connected(n, edges[n-1:])
    cut = min_cut(n, edges)
    assert cut == 3*s
    cycles = list(decomposition(s, prism))
    uses = Counter(uv for cycle in cycles for uv in cycle_edges(cycle))
    assert uses == Counter(edges)
    triangle_edges = set()
    for a,b,c in combinations(range(n), 3):
        if b in graph[a] and c in graph[a] and c in graph[b]:
            triangle_edges.update((edge(a,b), edge(b,c), edge(c,a)))
    # At most a third of these edges' number of edge-disjoint triangles;
    # every other nonempty simple cycle consumes at least four edges.
    upper = (len(edges) + len(triangle_edges)//3)//4
    assert len(cycles) == upper == (11 if prism else 9)*s*s//4
    return edges, cut, len(cycles)


def shared_cut_check(s, left, right):
    a, b = set(left), set(right)
    shared = sorted(a & b)
    n = 6*s

    def edge_mask(uv):
        return (1 << uv[0]) | (1 << uv[1])

    # A cut is supported on actual shared physical edges iff it splits none
    # of the graph's unique edges. Compute both spaces in the SAME edge order.
    common_masks = list(map(edge_mask, shared))
    def cut_words(unique, subsets):
        unique_masks = list(map(edge_mask, unique))
        space = set()
        for chosen in subsets:
            if any((chosen & edge).bit_count() == 1 for edge in unique_masks):
                continue
            support = sum(1 << i for i, edge in enumerate(common_masks)
                          if (chosen & edge).bit_count() == 1)
            space.add(support)
        return space

    if s == 2:
        # All 2^12 vertex subsets, also counting their complements.
        cuts_a = cut_words(a - b, range(1 << n))
        cuts_b = cut_words(b - a, range(1 << n))
    else:
        def unions_of_components(unique):
            graph = adjacency(n, unique)
            remaining = set(range(n))
            subsets = [0]
            while remaining:
                first = remaining.pop()
                reached = {first}
                todo = [first]
                while todo:
                    fresh = graph[todo.pop()] & remaining
                    reached.update(fresh)
                    remaining.difference_update(fresh)
                    todo.extend(fresh)
                mask = sum(1 << v for v in reached)
                subsets += [old | mask for old in subsets]
            return subsets
        cuts_a = cut_words(a - b, unions_of_components(a - b))
        cuts_b = cut_words(b - a, unions_of_components(b - a))
    gap_a = min(x.bit_count() for x in cuts_a - cuts_b)
    gap_b = min(x.bit_count() for x in cuts_b - cuts_a)
    assert (gap_a, gap_b) == (3*s*s, 4*s*s)

    # This physical shared cut separates the two triangles of the base prism.
    cut = {uv for uv in shared if (uv[0] % 6 < 3) != (uv[1] % 6 < 3)}
    cut_bits = sum(1 << i for i, uv in enumerate(shared) if uv in cut)
    assert cut_bits in cuts_a - cuts_b and len(cut) == gap_a
    witness = set(cycle_edges(tuple(vertex(base,0) for base in (0,1,2,3))))
    assert witness <= b and len(witness & cut) == 1
    return gap_a, gap_b


def successive_forests(n, rows, passes):
    # Parallel edges have distinct immutable slots. Break weight ties by slot.
    remaining = set(range(len(rows)))
    for _ in range(passes):
        groups = list(range(n))
        tree = []
        for i in sorted(remaining, key=lambda j: (rows[j][2], j)):
            u,v,_ = rows[i]
            if groups[u] != groups[v]:
                old, new = groups[v], groups[u]
                groups = [new if value == old else value for value in groups]
                tree.append(i)
        remaining.difference_update(tree)
    return sum(1 << i for i in range(len(rows)) if i not in remaining)


def brute_even_words(rows):
    words = []
    for word in range(1 << len(rows)):
        boundary = 0
        for i,(u,v,_) in enumerate(rows):
            if word & (1 << i):
                boundary ^= (1 << u) ^ (1 << v)
        if boundary == 0:
            words.append(word)
    return words


def parts_after(n, rows, allowed):
    graph = adjacency(n, [(u,v) for i,(u,v,_) in enumerate(rows) if allowed & (1 << i)])
    pending = set(range(n))
    parts = set()
    while pending:
        seed = pending.pop()
        component = {seed}
        todo = [seed]
        while todo:
            new = graph[todo.pop()] & pending
            component.update(new)
            pending.difference_update(new)
            todo.extend(new)
        parts.add(frozenset(component))
    return parts


def projections(words, allowed, pins):
    return {w & pins for w in words if not (w & ~allowed)}


def check_forests():
    # Every slot may be absent, have weight zero, or have weight one. The
    # first two slots are different parallel edges when both are present.
    slots = [(0,1), (0,1), (0,2), (1,2)]
    graphs = [(3, [(u,v,w) for (u,v),w in zip(slots, weights) if w >= 0])
              for weights in product((-1,0,1), repeat=len(slots))]
    graphs.extend([(2, [(0,1,w) for w in (0,0,0,1,2)]),
                   (4, [(0,1,2),(1,2,0),(0,2,1),(1,3,0),
                        (0,3,1),(2,3,2),(0,1,0),(2,3,0)])])
    checks = outside_positive = 0
    for n, rows in graphs:
        words = brute_even_words(rows)
        for k in (0,1,2):
            kept = successive_forests(n, rows, k+1)
            for threshold in sorted({-1} | {w for _,_,w in rows}):
                active = sum(1 << i for i,(_,_,w) in enumerate(rows) if w <= threshold)
                for j in range(k+1):
                    for selected in combinations(range(len(rows)), j):
                        pins = sum(1 << i for i in selected)
                        free = active & ~pins
                        assert parts_after(n, rows, free) == parts_after(n, rows, free & kept)
                        good = projections(words, active, pins)
                        after = projections(words, active & (kept | pins), pins)
                        assert after == good
                        if any(outcome & ~kept for outcome in good):
                            # Dropping an outside pin entirely would incorrectly
                            # force its terminal to zero. Test this explicitly.
                            assert projections(words, active & kept, pins) != good
                            outside_positive += 1
                        checks += 1
    assert outside_positive > 0
    # k forests alone can lose a parity extension on k retained pinned edges.
    for k in range(1,5):
        rows = [(0,1,0)] * (k+1)
        words = brute_even_words(rows)
        pins = (1 << k)-1
        all_slots = (1 << (k+1))-1
        assert 1 in projections(words, all_slots, pins)
        assert 1 not in projections(words, successive_forests(2, rows, k) | pins, pins)
    print(f'{len(graphs)} weighted multigraphs; {checks} threshold/pin-set comparisons; '
          f'{outside_positive} allow a positive pin outside the forest union; '
          'k-pass counterexamples for k=1..4')


def main():
    check_forests()
    for s in (2,4,6):
        a, cut_a, pack_a = check_graph(s, True)
        b, cut_b, pack_b = check_graph(s, False)
        assert a[:6*s-1] == b[:6*s-1]
        # Under the explicit slot matching, 3s already suffice to separate
        # the two codes: a prism star is an even parity check. A cycle in B
        # meets precisely one of these slots (the A:13 / B:14 bundle).
        star = [k for k, uv in enumerate(a) if vertex(2,0) in uv]
        witness = set(cycle_edges((vertex(0,0), vertex(1,0), vertex(2,1), vertex(3,0))))
        assert witness.issubset(b) and len(star) == 3*s
        assert sum(b[k] in witness for k in star) == 1
        physical_gaps = shared_cut_check(s, a, b)
        print(f's={s}, vertices={6*s}, edges={len(a)}, cuts=({cut_a},{cut_b}), '
              f'packings=({pack_a},{pack_b}), backdoor gap={pack_a-pack_b}, '
              f'directed shared-cut minima={physical_gaps}')


if __name__ == '__main__':
    main()
