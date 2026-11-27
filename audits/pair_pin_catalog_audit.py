"""Exhaust the degree-two component scan and the 12-to-24 vertex cubic catalog."""
from itertools import combinations, permutations, product


def neighbor_masks(n, edges):
    adj = [0]*n
    for a, b in edges:
        assert 0 <= a < b < n
        assert not adj[a] & (1 << b)
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def selected(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def low_degree_program(adj):
    """Order each component along its path or cycle; compile start/close flags."""
    todo = set(range(len(adj)))
    records = []
    while todo:
        root = min(todo)
        component = {root}
        stack = [root]
        while stack:
            for u in selected(adj[stack.pop()]):
                if u not in component:
                    component.add(u)
                    stack.append(u)
        todo -= component
        endpoints = {u for u in component if adj[u].bit_count() <= 1}
        cycle = not endpoints
        u = min(endpoints or component)
        ordered = [u]
        seen = {u}
        while True:
            choices = [v for v in selected(adj[u]) if v not in seen]
            if not choices:
                break
            u = min(choices)
            ordered.append(u)
            seen.add(u)
        assert seen == component
        if cycle:
            assert len(ordered) >= 3 and adj[ordered[-1]] & (1 << ordered[0])
        records.extend((u, i == 0, cycle and i+1 == len(ordered))
                       for i, u in enumerate(ordered))
    assert sorted(u for u, _, _ in records) == list(range(len(adj)))
    return records


def scan(records, mask):
    prev = first = False
    for u, starts, closes in records:
        bit = bool(mask & (1 << u))
        if starts:
            first = bit
        if (not starts and prev and bit) or (closes and first and bit):
            return False
        prev = bit
    return True


def pair_directory(n):
    pairs = list(combinations(range(n), 2))
    response_masks = [0]*(1 << n)
    for i, (u, v) in enumerate(pairs):
        need = (1 << u) | (1 << v)
        for bits in range(1 << n):
            if bits & need == need:
                response_masks[bits] |= 1 << i
    return pairs, response_masks


def nonedges(pairs, adj):
    return sum(1 << i for i, (u, v) in enumerate(pairs) if not adj[u] & (1 << v))


def audit_degree_two(n):
    pairs, response_masks = pair_directory(n)
    graph_count = assignments = pair_checks = 0
    for present in range(1 << len(pairs)):
        edges = [pairs[i] for i in selected(present)]
        adj = neighbor_masks(n, edges)
        if any(neighbors.bit_count() > 2 for neighbors in adj):
            continue
        program = low_degree_program(adj)
        edge_masks = [(1 << u) | (1 << v) for u, v in edges]
        realized = 0
        for bits in range(1 << n):
            accept = scan(program, bits)
            assert accept == all(bits & edge != edge for edge in edge_masks)
            if accept:
                realized |= response_masks[bits]
            assignments += 1
        assert realized == nonedges(pairs, adj)
        graph_count += 1
        pair_checks += len(pairs)
    return graph_count, assignments, pair_checks


def cubic_graphs(r):
    # Three groups on each shore. Nine separately recoverable matchings.
    for choices in product(permutations(range(r)), repeat=9):
        yield frozenset((i*r+k, 3*r+j*r+choices[3*i+j][k])
                        for i in range(3) for j in range(3) for k in range(r))


def cubic_pair_responses(adj, response_masks):
    """Actually existentially quantify over every selected subset of the fresh graph."""
    n = len(adj)
    valid = bytearray(1 << n)
    valid[0] = 1
    answers = accepted = 0
    for mask in range(1, 1 << n):
        bit = mask & -mask
        rest = mask ^ bit
        if valid[rest] and not adj[bit.bit_length()-1] & rest:
            valid[mask] = 1
            answers |= response_masks[mask]
            accepted += 1
    return answers, accepted + 1


def audit_cubic():
    n = 12
    pairs, response_masks = pair_directory(n)
    old = next(cubic_graphs(2))
    old_adj = neighbor_masks(n, old)
    old_answers, _ = cubic_pair_responses(old_adj, response_masks)
    assert old_answers == nonedges(pairs, old_adj) and old_answers.bit_count() == 48
    sets = set()
    extension_bits = set()
    accepted = 0
    for fresh in cubic_graphs(2):
        assert fresh not in sets
        sets.add(fresh)
        adj = neighbor_masks(n, fresh)
        assert len(fresh) == 18 and all(a.bit_count() == 3 for a in adj)
        answers, independent_sets = cubic_pair_responses(adj, response_masks)
        assert answers == nonedges(pairs, adj) and answers.bit_count() == 48
        accepted += independent_sets
        extension_bits.add(answers)

        combined = old | {(u+n, v+n) for u,v in fresh}
        both = neighbor_masks(2*n, combined)
        assert len(combined) == 36 and all(a.bit_count() == 3 for a in both)
        assert nonedges(pairs, both) == old_answers
        assert nonedges([(u+n,v+n) for u,v in pairs], both) == answers
        assert all(not both[u] & (1 << (n+v)) for u in range(n) for v in range(n))
        # The empty extension witnesses every independent pair. A doubled graph
        # therefore accepts 48 old, 48 fresh, and all 144 cross pairs.
        assert nonedges(list(combinations(range(2*n), 2)), both).bit_count() == 240
    assert len(sets) == len(extension_bits) == 2**9
    return len(sets), accepted


if __name__ == '__main__':
    totals = [audit_degree_two(n) for n in range(7)]
    print('degree at most two, n=0..6:')
    for n, (graphs, assignments, pairs) in enumerate(totals):
        print(f'  n={n}: {graphs} graphs, {assignments} selected subsets, {pairs} pair answers')
    print('totals:', *(sum(group) for group in zip(*totals)))
    fresh, counts = audit_cubic()
    print(f'{fresh} cubic extensions, {fresh * 4096} fresh subsets, {counts} independent; '
          f'{fresh} distinct fresh response vectors, 66 old answers preserved per extension')
