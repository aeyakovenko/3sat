"""Check witness-only clause masks and contraction of marked incidence trees."""
from collections import deque
from itertools import combinations, product
from random import Random


def bit(i):
    return 1 << i


def satisfying(rows, value):
    return all(any(bool(value >> (abs(lit) - 1) & 1) == (lit > 0) for lit in row) for row in rows)


def clauses(n):
    return [tuple(v * s for v, s in zip(vs, signs))
            for vs in combinations(range(1, n + 1), 3)
            for signs in product((-1, 1), repeat=3)]


def positive_count(n):
    # Exact inclusion/exclusion over subsets of complete assignments; each
    # intersection is all submasks of its common allowed-clause mask.
    rows = clauses(n)
    masks = [sum(bit(j) for j, row in enumerate(rows) if satisfying([row], z))
             for z in range(bit(n))]
    intersections = [(bit(len(rows)) - 1, 1)]
    positive = 0
    for mask in masks:
        new = [(old & mask, -sign) for old, sign in intersections]
        positive -= sum(sign * bit(common.bit_count()) for common, sign in new)
        intersections.extend(new)
    return positive


def domains_and_edges(rows):
    n = max(abs(t) for row in rows for t in row)
    unary = {i: 3 for i in range(n)}
    edges = []
    for j, row in enumerate(rows, n):
        forbidden = sum(bit(i) for i, lit in enumerate(row) if lit < 0)
        unary[j] = 255 ^ bit(forbidden)
        for i, lit in enumerate(row):
            # Endpoint states are the actual variable values, even for signed occurrences.
            rel = tuple(sum(bit(z) for z in range(8) if (z >> i & 1) == x) for x in range(2))
            edges.append((abs(lit) - 1, j, i, rel + (0,) * 6))
    return unary, edges


def transpose(rel):
    return tuple(sum(bit(i) for i in range(8) if rel[i] & bit(j)) for j in range(8))


def glue(left, domain, right):
    # Relation at the two surviving endpoints after projecting the middle.
    def row(i):
        mask = 0
        for mid in range(8):
            if left[i] & domain & bit(mid):
                mask |= right[mid]
        return mask
    return tuple(row(i) for i in range(8))


def compress(rows):
    return kernel(*domains_and_edges(rows))


def kernel(unary, edges):
    unary = unary.copy()
    parent = {x: x for x in unary}
    tree = {x: {} for x in unary}
    chords = []

    def root(x):
        while x != parent[x]:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def link(a, b, rel):
        tree[a][b] = rel
        tree[b][a] = transpose(rel)

    for a, b, pos, rel in edges:
        ra, rb = root(a), root(b)
        if ra == rb:
            chords.append((a, b, pos))
        else:
            parent[ra] = rb
            link(a, b, rel)
    # Cases here use connected formulas on consecutive occurring variable names.
    assert len({root(x) for x in unary}) == 1
    assert len(chords) == len(edges) - len(unary) + 1
    marked = {x for a, b, _ in chords for x in (a, b)}
    pending = deque(x for x in tree if x not in marked and len(tree[x]) <= 2)
    scalar = True
    while pending:
        x = pending.popleft()
        if x not in tree or x in marked or len(tree[x]) > 2:
            continue
        ns = list(tree[x])
        if len(ns) == 2:
            a, b = ns
            rel = glue(tree[a][x], unary[x], tree[x][b])
            link(a, b, rel)
        elif len(ns) == 1:
            a, = ns
            unary[a] &= sum(bit(i) for i in range(8) if tree[a][x][i] & unary[x])
        else:
            scalar &= bool(unary[x])
        for a in ns:
            del tree[a][x]
            if a not in marked and len(tree[a]) <= 2:
                pending.append(a)
        del tree[x]
        del unary[x]
    assert len(tree) <= max(0, 4 * len(chords) - 2)
    return scalar, unary, tree, chords


def feasible(scalar, unary, tree, chords, bits):
    if not scalar or not tree:
        return scalar
    domains = unary.copy()
    for i, (a, b, pos) in enumerate(chords):
        v = bits >> i & 1
        domains[a] &= bit(v)
        domains[b] &= sum(bit(z) for z in range(8) if z >> pos & 1 == v)

    def visit(x, parent):
        viable = domains[x]
        for child, rel in tree[x].items():
            if child != parent:
                sub = visit(child, x)
                viable &= sum(bit(i) for i in range(8) if rel[i] & sub)
        return viable

    return bool(visit(next(iter(tree)), None))


def test(rows, rng):
    scalar, unary, tree, chords = compress(rows)
    n = max(abs(t) for row in rows for t in row)
    observed = {sum(((z >> a) & 1) << i for i, (a, _, _) in enumerate(chords))
                for z in range(bit(n)) if satisfying(rows, z)}
    if len(chords) <= 9:
        choices = range(bit(len(chords)))
    else:
        choices = observed | {rng.getrandbits(len(chords)) for _ in range(60)}
    for choices_bit in choices:
        assert feasible(scalar, unary, tree, chords, choices_bit) == (choices_bit in observed)
    return len(choices), len(tree), len(chords)


def solve_blocks(rows):
    unary, edges = domains_and_edges(rows)
    adjacency = {x: [] for x in unary}
    for edge, (a, b, _, _) in enumerate(edges):
        adjacency[a].append((b, edge))
        adjacency[b].append((a, edge))
    stack, blocks, disc = [], [], {}

    def visit(x, parent_edge):
        disc[x] = len(disc)
        low = disc[x]
        for y, edge in adjacency[x]:
            if y not in disc:
                stack.append(edge)
                child = visit(y, edge)
                low = min(low, child)
                if child >= disc[x]:
                    block = []
                    while not block or block[-1] != edge:
                        block.append(stack.pop())
                    blocks.append(block)
            elif edge != parent_edge and disc[y] < disc[x]:
                low = min(low, disc[y])
                stack.append(edge)
        return low

    visit(next(iter(unary)), None)
    assert len(disc) == len(unary) and sorted(e for block in blocks for e in block) == list(range(len(edges)))
    incident = {x: [] for x in unary}
    vertex_sets = []
    for b, ids in enumerate(blocks):
        vs = {x for e in ids for x in edges[e][:2]}
        vertex_sets.append(vs)
        for x in vs:
            incident[x].append(b)
    seen = set()

    def solve(b, parent):
        assert b not in seen
        seen.add(b)
        domains = {x: unary[x] for x in vertex_sets[b]}
        for x in domains:
            if x != parent:
                for child in incident[x]:
                    if child != b:
                        domains[x] &= solve(child, x)
        answer = 0
        for state in range(1 if parent is None else 8):
            trial = domains.copy()
            if parent is not None:
                trial[parent] &= bit(state)
            scalar, masks, tree, feedback = kernel(trial, [edges[e] for e in blocks[b]])
            names = sorted({a for a, _, _ in feedback})
            for z in range(bit(len(names))):
                choice = sum(((z >> names.index(a)) & 1) << i for i, (a, _, _) in enumerate(feedback))
                if feasible(scalar, masks, tree, feedback, choice):
                    answer |= bit(state)
                    break
        return answer

    answer = solve(0, None)
    assert seen == set(range(len(blocks)))
    first_clause = len(unary) - len(rows)
    return bool(answer), sum(len(bs) > 1 for x, bs in incident.items() if x >= first_clause)


def serialized_batch(rng):
    anchored = []
    for i in range(3):
        ids = (1+i, 4+2*i, 5+2*i)
        anchored.extend(tuple(-v if val else v for v, val in zip(ids, bits))
                        for bits in product((0, 1), repeat=3) if bits != (0, 0, 0))
    components = [clauses(3), anchored + [(1,2,3)], anchored + [(-1,2,3)]]
    for n in range(3, 8):
        components.append([(i,i+1,i+2) for i in range(1,n-1)] + rng.sample(clauses(n), 4))
    seed_names = rng.sample(range(1000,100000), sum(max(abs(t) for row in f for t in row) for f in components))
    expected, merged = {}, []
    for rows in components:
        n = max(abs(t) for row in rows for t in row)
        rename = [seed_names.pop() for _ in range(n)]
        expected[frozenset(rename)] = any(satisfying(rows, z) for z in range(bit(n)))
        for row in rows + [rows[0]]:
            record = [rename[abs(lit)-1] * (1 if lit > 0 else -1) for lit in row]
            rng.shuffle(record)
            merged.append(record)
    rng.shuffle(merged)
    lines = [f'p cnf 99999 {len(merged)}'] + [' '.join(str(v) for v in row) + ' 0' for row in merged]
    data = ('\n'.join(lines) + '\n').encode('ascii')
    header, *records = data.splitlines()
    assert int(header.split()[3]) == len(records)
    edges = set()
    graph = {}
    for line in records:
        *row, end = map(int, line.split())
        assert end == 0 and len(row) == len({abs(lit) for lit in row}) == 3
        edges.add(tuple(sorted(row, key=abs)))
        for t in row:
            graph.setdefault(abs(t), set()).update(abs(x) for x in row if x != t)
    groups = {}
    while graph:
        start = next(iter(graph))
        pending, vs = [start], set()
        while pending:
            x = pending.pop()
            if x in graph:
                vs.add(x)
                pending.extend(graph.pop(x))
        for x in vs:
            groups[x] = frozenset(vs)
    batches = {}
    for row in edges:
        batches.setdefault(groups[abs(row[0])], []).append(row)
    actual = {}
    clause_cuts = 0
    for group, rows in batches.items():
        rank = {x:i for i,x in enumerate(sorted(group), 1)}
        local = [tuple((1 if t > 0 else -1)*rank[abs(t)] for t in row) for row in rows]
        value, cuts = solve_blocks(local)
        actual[group] = value
        clause_cuts += cuts
    assert actual == expected and set(actual.values()) == {False, True} and clause_cuts > 0
    return len(data)*8, len(batches), sum(actual.values()), clause_cuts


def main():
    assert positive_count(3) == sum(any(satisfying([row for i, row in enumerate(clauses(3))
                                                    if mask & bit(i)], z) for z in range(8))
                                    for mask in range(256)) == 255
    count4 = positive_count(4)
    samples, probes, improved = 0, 0, 0
    rng = Random(49923)
    for n in range(3, 8):
        pool = clauses(n)
        for _ in range(65):
            rows = [tuple(rng.choice((-1, 1)) * z for z in (i, i+1, i+2))
                    for i in range(1, n-1)]
            rows.extend(rng.sample(pool, rng.randrange(0, min(12, len(pool)) + 1)))
            rng.shuffle(rows)
            checked, nodes, _ = test(rows, rng)
            probes += checked
            improved += int(nodes < n + len(rows))
            samples += 1
    # Explicit long incidence trees with and without a cyclic subformula.
    extra = [(i, i+1, i+2) for i in range(3, 15, 2)]
    for start in ([(1,2,3)], [(1,2,3), (-1,-2,-3)]):
        checked, nodes, rho = test(start + extra, rng)
        assert nodes <= 6 and rho <= 2
        probes += checked
        samples += 1
    file_bits, count, positive, cuts = serialized_batch(rng)
    print(f"{file_bits}-bit shuffled DIMACS: {count} recovered components ({positive} SAT), {cuts} clause articulations.")
    print(f"Positive proper clause masks: 255 / 256 on 3 variables; {count4} / {2**32} on 4.")
    print(f"{samples} connected instances and {probes} feedback-value profiles checked; "
          f"{improved} of 325 random inputs shrink, plus both long-tree examples.")


if __name__ == '__main__':
    main()
