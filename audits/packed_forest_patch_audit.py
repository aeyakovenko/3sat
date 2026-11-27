"""Compare physical SAT patch files, forest messages and two-hole lookup tables."""

from functools import lru_cache
from itertools import product
from random import Random


def build_tree(clauses, shared):
    nodes = []
    def add(op, *children):
        nodes.append((op, children))
        return len(nodes)-1
    def combine(inputs, identity):
        current = add(('const', identity))
        for item in inputs:
            current = add(('and',), current, item)
        return current
    shared_id = {x: i for i, x in enumerate(shared)}
    local = {abs(l) for row in clauses for l in row} - set(shared)
    incident = {x: set() for x in local}
    buckets = {}
    for row in clauses:
        scope = tuple(sorted({abs(l) for l in row if abs(l) in local}))
        assert len(scope) <= 2
        if len(scope) == 2:
            x, y = scope
            incident[x].add(y)
            incident[y].add(x)
        buckets.setdefault(scope, []).append(row)
    def guard(scope, row):
        fields = tuple(('l', scope.index(abs(l)), l > 0) if abs(l) in scope
                       else ('z', shared_id[abs(l)], l > 0) for l in row)
        return add(('guard', len(scope), fields))
    visited = set()
    def subtree(x, parent):
        visited.add(x)
        incoming = [guard((x,), row) for row in buckets.get((x,), ())]
        for y in sorted(incident[x] - {parent}):
            assert y not in visited
            child = subtree(y, x)
            edge = [guard((x, y), row) for row in buckets[tuple(sorted((x, y)))]]
            incoming.append(add(('send',), combine(edge, 15), child))
        return combine(incoming, 3)
    roots = [guard((), row) for row in buckets.get((), ())]
    for x in sorted(local):
        if x not in visited:
            roots.append(add(('exists',), subtree(x, None)))
    root = combine(roots, 1)
    return nodes, root


def transition(op, inputs, valuation):
    tag = op[0]
    if tag == 'const':
        return op[1]
    if tag == 'and':
        return inputs[0] & inputs[1]
    if tag == 'exists':
        return int(inputs[0] != 0)
    if tag == 'send':
        relation, allowed = inputs
        return sum(1 << x for x in range(2)
                   if any(allowed >> y & 1 and relation >> (x + 2*y) & 1 for y in range(2)))
    assert tag == 'guard'
    _, arity, fields = op
    return sum(1 << word for word in range(1 << arity)
               if any(bool((word if kind == 'l' else valuation) >> i & 1) == polarity
                      for kind, i, polarity in fields))


def make_pieces(nodes, max_size):
    # A convenient finite partitioner; the asymptotic piece count in the
    # manuscript uses the published linear-time tree-covering lemma.
    blocks = {}
    for root, (_, children) in enumerate(nodes):
        inside, holes = {root}, list(children)
        for child in children:
            sub, subholes = blocks[child]
            if len(inside) + len(sub) <= max_size and len(holes) - 1 + len(subholes) <= 2:
                del blocks[child]
                inside |= sub
                holes.remove(child)
                holes.extend(subholes)
        blocks[root] = inside, holes
    return blocks


def piece_key(nodes, root, members, holes):
    if root not in members:
        return ('hole', holes.index(root))
    op, children = nodes[root]
    return ('node', op, tuple(piece_key(nodes, c, members, holes) for c in children))


@lru_cache(None)
def state_masks(key, args, bits):
    def walk(key, z):
        if key[0] == 'hole':
            return args[key[1]]
        return transition(key[1], tuple(walk(child, z) for child in key[2]), z)
    out = {}
    for z in range(1 << bits):
        state = walk(key, z)
        out[state] = out.get(state, 0) | (1 << z)
    return out


def packed_verdicts(rows, shared, bound):
    nodes, root = build_tree(rows, shared)
    pieces = make_pieces(nodes, bound)
    results = {}
    all_mask = (1 << (1 << len(shared))) - 1
    for v, (members, holes) in pieces.items():
        key = piece_key(nodes, v, members, holes)
        combined = {}
        for args in product(*(results[child] for child in holes)):
            mask = all_mask
            for child, state in zip(holes, args):
                mask &= results[child][state]
            for result, piece_mask in state_masks(key, args, len(shared)).items():
                covered = piece_mask & mask
                if covered:
                    combined[result] = combined.get(result, 0) | covered
        assert sum(value.bit_count() for value in combined.values()) == 1 << len(shared)
        results[v] = combined
    return results[root].get(1, 0)


def direct(rows, shared):
    local = sorted({abs(l) for row in rows for l in row} - set(shared))
    out = 0
    for z in range(1 << len(shared)):
        base = {x: bool(z >> i & 1) for i, x in enumerate(shared)}
        for values in product((False, True), repeat=len(local)):
            assignment = base | dict(zip(local, values))
            if all(any(assignment[abs(l)] == (l > 0) for l in row) for row in rows):
                out |= 1 << z
                break
    return out


def encode(rows):
    bound = max(abs(l) for row in rows for l in row)
    return (f"p cnf {bound} {len(rows)}\n" +
            ''.join(' '.join(map(str, row)) + ' 0\n' for row in rows)).encode('ascii')


def decode(data):
    lines = data.splitlines()
    _, _, variables, count = lines[0].split()
    assert int(count) == len(lines)-1
    rows = []
    for line in lines[1:]:
        *row, end = map(int, line.split())
        assert end == 0 and len(set(map(abs, row))) == len(row) == 3
        assert max(map(abs, row)) <= int(variables)
        rows.append(tuple(row))
    return rows


def check_high_interaction(source):
    # Occurrences begin at 1. The three final names are shared anchors.
    copies = {}
    rows, triangles = [], []
    occurrence_count = 3 * len(source)
    u, v, w = range(occurrence_count + 1, occurrence_count + 4)
    for j, row in enumerate(source):
        triangle = tuple(3*j + i + 1 for i in range(3))
        rows.append(tuple(x if lit > 0 else -x for lit, x in zip(row, triangle)))
        triangles.append(set(triangle))
        for lit, x in zip(row, triangle):
            copies.setdefault(abs(lit), []).append(x)
            rows.append((u, v, x))
    for chain in copies.values():
        for prev, curr in zip(chain, chain[1:]):
            rows.extend([(-prev, curr, w), (prev, -curr, w)])
    anchors = [tuple(-x if val else x for x, val in zip((u,v,w), setting))
               for setting in product((0, 1), repeat=3) if setting != (1, 1, 0)]
    rows.extend(anchors)
    rows = decode(encode(rows))
    vertices = sorted({abs(lit) for row in rows for lit in row})
    graph = {x: set() for x in vertices}
    for row in rows:
        for x in map(abs, row):
            graph[x].update(abs(y) for y in row if abs(y) != x)
    for x in vertices:
        pending = [next(y for y in vertices if x != y)]
        seen = {x}
        while pending:
            y = pending.pop()
            if y not in seen:
                seen.add(y)
                pending.extend(graph[y] - seen)
        assert len(seen) == len(vertices)
    assert len(set.union(*triangles)) == 3 * len(source)
    assert all(tri - {x} <= graph[x] for tri in triangles for x in tri)

    def satisfy(clauses, assignment):
        return all(any(assignment[abs(l)] == (l > 0) for l in row) for row in clauses)

    forced = {u: True, v: True, w: False}
    assert [bits for bits in product((False, True), repeat=3)
            if satisfy(anchors, dict(zip((u,v,w), bits)))] == [(True, True, False)]

    # Generic DPLL, with the independently checked anchor consequences seeded.
    # Enumerate both branches when the remaining free variables have no clauses.
    def models(assignment):
        free_rows = []
        for row in rows:
            if any(abs(l) in assignment and assignment[abs(l)] == (l > 0) for l in row):
                continue
            free = [l for l in row if abs(l) not in assignment]
            if not free:
                return
            if len(free) == 1:
                l = free[0]
                yield from models(assignment | {abs(l): l > 0})
                return
            free_rows.append(free)
        if len(assignment) == len(vertices):
            yield assignment
            return
        x = (abs(min(free_rows, key=len)[0]) if free_rows
             else next(x for x in vertices if x not in assignment))
        for bit in (False, True):
            yield from models(assignment | {x: bit})

    names = sorted(copies)
    expected = {bits for bits in product((False, True), repeat=len(names))
                if satisfy(source, dict(zip(names, bits)))}
    witnesses = set()
    for assignment in models(forced):
        bits = tuple(assignment[copies[name][0]] for name in names)
        assert all(assignment[x] == val for name, val in zip(names, bits) for x in copies[name])
        assert bits not in witnesses
        witnesses.add(bits)
    assert witnesses == expected
    return len(witnesses)


def main():
    # Pin variables (12,13,14) to (0,1,0). Flipping the last digit between
    # 12 and 13 in each movable clause changes just one physical bit.
    anchors = [tuple(-v if value else v for v, value in zip((12, 13, 14), pattern))
               for pattern in product((0, 1), repeat=3) if pattern != (0, 1, 0)]
    slots = [(sx*x, sy*y) for x, y in ((1,2), (2,3))
             for sx, sy in product((-1,1), repeat=2)]
    files, sat = [], 0
    for switches in range(1 << len(slots)):
        rows = anchors + [(*pair, 12 + ((switches >> i) & 1)) for i, pair in enumerate(slots)]
        file = encode(rows)
        files.append(file)
        parsed = decode(file)
        actual = direct(parsed, (12,13))
        sat += bool(actual)
        for size in (1,4,9):
            assert packed_verdicts(parsed, (12,13), size) == actual
    edges = 0
    for m, file in enumerate(files):
        for i in range(len(slots)):
            if not m >> i & 1:
                other = files[m | (1 << i)]
                assert len(file) == len(other)
                assert sum((a ^ b).bit_count() for a, b in zip(file, other)) == 1
                edges += 1
    rng = Random(334)
    random_cases = 180
    for _ in range(random_cases):
        shared = (12, 13, 14)
        pairs = [(v, rng.randrange(1, v)) for v in range(2,8)]
        rows = []
        for pair in pairs:
            for _ in range(rng.randrange(1,4)):
                scope = (*pair, rng.choice(shared))
                rows.append(tuple(rng.choice((-1,1))*x for x in scope))
        rows.extend([(-12, 13, 14), (1, -12, -13)])
        rng.shuffle(rows)
        assert packed_verdicts(rows, shared, 8) == direct(rows, shared)
    assert 0 < sat < len(files)
    all_triples = [tuple(-x if bit else x for x, bit in zip((1,2,3), bits))
                   for bits in product((0, 1), repeat=3)]
    tests = [all_triples[:j] for j in range(1, 9)]
    tests.extend([[(1,2,3), (-2,4,5)], [(1,2,3), (-4,-5,-6)], [(-1,2,3), (4,-2,5), (6,-3,7)]])
    high_counts = [check_high_interaction(source) for source in tests]
    assert high_counts[:8] == list(range(7,-1,-1))
    print(f"{len(files)} parsed files ({sat} SAT), {edges} physical one-bit pairs, "
          f"{random_cases} additional forest cases, {len(tests)} parsimonious high-interaction controls")


if __name__ == '__main__':
    main()
