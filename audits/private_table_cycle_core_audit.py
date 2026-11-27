"""Check packed tree reductions and the cycle core against full assignments."""

from collections import deque
from dataclasses import dataclass
from itertools import product
from random import Random


@dataclass(frozen=True)
class Relation:
    names: tuple
    bits: int


def restrict_index(value, positions):
    return sum(((value >> position) & 1) << i for i, position in enumerate(positions))


def filter_project(bag, children, ports, low_limit):
    """Each terminal DFS branch filters a whole word; OR before low projection."""
    k = len(bag.names)
    q = min(k, low_limit)
    lanes = 1 << q
    full = (1 << lanes) - 1
    pos = {name: i for i, name in enumerate(bag.names)}
    low_one = [sum(1 << j for j in range(lanes) if j >> i & 1) for i in range(q)]
    patterns = {}
    for child in children:
        for row in range(1 << len(child.names)):
            if child.bits >> row & 1:
                continue
            low, ones, zeroes = full, 0, 0
            for j, name in enumerate(child.names):
                bit = row >> j & 1
                i = pos[name]
                if i < q:
                    low &= low_one[i] if bit else full ^ low_one[i]
                elif bit:
                    ones |= 1 << (i - q)
                else:
                    zeroes |= 1 << (i - q)
            key = (ones, zeroes)
            patterns[key] = patterns.get(key, 0) | low

    port_pos = [pos[name] for name in ports]
    groups = {}

    def descend(h, upper, cubes):
        if not h:
            feasible = ((bag.bits >> (upper * lanes)) & full) & ~cubes.get((0, 0), 0)
            key = restrict_index(upper << q, port_pos)
            groups[key] = groups.get(key, 0) | feasible
            return
        flag = 1 << (h - 1)
        for value in (0, 1):
            remaining = {}
            for (ones, zeroes), low in cubes.items():
                if (zeroes if value else ones) & flag:
                    continue
                key = (ones & ~flag, zeroes & ~flag)
                remaining[key] = remaining.get(key, 0) | low
            descend(h - 1, upper | (flag if value else 0), remaining)

    descend(k - q, 0, patterns)
    masks = {}
    for lane in range(lanes):
        low_key = restrict_index(lane, port_pos)
        masks[low_key] = masks.get(low_key, 0) | (1 << lane)
    result = 0
    for upper, word in groups.items():
        for lower, mask in masks.items():
            if word & mask:
                result |= 1 << (upper | lower)
    return Relation(tuple(ports), result)


def project_row(row, relation, names):
    return restrict_index(row, [relation.names.index(name) for name in names])


def check_factors(bags):
    names = sorted({name for bag in bags for name in bag.names})
    positions = [[names.index(name) for name in bag.names] for bag in bags]
    return any(all(bag.bits >> restrict_index(row, indices) & 1
                   for bag, indices in zip(bags, positions))
               for row in range(1 << len(names)))


def cycle_core(bags, edges, low_limit=2, contraction=False):
    """The connected input supplies one ordered separator tuple per graph edge."""
    n = len(bags)
    adjacent = [[] for _ in range(n)]
    for index, (left, right, _) in enumerate(edges):
        adjacent[left].append((right, index))
        adjacent[right].append((left, index))
    parent = {0}
    queue = deque([0])
    tree_edges = set()
    while queue:
        v = queue.popleft()
        for other, index in adjacent[v]:
            if other not in parent:
                parent.add(other)
                tree_edges.add(index)
                queue.append(other)
    assert len(parent) == n
    chords = [edge for i, edge in enumerate(edges) if i not in tree_edges]
    marked = {v for left, right, _ in chords for v in (left, right)} or {0}
    tree = [{other: index for other, index in row if index in tree_edges}
            for row in adjacent]
    queue = deque(v for v in range(n) if v not in marked and len(tree[v]) == 1)
    incoming = [[] for _ in range(n)]
    removed = set()
    while queue:
        v = queue.popleft()
        other, index = next(iter(tree[v].items()))
        summary = filter_project(bags[v], incoming[v], edges[index][2], low_limit)
        incoming[other].append(summary)
        del tree[other][v]
        tree[v].clear()
        removed.add(v)
        if other not in marked and len(tree[other]) == 1:
            queue.append(other)

    live = set(range(n)) - removed
    special = {v for v in live if v in marked or len(tree[v]) != 2}
    local = {}
    for v in live:
        ports = {name for index in tree[v].values() for name in edges[index][2]}
        for left, right, scope in chords:
            if v in (left, right):
                ports.update(scope)
        local[v] = filter_project(bags[v], incoming[v], sorted(ports), low_limit)

    links = {v: [] for v in special}
    for start in special:
        for first, edge in tree[start].items():
            source_scope = edges[edge][2]
            previous, curr = start, first
            segments = []
            end_scope = source_scope
            while curr not in special:
                nxt, next_edge = next((x, e) for x, e in tree[curr].items() if x != previous)
                next_scope = edges[next_edge][2]
                segments.append((local[curr], end_scope, next_scope))
                end_scope = next_scope
                previous, curr = curr, nxt
            if curr < start:
                continue
            pairs = set()
            for source in range(1 << len(source_scope)):
                possible = {source}
                for relation, left, right in segments:
                    possible = {project_row(row, relation, right)
                                for row in range(1 << len(relation.names))
                                if relation.bits >> row & 1 and project_row(row, relation, left) in possible}
                pairs.update((source, sink) for sink in possible)
            links[start].append((curr, source_scope, end_scope, pairs))
            links[curr].append((start, end_scope, source_scope, {(b, a) for a, b in pairs}))

    if contraction:
        return contract_core(special, links, chords, local)

    chord_names = sorted({name for _, _, names in chords for name in names})
    for value in range(1 << len(chord_names)):
        fixed = {name: (value >> i) & 1 for i, name in enumerate(chord_names)}

        def allowed(v, parent_node, exit_scope, pins):
            constraints = []
            for other, here, there, pairs in links[v]:
                if other == parent_node:
                    continue
                downstream = allowed(other, v, there, pins)
                constraints.append((here, {a for a, b in pairs if b in downstream}))
            table = local[v]
            feasible = set()
            for row in range(1 << len(table.names)):
                if not (table.bits >> row & 1):
                    continue
                if any((row >> i & 1) != pins[name] for i, name in enumerate(table.names) if name in pins):
                    continue
                if all(project_row(row, table, scope) in accepted for scope, accepted in constraints):
                    feasible.add(project_row(row, table, exit_scope))
            return feasible

        if allowed(min(special), None, (), fixed):
            return True
    return False


def contract_core(special, links, chords, local):
    """Second core algorithm, with distinct local copies for each edge port."""
    if not chords:
        return bool(local[min(special)].bits)
    incidence = {v: [] for v in special}
    scopes = []
    neighbors = {v: set() for v in special}
    transfers = {}
    serial = max(special) + 1

    def add_edge(left, right, names):
        ident = len(scopes)
        scopes.append(tuple(names))
        incidence[left].append(ident)
        incidence[right].append(ident)
        neighbors[left].add(right)
        neighbors[right].add(left)

    for v in special:
        for u, left, right, pairs in links[v]:
            if u < v:
                continue
            joint = serial
            serial += 1
            incidence[joint] = []
            neighbors[joint] = set()
            transfers[joint] = pairs, len(left)
            add_edge(v, joint, left)
            add_edge(joint, u, right)
    for v, u, scope in chords:
        add_edge(v, u, scope)

    def bundle(edge_ids):
        return tuple((e, i) for e in sorted(edge_ids) for i in range(len(scopes[e])))

    order = []
    stack = [min(special)]
    seen = set()
    while stack:
        v = stack.pop()
        if v in seen:
            continue
        seen.add(v)
        order.append(v)
        stack.extend(neighbors[v] - seen)

    active = set()
    table = Relation((), 1)
    for v in order:
        incident = set(incidence[v])
        assert len(active | incident) <= 2 * len(chords) + 1
        all_bits = bundle(active | incident)
        if len(all_bits) > 12:
            return None  # The audit caps its brute-force union table.
        local_bits = bundle(incident)
        new_active = active ^ incident
        out = bundle(new_active)
        old_positions = [all_bits.index(bit) for bit in table.names]
        local_positions = [all_bits.index(bit) for bit in local_bits]
        out_positions = [all_bits.index(bit) for bit in out]
        current = 0
        if v in transfers:
            pairs, left_size = transfers[v]
            for a, b in pairs:
                current |= 1 << (a | (b << left_size))
        else:
            names = tuple(scopes[e][i] for e, i in local_bits)
            positions = [local[v].names.index(name) for name in names]
            for row in range(1 << len(local[v].names)):
                if local[v].bits >> row & 1:
                    current |= 1 << restrict_index(row, positions)
        joined = 0
        for row in range(1 << len(all_bits)):
            if (table.bits >> restrict_index(row, old_positions) & 1
                    and current >> restrict_index(row, local_positions) & 1):
                joined |= 1 << restrict_index(row, out_positions)
        active = new_active
        table = Relation(out, joined)
    assert not active
    return bool(table.bits)


def random_instance(rng):
    n = rng.randrange(2, 8)
    pairs = [(rng.randrange(v), v) for v in range(1, n)]
    others = [(u, v) for u in range(n) for v in range(u + 1, n) if (u, v) not in pairs]
    rng.shuffle(others)
    pairs.extend(others[:rng.randrange(min(3, len(others)) + 1)])
    adjacent = [[] for _ in range(n)]
    for i, (u, v) in enumerate(pairs):
        adjacent[u].append(i)
        adjacent[v].append(i)
    shared = [set() for _ in pairs]
    names = [set() for _ in range(n)]
    for name in range(rng.randrange(1, 10)):
        start = rng.randrange(n)
        names[start].add(name)
        live = {start}
        for _ in range(rng.randrange(5)):
            options = {i for v in live for i in adjacent[v] if len(shared[i]) < 3}
            if not options:
                break
            i = rng.choice(sorted(options))
            u, v = pairs[i]
            shared[i].add(name)
            names[u].add(name)
            names[v].add(name)
            live.update((u, v))
    bags = []
    for row in names:
        order = sorted(row)
        rng.shuffle(order)
        bags.append(Relation(tuple(order), rng.getrandbits(1 << len(order))))
    edges = [(u, v, tuple(sorted(shared[i], reverse=bool(i % 2))))
             for i, (u, v) in enumerate(pairs)]
    rng.shuffle(edges)
    return bags, edges


def main():
    triangles = [(0, 1, (1,)), (1, 2, (2,)), (0, 2, (0,))]
    for x, y, z in product(range(16), repeat=3):
        bags = [Relation((0, 1), x), Relation((1, 2), y), Relation((2, 0), z)]
        expected = check_factors(bags)
        assert cycle_core(bags, triangles, low_limit=1) == expected
        assert cycle_core(bags, triangles, low_limit=1, contraction=True) == expected
    print('4096 triangle relation instances checked')

    rng = Random(26791)
    counts = {}
    contractions = 0
    for _ in range(500):
        bags, edges = random_instance(rng)
        expected = check_factors(bags)
        for low_limit in (0, 1, 3):
            assert cycle_core(bags, edges, low_limit) == expected
        contracted = cycle_core(bags, edges, contraction=True)
        if contracted is not None:
            assert contracted == expected
            contractions += 1
        beta = len(edges) - len(bags) + 1
        counts[beta] = counts.get(beta, 0) + 1
    print('500 connected instances at three pack widths checked; by cycle rank', counts)
    print(f'{contractions} random compressed cores independently contracted')


if __name__ == '__main__':
    main()
