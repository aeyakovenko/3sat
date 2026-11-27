"""Compile three XOR-address banks and an optional parity tag into proper 3-DIMACS."""

import argparse
from collections import deque
from itertools import combinations, pairwise, product
from random import Random

from sheet_guard_deletions_audit import solve_dimacs


class ProperCNF:
    def __init__(self, reserved):
        self.reserved = reserved
        self.next_id = 1
        self.rows = []
        self.false1, self.false2 = self.fresh(), self.fresh()
        aux1, aux2 = self.fresh(), self.fresh()
        for false_name in (self.false1, self.false2):
            for s, t in product((-1, 1), repeat=2):
                self.rows.append((-false_name, s * aux1, t * aux2))

    def fresh(self):
        while self.next_id in self.reserved:
            self.next_id += 1
        self.next_id += 1
        return self.next_id - 1

    def clause(self, *row):
        padded = row + (self.false1, self.false2)[:3 - len(row)]
        assert len(padded) == 3 and len({abs(i) for i in padded}) == 3
        self.rows.append(padded)

    def xor(self, a, b):
        z = self.fresh()
        self.clause(a, b, -z)
        self.clause(-a, -b, -z)
        self.clause(-a, b, z)
        self.clause(a, -b, z)
        return z

    def conjunction(self, a, b):
        z = self.fresh()
        self.clause(-z, a)
        self.clause(-z, b)
        self.clause(-a, -b, z)
        return z

    def parity(self, wires):
        assert wires
        z = wires[0]
        for wire in wires[1:]:
            z = self.xor(z, wire)
        return z

    def bank(self, selectors, labels, replicas):
        level = [self.parity(selectors[i * replicas:(i + 1) * replicas]) for i in range(labels)]
        address = []
        while len(level) > 1:
            # A label's current bit is one on each right subtree at this level.
            address.append(self.parity(level[1::2]))
            level = [self.xor(a, b) for a, b in zip(level[::2], level[1::2])]
        return address, level[0]

    def lookup(self, names, address):
        level = list(names)
        for control in address:
            next_level = []
            for a, b in zip(level[::2], level[1::2]):
                z = self.fresh()
                self.clause(control, -a, z)
                self.clause(control, a, -z)
                self.clause(-control, -b, z)
                self.clause(-control, b, -z)
                next_level.append(z)
            level = next_level
        assert len(level) == 1
        return level[0]


def forced_reachability(cnf, labels, edges, source, sink, enabled, presence):
    """Decode the unique source, then propagate forced Boolean values through a DAG."""
    root = cnf.fresh()
    cnf.clause(-root, enabled)
    cnf.clause(root, -enabled)
    seeds = [root]
    for bit in reversed(source):
        seeds = [cnf.conjunction(prefix, sign) for prefix in seeds for sign in (-bit, bit)]
    assert len(seeds) == labels
    successors = [[] for _ in range(labels)]
    pending = [0] * labels
    for slot, (u, v) in enumerate(edges):
        assert 0 <= u < labels and 0 <= v < labels
        successors[u].append((v, slot))
        pending[v] += 1
    ready = deque(v for v in range(labels) if not pending[v])
    values = seeds.copy()
    visited = 0
    while ready:
        u = ready.popleft()
        visited += 1
        for v, slot in successors[u]:
            contribution = values[u] if presence is None else cnf.conjunction(values[u], presence[slot])
            values[v] = -cnf.conjunction(-values[v], -contribution)
            pending[v] -= 1
            if not pending[v]:
                ready.append(v)
    if visited != labels:
        raise ValueError('tagged templates require a directed acyclic graph')
    return cnf.lookup(values, sink)


def build_template(labels, replicas, edges, *, tagged, graph_slots):
    """Build the public bytes. In graph-slot mode edges is the entire ambient DAG."""
    assert labels > 0 and labels & (labels - 1) == 0 and replicas > 0
    size = labels * replicas
    selector_count = (3 + int(tagged)) * size
    total_pairs = selector_count + (len(edges) if graph_slots else 0)
    pairs = [(10 * j + 2, 10 * j + 3) for j in range(total_pairs)]
    cnf = ProperCNF({v for pair in pairs for v in pair})
    for zero_name, one_name in pairs:
        cnf.clause(zero_name, one_name)
        cnf.clause(-zero_name, -one_name)
    addresses, parities = [], []
    for bank in range(3):
        bank_bits = [value for _, value in pairs[bank * size:(bank + 1) * size]]
        address, odd = cnf.bank(bank_bits, labels, replicas)
        addresses.append(address)
        parities.append(odd)
    s_bits = [cnf.xor(x, y) for x, y in zip(addresses[0], addresses[1])]
    t_bits = [cnf.xor(y, z) for y, z in zip(addresses[1], addresses[2])]
    enabled = cnf.conjunction(cnf.conjunction(parities[0], parities[1]), parities[2])
    if tagged:
        tag = cnf.parity([value for _, value in pairs[3 * size:selector_count]])
        presence = [value for _, value in pairs[selector_count:]] if graph_slots else None
        reachable = forced_reachability(cnf, labels, edges, s_bits, t_bits, enabled, presence)
        cnf.clause(-enabled, -reachable, tag)
        cnf.clause(-enabled, reachable, -tag)
    else:
        names = [cnf.fresh() for _ in range(labels)]
        for u, v in edges:
            assert 0 <= u < labels and 0 <= v < labels
            if u != v:
                cnf.clause(-names[u], names[v])
        cnf.clause(-enabled, cnf.lookup(names, s_bits))
        cnf.clause(-enabled, -cnf.lookup(names, t_bits))
    max_id = max(cnf.next_id - 1, pairs[-1][1])
    rows = len(pairs) + len(cnf.rows)
    data = bytearray(f'p cnf {max_id} {rows}\n'.encode())
    offsets, graph_offsets = {}, {}
    gap = b' ' * (2 * (max_id + rows).bit_length())
    for i, (base, alternate) in enumerate(pairs):
        str_base = str(base).encode()
        assert str_base[:-1] + b'3' == str(alternate).encode()
        position = len(data) + len(str_base) - 1
        if i < selector_count:
            bank, site = divmod(i, size)
            offsets[bank, site // replicas, site % replicas] = position
        else:
            graph_offsets[edges[i - selector_count]] = position
        data.extend(str_base + gap + f'{cnf.false1} {cnf.false2} 0\n'.encode())
    data.extend(''.join(f'{a} {b} {c} 0\n' for a, b, c in cnf.rows).encode())
    width = (8 * len(data)).bit_length()
    switch_bytes = [*offsets.values(), *graph_offsets.values()]
    assert all(8 * (b - a) >= width for a, b in pairwise(switch_bytes))
    assert rows <= 120 * size + 9 * len(edges) + 40
    return bytes(data), offsets, graph_offsets


def compile_graph(labels, replicas, edges, *, tagged=False):
    data, offsets, _ = build_template(labels, replicas, edges, tagged=tagged, graph_slots=False)
    return data, offsets


def compile_padded_dag(labels, replicas, ambient_edges, present_edges=()):
    """Return bytes and both offset maps. Public edge order fixes the layout for all subgraphs."""
    if len(set(ambient_edges)) != len(ambient_edges):
        raise ValueError('ambient edge slots must be unique')
    data, query_offsets, graph_offsets = build_template(labels, replicas, ambient_edges,
                                                        tagged=True, graph_slots=True)
    return bytes(edited(data, graph_offsets, present_edges)), query_offsets, graph_offsets


def edited(base, offsets, choices):
    data = bytearray(base)
    for choice in choices:
        i = offsets[choice]
        assert data[i] == ord('2')
        data[i] ^= 1
    return data


def transitive_closure(n, edges):
    rows = [{i} for i in range(n)]
    for u, v in edges:
        rows[u].add(v)
    for i in range(n):
        for row in rows:
            if i in row:
                row.update(rows[i])
    return rows


def semantics(choices, closure):
    addresses, counts = [0] * 3, [0] * 3
    tag = False
    for bank, label, _ in choices:
        if bank == 3:
            tag = not tag
        else:
            addresses[bank] ^= label
            counts[bank] += 1
    if any(n % 2 == 0 for n in counts):
        return True
    a, b, c = addresses
    return ((b ^ c) in closure[a ^ b]) == tag


def test(solver):
    # The six editable coordinates include all masks, beyond the intended triples.
    total, no = 0, 0
    for n, r, edges in [(1, 1, []), (2, 1, []), (2, 1, [(0, 1)]),
                        (4, 2, [(0, 1), (1, 2), (2, 1)])]:
        base, offsets = compile_graph(n, r, edges)
        closure = transitive_closure(n, edges)
        keys = list(offsets)

        def check(choices, closure=closure, base=base, offsets=offsets):
            nonlocal total, no
            verdict = semantics(choices, closure)
            assert solve_dimacs(solver, edited(base, offsets, choices)) == verdict
            total += 1
            no += not verdict
            return verdict

        if n <= 2:
            for k in range(len(keys) + 1):
                for choices in combinations(keys, k):
                    check(choices)
        else:
            for k in range(3):
                for choices in combinations(keys, k):
                    assert check(choices)
            rng = Random(94831)
            dense_active = set()
            for _ in range(120):
                chosen = set()
                for bank in range(3):
                    bank_keys = [key for key in keys if key[0] == bank]
                    chosen.update(rng.sample(bank_keys, rng.choice((3, 4, 5, 7))))
                verdict = check(chosen)
                if all(sum(key[0] == j for key in chosen) % 2 for j in range(3)):
                    dense_active.add(verdict)
            assert dense_active == {False, True}
        for s, t in product(range(n), repeat=2):
            touched = set()
            for j, replica in product(range(n), range(r)):
                choices = [(0, s ^ j, replica), (1, j, replica), (2, t ^ j, replica)]
                assert touched.isdisjoint(choices)
                touched.update(choices)
                data = edited(base, offsets, choices)
                assert sum((a ^ b).bit_count() for a, b in zip(base, data)) == 3
                assert check(choices) == (t not in closure[s])
            assert len(touched) == 3 * n * r
    return total, no


def tagged_test(solver):
    radius, pairs, dense, unsat = 0, 0, 0, 0
    for n, r, edges in [(1, 1, []), (2, 1, [(1, 0)]),
                        (4, 2, [(1, 3), (3, 0), (1, 2), (2, 0)])]:
        base, offsets = compile_graph(n, r, edges, tagged=True)
        closure = transitive_closure(n, edges)
        keys = list(offsets)
        for size in range(3):
            for choices in combinations(keys, size):
                assert solve_dimacs(solver, edited(base, offsets, choices))
                radius += 1
        for s, t in product(range(n), repeat=2):
            touched = set()
            for j, replica in product(range(n), range(r)):
                triple = [(0, s ^ j, replica), (1, j, replica), (2, t ^ j, replica)]
                fourth = (3, j, replica)
                four = [*triple, fourth]
                assert touched.isdisjoint(four)
                touched.update(four)
                short, long = edited(base, offsets, triple), edited(base, offsets, four)
                assert sum((a ^ b).bit_count() for a, b in zip(short, long)) == 1
                assert sum((a ^ b).bit_count() for a, b in zip(base, short)) == 3
                assert sum((a ^ b).bit_count() for a, b in zip(base, long)) == 4
                assert solve_dimacs(solver, short) == (t not in closure[s])
                assert solve_dimacs(solver, long) == (t in closure[s])
                pairs += 1
                unsat += 1
            assert len(touched) == 4 * n * r
        if n == 4:
            rng = Random(913195)
            active = set()
            for _ in range(120):
                selected = []
                for bank in range(4):
                    copies = [key for key in keys if key[0] == bank]
                    selected.extend(rng.sample(copies, rng.choice((3, 4, 5, 7))))
                verdict = semantics(selected, closure)
                assert solve_dimacs(solver, edited(base, offsets, selected)) == verdict
                if all(sum(key[0] == j for key in selected) % 2 for j in range(3)):
                    active.add((sum(key[0] == 3 for key in selected) % 2, verdict))
                dense += 1
                unsat += not verdict
            assert len(active) == 4
    return radius, pairs, dense, unsat


def padded_test(solver):
    n, r = 4, 1
    ambient = [(1, 3), (1, 2), (2, 0), (3, 0)]
    empty, sites, positions = compile_padded_dag(n, r, ambient)
    width = (len(empty) * 8).bit_length()
    query_words = {8 * pos // width for pos in sites.values()}
    graph_words = {8 * pos // width for pos in positions.values()}
    assert query_words.isdisjoint(graph_words)
    assert len(query_words) == 4 * n * r and len(graph_words) == len(ambient)
    subgraphs = pairs = 0
    for mask in range(1 << len(ambient)):
        present = [edge for slot, edge in enumerate(ambient) if mask >> slot & 1]
        data, query_offsets, graph_offsets = compile_padded_dag(n, r, ambient, present)
        assert query_offsets == sites and graph_offsets == positions and len(data) == len(empty)
        changed = {i: a ^ b for i, (a, b) in enumerate(zip(empty, data)) if a != b}
        assert changed == {positions[edge]: 1 for edge in present}
        assert solve_dimacs(solver, data)
        closure = transitive_closure(n, present)
        for s, t, j in product(range(n), repeat=3):
            triple = [(0, s ^ j, 0), (1, j, 0), (2, t ^ j, 0)]
            four = [*triple, (3, j, 0)]
            assert solve_dimacs(solver, edited(data, sites, triple)) == (t not in closure[s])
            assert solve_dimacs(solver, edited(data, sites, four)) == (t in closure[s])
            pairs += 1
        subgraphs += 1
    return subgraphs, pairs


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('solver', help='executable accepting DIMACS on stdin and returning 10/20')
    args = parser.parse_args()
    print('proper DIMACS files checked, UNSAT:', test(args.solver))
    print('tagged radius-two files, adjacent pairs, dense masks, UNSAT files:', tagged_test(args.solver))
    print('padded subgraphs, adjacent pairs:', padded_test(args.solver))
