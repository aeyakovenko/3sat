"""Audit the cubic parity growth examples. Requires pycosat."""
from itertools import product
from math import comb

import pycosat


def block_layout(k):
    blocks = [[(i, j) for j in range(k) if i != j] for i in range(k)]
    cycle = [v for block in blocks for v in block]
    chords = [((i, j), (j, i)) for i in range(k) for j in range(i)]
    return blocks, cycle, chords


def check_history(cycle, chords):
    """Insert matched pairs in the target cyclic order from a two-vertex seed."""
    kept = set(chords[0])
    previous = [v for v in cycle if v in kept]
    for pair in chords[1:]:
        assert not kept.intersection(pair)
        kept.update(pair)
        current = [v for v in cycle if v in kept]
        assert [v for v in current if v not in pair] == previous
        previous = current
    assert previous == cycle


def encode(cycle, chords, charges):
    edges = [(v, cycle[(i+1) % len(cycle)]) for i, v in enumerate(cycle)] + chords
    incident = {v: [] for v in cycle}
    for index, (u, v) in enumerate(edges, start=1):
        assert u != v
        incident[u].append(index)
        incident[v].append(index)
    clauses = []
    for v in cycle:
        names = incident[v]
        assert len(set(names)) == 3
        for a in product((0, 1), repeat=3):
            if sum(a) % 2 != charges[v]:
                clauses.append([var if bit == 0 else -var for var, bit in zip(names, a)])
    return clauses, edges


def check_minors(blocks, cycle, edges):
    vertex_block = {v: i for i, block in enumerate(blocks) for v in block}
    crossing = {tuple(sorted((vertex_block[u], vertex_block[v]))) for u, v in edges
                if vertex_block[u] != vertex_block[v]}
    assert len(crossing) == comb(len(blocks), 2)
    owner = [v for _, v in edges[:len(cycle)]] + [u for u, _ in edges[len(cycle):]]
    groups = {v: set() for v in cycle}
    for index, v in enumerate(owner):
        groups[v].add(index)
    for v, group in groups.items():
        assert group and all(v in edges[e] for e in group)
    for u, v in edges:
        assert any(set(edges[e]).intersection(edges[f])
                   for e in groups[u] for f in groups[v])


def check_formulas(cycle, chords):
    odd = {v: int(v == cycle[0]) for v in cycle}
    cnf, edges = encode(cycle, chords, odd)
    assert pycosat.solve(cnf) == "UNSAT"
    for j in range(len(cnf)):
        assert isinstance(pycosat.solve(cnf[:j] + cnf[j+1:]), list)
    odd[cycle[-1]] ^= 1
    even, _ = encode(cycle, chords, odd)
    assert isinstance(pycosat.solve(even), list)
    return edges, len(cnf)


def main():
    _, tested = check_formulas([0, 1], [(0, 1)])
    for k in range(3, 9):
        blocks, cycle, chords = block_layout(k)
        check_history(cycle, chords)
        edges, clauses = check_formulas(cycle, chords)
        check_minors(blocks, cycle, edges)
        assert clauses == 4*k*(k-1) and len(edges) == 3*k*(k-1)//2
        tested += clauses
    print("Seed and six clique-minor layouts verified;", tested, "single-clause deletions SAT")


if __name__ == "__main__":
    main()
