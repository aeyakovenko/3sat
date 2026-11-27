"""Finite comparisons for degree-four obstruction and kernel bounds."""
from itertools import combinations
from random import Random

import networkx as nx

from threshold_port_coloring_audit import capped_diamonds, colorable, make_paths, quotient


def gallai_component(graph):
    for vertices in nx.biconnected_components(graph):
        block = graph.subgraph(vertices)
        n = len(block)
        complete = 2 * block.number_of_edges() == n * (n-1)
        odd_cycle = n % 2 and all(d == 2 for _, d in block.degree())
        if not complete and not odd_cycle:
            return False
    return True


def kernel(graph):
    core = graph.copy()
    while True:
        peeled = [v for v, d in core.degree() if d <= 2]
        if not peeled:
            break
        core.remove_nodes_from(peeled)
    high = {v for v, d in core.degree() if d == 4}
    lows = core.subgraph(set(core) - high)
    keep = set(high)
    comps = 0
    for vertices in nx.connected_components(lows):
        part = lows.subgraph(vertices)
        if not gallai_component(part):
            continue
        if len(part) == 4 and part.number_of_edges() == 6:
            return nx.complete_graph(4)
        keep.update(vertices)
        comps += 1
    output = core.subgraph(keep)
    assert len(output) + 6*comps <= 13*len(high)
    assert output.number_of_edges() + 9*comps <= 20*len(high)
    return output


def critical_subgraph(graph):
    core = graph.copy()
    for u, v in list(core.edges()):
        core.remove_edge(u, v)
        if colorable(core.edges()):
            core.add_edge(u, v)
    core.remove_nodes_from(list(nx.isolates(core)))
    return core


def check_graph(graph):
    expected = colorable(graph.edges())
    assert colorable(kernel(graph).edges()) == expected
    if expected:
        return 0
    critical = critical_subgraph(graph)
    k = sum(d == 4 for _, d in graph.degree())
    assert len(critical) <= 3*k+4
    assert critical.number_of_edges() <= 5*k+6
    edges = list(graph.edges())
    rows, endpoints = make_paths(max(graph)+1, edges)
    keep = [r for r in rows if endpoints[r[0]] in critical]
    assert len(keep) <= 7*k+8
    assert not colorable(quotient(len(edges), keep))
    return 1


def join_ore(left, right, edge, split, moved):
    # Give the second piece fresh labels. Its split neighbors are then sent
    # to the two terminals of the deleted edge in the first piece.
    result = left.copy()
    u, v = edge
    result.remove_edge(u, v)
    offset = max(left)+1
    for a, b in right.edges():
        if a == split or b == split:
            other = b if a == split else a
            result.add_edge(u if other in moved else v, other+offset)
        else:
            result.add_edge(a+offset, b+offset)
    return result


def main():
    atlas = [g for g in nx.graph_atlas_g() if all(d <= 4 for _, d in g.degree())]
    negatives = sum(check_graph(g) for g in atlas)
    print(f'{len(atlas)} atlas graphs checked; {negatives} have uncolorable row sublists')
    rng = Random(914)
    ore = nx.complete_graph(4)
    joins = 0
    for _ in range(6):
        right = nx.complete_graph(4)
        options = [(edge, set(moved)) for edge in ore.edges()
                   for size in (1, 2) for moved in combinations((1,2,3), size)
                   if ore.degree(edge[0])-1+size <= 4
                   and ore.degree(edge[1])-1+3-size <= 4]
        edge, moved = rng.choice(options)
        ore = join_ore(ore, right, edge, 0, moved)
        assert check_graph(ore) == 1
        assert 3*ore.number_of_edges() == 5*len(ore)-2
        joins += 1
    print(f'{joins} bounded-degree Ore compositions checked')
    for k in range(8):
        n, edges = capped_diamonds(k+1)
        rows, _ = make_paths(n, edges)
        assert len(rows) == 7*k+8 and n == 3*k+4 and len(edges) == 5*k+6
        assert not colorable(quotient(len(edges), rows))
        for i in range(len(rows)):
            assert colorable(quotient(len(edges), rows[:i] + rows[i+1:]))
    print('sharp at k=0 through 7, including every individual row deletion')


if __name__ == '__main__':
    main()
