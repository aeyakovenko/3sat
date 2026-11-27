"""Enumerate actual permutation exact covers and their conflict graphs.
Requires pycosat and networkx. The finite audit normalizes by augmenting-path
matching; the manuscript uses the linear-time edge-coloring theorem.
"""

from collections import Counter, defaultdict
from itertools import product
from random import Random

import networkx as nx
import pycosat


def dag_for(clauses):
    graph = nx.DiGraph()
    colors, default_checks = {}, []

    def fresh(color=None):
        v = len(colors)
        graph.add_node(v)
        colors[v] = ('single', v) if color is None else color
        return v

    def lane(start, members, end):
        vertices = [start, *members, end]
        for u, v in zip(vertices, vertices[1:]):
            assert u != v and not graph.has_edge(u, v)
            graph.add_edge(u, v)
        return vertices

    def alternatives(start, members, end):
        if len(members) == 1:
            return [lane(start, members[0], end)]
        if len(members) == 2:
            return [lane(start, branch, end) for branch in members]
        second_fork, second_merge = fresh(), fresh()
        left = lane(start, members[0], end)
        graph.add_edge(start, second_fork)
        graph.add_edge(second_merge, end)
        rest = alternatives(second_fork, members[1:], second_merge)
        return [left] + [[start, *path, end] for path in rest]

    # Empty clauses are handled by returning a fixed false formula beforehand.
    source, entry, sink = fresh(), fresh(), fresh()
    graph.add_edge(source, entry)
    stages = []
    checks = {}
    variable_blockers = defaultdict(lambda: [[], []])
    for j, clause in enumerate(clauses):
        for step, literal in enumerate(clause):
            demands = [-jlit for jlit in clause[:step]] + [literal]
            checks[j, step] = []
            for d, demanded in enumerate(demands):
                color = ('pair', j, step, d)
                blocker, gate = fresh(color), fresh(color)
                value = int(demanded < 0)  # assignment on which the demand is false
                variable_blockers[abs(demanded)][value].append(blocker)
                checks[j, step].append(gate)
                if step == 0:
                    default_checks.append(color)
    root = entry
    for name in sorted(variable_blockers):
        end = fresh()
        paths = []
        for value in (0, 1):
            marker = fresh()
            paths.append([marker, *variable_blockers[name][value]])
        stages.append((name, alternatives(root, paths, end)))
        root = end
    for j, clause in enumerate(clauses):
        end = fresh()
        paths = alternatives(root, [checks[j, i] for i in range(len(clause))], end)
        stages.append((clause, paths))
        root = end
    graph.add_edge(root, sink)
    bypass_color = ('bypass',)
    bypass = lane(source, [fresh(bypass_color), fresh(), fresh(bypass_color)], sink)
    assert nx.is_directed_acyclic_graph(graph)
    assert max(dict(graph.in_degree()).values()) <= 2 and max(dict(graph.out_degree()).values()) <= 2
    for v in graph:
        if colors[v][0] != 'single':
            assert graph.in_degree(v) == graph.out_degree(v) == 1
    return graph, colors, source, entry, sink, stages, bypass, default_checks


def packing_from(graph, colors, source, sink):
    groups, slot = defaultdict(list), {}
    for v, color in colors.items():
        if v != source:
            groups[color].append(v)
    triples = {}
    point = 0
    for color, ports in groups.items():
        assert len(ports) in (1, 2)
        triples['old', color] = (point, point+1, point+2)
        for j, v in enumerate(ports):
            slot[v] = point+j
        point += 3
    slot[source] = point
    holes = {point, point+1, point+2}
    packed = set(triples)
    for u, v in graph.edges:
        assert colors[u] != colors[v]
        base = triples['old', colors[v]]
        triples['arc', u, v] = tuple(r for r in base if r != slot[v]) + (slot[u],)
    triples['terminal',] = (slot[sink], point+1, point+2)
    point += 3
    degree = Counter(r for col in triples.values() for r in col)
    assert all(1 <= degree[r] <= 3 for r in range(point))
    missing = [r for r in range(point) for _ in range(3-degree[r])]
    assert len(missing) % 3 == 0
    for j in range(0, len(missing), 3):
        for k in range(3):
            triples['filler', j, k] = (missing[j+k], point+k, point+(k+1)%3)
        t = ('fixed', j)
        triples[t] = (point, point+1, point+2)
        packed.add(t)
        point += 3
    assert len(triples) == point
    assert len({frozenset(col) for col in triples.values()}) == point
    assert all(len(set(col)) == 3 for col in triples.values())
    assert Counter(r for col in triples.values() for r in col) == {r: 3 for r in range(point)}
    coverage = Counter(r for key in packed for r in triples[key])
    assert all(coverage[r] == int(r not in holes) for r in range(point))
    return triples, packed, holes


def normalize(triples):
    n = len(triples)
    ids = dict(enumerate(triples))
    graph = nx.Graph()
    graph.add_nodes_from(range(2*n))
    for j, key in ids.items():
        graph.add_edges_from((v, n+j) for v in triples[key])
    matchings = []
    for _ in range(3):
        matching = nx.bipartite.maximum_matching(graph, top_nodes=range(n))
        m = tuple(matching[i]-n for i in range(n))
        assert len(set(m)) == n
        matchings.append(m)
        graph.remove_edges_from((i, n+j) for i, j in enumerate(m))
    first, second, third = matchings
    inv = {j: i for i, j in enumerate(first)}
    p, q = [tuple(inv[j] for j in m) for m in (second, third)]
    assert sorted(p) == sorted(q) == list(range(n))
    row_cols = list(zip(range(n), p, q))
    assert all(len(set(row)) == 3 for row in row_cols)
    return row_cols, [ids[j] for j in first]


def route_weights(path, colors, triples, packed, boolean):
    result = dict.fromkeys(triples, 0)
    for key in packed:
        result[key] = 1
    result['terminal',] = 1
    for u, v in zip(path, path[1:]):
        result['arc', u, v] = 1
        old = ('old', colors[v])
        result[old] = 0 if boolean else result[old]-1
    return result


def residual(row_cols, keys, vector):
    return [sum(vector[keys[j]] for j in row)-1 for row in row_cols]


def audit_formula(clauses):
    graph, colors, source, entry, sink, stages, bypass, defaults = dag_for(clauses)
    triples, packed, holes = packing_from(graph, colors, source, sink)
    rows, keys = normalize(triples)
    y = route_weights(bypass, colors, triples, packed, False)
    assert set(y.values()) == {-1, 0, 1} and sum(v == -1 for v in y.values()) == 1
    assert set(residual(rows, keys, y)) == {0}
    exact = []
    for row in rows:
        a, b, c = [1+i for i in row]
        exact.extend([(a,b,c), (-a,-b), (-a,-c), (-b,-c)])
    seen = set()
    assignment_count = 0
    source_vars = sorted({abs(lit) for clause in clauses for lit in clause})
    for bits in product((0, 1), repeat=len(source_vars)):
        values = dict(zip(source_vars, bits))
        bad = []
        path = [source, entry]
        for key, options in stages:
            if isinstance(key, int):
                index = values[key]
            else:
                truth = [values[abs(lit)] ^ int(lit < 0) for lit in key]
                index = next((i for i,b in enumerate(truth) if b), 0)
                bad.append(not any(truth))
            path.extend(options[index][1:])
        path.append(sink)
        vector = route_weights(path, colors, triples, packed, True)
        for variable, options in stages:
            if isinstance(variable, int):
                first, marker = options[1][:2]
                assert vector['arc', first, marker] == values[variable]
        failures = {r for j, failed in enumerate(bad) if failed for r in triples['old', defaults[j]]}
        assert residual(rows, keys, vector) == [int(r in failures) for r in range(len(rows))]
        if not any(bad):
            seen.add(frozenset(key for key, bit in vector.items() if bit))
        assignment_count += 1

    models = 0
    for m in pycosat.itersolve(exact, vars=len(rows)):
        selected = frozenset(keys[v-1] for v in m if v > 0)
        assert selected in seen
        seen.remove(selected)
        removed, added = packed-selected, selected-packed
        conflict = nx.Graph()
        conflict.add_nodes_from(removed | added)
        for old in removed:
            for new in added:
                count = len(set(triples[old]) & set(triples[new]))
                if count:
                    conflict.add_edge(old, new, size=count)
        assert nx.is_connected(conflict) and nx.is_tree(conflict)
        assert sorted(dict(conflict.degree()).values()) == [1, 1] + [2]*(len(conflict)-2)
        assert sum(w['size'] for _, _, w in conflict.edges(data=True)) == 3*len(removed)
        assert all(sum(r in triples[key] for key in added) == 1 for r in holes)
        models += 1
    assert not seen
    return assignment_count, models, len(rows)


if __name__ == '__main__':
    lits = (-2, -1, 1, 2)
    clauses = [(v,) for v in lits] + list(product(lits, repeat=2)) + list(product(lits, repeat=3))
    suite = [()] + [(row,) for row in clauses] + list(product([(v,) for v in lits], repeat=2))
    rng = Random(7523)
    for _ in range(68):
        suite.append(tuple(rng.choice(clauses) for _ in range(rng.randint(2, 4))))
    results = [audit_formula(tuple(dict.fromkeys(f))) for f in suite]
    print('formulas:', len(results), 'tentative assignments:', sum(r[0] for r in results))
    print('all perfect covers/path repairs:', sum(r[1] for r in results), 'largest permutation:', max(r[2] for r in results))
