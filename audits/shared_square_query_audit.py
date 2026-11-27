"""Build a shared square CNF for graph queries and flip only named ASCII bits."""

import argparse
from collections import defaultdict
from itertools import combinations, pairwise

from sheet_guard_deletions_audit import (
    CLAUSE_DELETIONS,
    INTACT,
    double_relay_groups,
    local_clauses,
    solve_dimacs,
)


def compile_graph(vertices, edges, sources, sinks, full_cuts, aliases=1, padding=0):
    groups = defaultdict(lambda: ([], []))
    boxes = []
    ports = {}
    tokens = 0

    def square(names):
        nonlocal tokens
        result = tuple(range(tokens, tokens + 4))
        tokens += 4
        for name, token, side in zip(names, result, (0, 1, 1, 0)):
            groups[name][side].append(token)
        return result

    for k, (u, v) in enumerate(edges):
        assert u in vertices and v in vertices
        w = ("implication", k)
        boxes.append(square((u, w, v, w)))

    for role, terminals in (("src", sources), ("dst", sinks)):
        for terminal in terminals:
            for alias in range(aliases):
                key = (role, terminal, alias)
                a = b = terminal
                if full_cuts:
                    if role == "src":
                        b = ("free_zero", terminal, alias)
                    else:
                        a = ("free_one", terminal, alias)
                job = square((a, b, a, b))
                boxes.append(job)
                ports[key] = job[:2]

    # The existing clone compiler takes one distinguished square. Here it is
    # an additional neutral square; all real queries are ordinary old jobs
    # whose original two marked centers will be made intact in the encoding.
    neutral = square((("neutral",),) * 4)
    c, a, b, z = neutral
    tokens = double_relay_groups(groups, boxes, (c, z, b, a), tokens)
    boxes.append(neutral)

    layers = [[{}, {}], [{}, {}]]

    def match(permutation, x, y):
        assert x != y and x not in permutation and y not in permutation
        permutation[x], permutation[y] = y, x

    for left, right in groups.values():
        assert len(left) == len(right) == 2
        for i in range(2):
            match(layers[0][0], left[i], right[i])
            match(layers[0][1], left[i], right[1 - i])
    for c, a, b, z in boxes:
        for i, j in ((c, a), (z, b)):
            match(layers[1][0], i, j)
        for i, j in ((c, b), (z, a)):
            match(layers[1][1], i, j)
    for plus, minus in layers:
        assert len(plus) == len(minus) == tokens
        assert all(plus[minus[i]] != i and plus[minus[plus[minus[i]]]] == i for i in plus)

    id_map, selector = {}, {}
    for j, (key, ends) in enumerate(ports.items(), start=1):
        for k, endpoint in enumerate(ends):
            id_map[endpoint] = 10 * j + k
            selector[endpoint] = (key, k)
    reserved = set(id_map.values())
    free = (i for i in range(1, 5 * tokens + 1) if i not in reserved)
    for t in range(tokens):
        if t not in id_map:
            id_map[t] = next(free)

    # The public IDs need not occupy a contiguous interval. Choose all private
    # names from the remaining dense permutation of [1, 5*tokens].
    private = iter(free)
    rows = []
    locations = {}
    for layer, (plus, minus) in enumerate(layers):
        for i in range(tokens):
            intact = not layer or i in selector
            block = local_clauses(id_map[i], id_map[plus[i]], id_map[minus[i]],
                                  next(private), next(private), INTACT if intact else CLAUSE_DELETIONS)
            if layer and i in selector:
                locations[len(rows) + len(block) - 2] = selector[i]
            rows.extend(block)
    assert next(private, None) is None
    data = bytearray(f"p cnf {5*tokens} {len(rows)}\n".encode())
    offsets = {}
    for j, row in enumerate(rows):
        assert len({abs(x) for x in row}) == 3
        if j in locations:
            data.extend(b" " * padding)
            offsets[locations[j]] = len(data) + len(str(row[0])) - 1
            assert row[0] % 10 in (0, 1)
        data.extend((" ".join(map(str, row)) + " 0\n").encode())
    if padding:
        ordered = sorted(offsets.values())
        assert all(y - x >= padding for x, y in pairwise(ordered))
    return bytes(data), offsets


def reach(edges, start):
    seen = {start}
    for _ in range(len(edges) + 1):
        seen.update(v for u, v in edges if u in seen)
    return seen


def marked_file(base, offsets, choices, full_cuts):
    data = bytearray(base)
    marked = []
    for key in choices:
        arms = (0, 1) if full_cuts else (int(key[0] == "dst"),)
        for arm in arms:
            address = offsets[key, arm]
            assert data[address] in b"01"
            data[address] ^= 1
            marked.append(address)
    assert len(set(marked)) == len(marked)
    return bytes(data)


def audit(executable):
    cases = answers = tested = 0
    for vertices, available, sources, sinks in (
        (range(4), [(0, 2), (0, 3), (1, 2), (1, 3)], (0, 1), (2, 3)),
        (range(5), [(0, 2), (1, 2), (2, 3), (2, 4), (2, 1)], (0, 1), (3, 4)),
    ):
        for num in range(len(available) + 1):
            for edges in combinations(available, num):
                cases += 1
                accessible = {s: reach(edges, s) for s in sources}
                for full in (False, True):
                    base, offsets = compile_graph(vertices, edges, sources, sinks, full)
                    keys = [("src", s, 0) for s in sources] + [("dst", t, 0) for t in sinks]
                    for size in range(len(keys) + 1):
                        for choices in combinations(keys, size):
                            yes = not any(t in accessible[s] for s in sources if ("src", s, 0) in choices
                                          for t in sinks if ("dst", t, 0) in choices)
                            data = marked_file(base, offsets, choices, full)
                            actual = solve_dimacs(executable, data)
                            assert actual == yes, (edges, choices, full)
                            tested += 1
                            answers += yes
    # A pair of edits can use any of three disjoint aliases on either side.
    aliases = 3
    graph = [(0, 2), (1, 2), (2, 3)]
    alias_tests = 0
    for full in (False, True):
        base, offsets = compile_graph(range(5), graph, (0, 1), (3, 4), full, aliases, padding=16)
        for s in (0, 1):
            for t in (3, 4):
                for i in range(aliases):
                    for j in range(aliases):
                        data = marked_file(base, offsets, (("src", s, i), ("dst", t, j)), full)
                        assert solve_dimacs(executable, data) == (t not in reach(graph, s))
                        alias_tests += 1
    print(f"{alias_tests} spaced three-alias encodings, every source/sink alias pair checked")
    print(f"{cases} graphs, {tested} proper DIMACS files, {answers} SAT, {tested-answers} UNSAT")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver", help="path to a solver accepting DIMACS on stdin and returning 10/20")
    audit(parser.parse_args().solver)
