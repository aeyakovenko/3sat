"""Check contraction and branch feasibility against complete assignments on cubic multigraphs."""
from collections import defaultdict
from itertools import combinations, product
from random import Random


def graph_components(vertices, links):
    unseen = set(vertices)
    while unseen:
        first = unseen.pop()
        stack = [first]
        part = []
        while stack:
            v = stack.pop()
            part.append(v)
            for u in links[v]:
                if u in unseen:
                    unseen.remove(u)
                    stack.append(u)
        yield part


def classify(forbidden):
    counts = [sum(x.bit_count() % 2 == p for x in forbidden) for p in range(2)]
    major = int(counts[1] > counts[0])
    assert len(forbidden) == 4
    if counts[major] == 4:
        return 1-major, None
    assert counts[major] == 3
    removed, = {x for x in range(8) if x.bit_count() % 2 == major} - forbidden
    added, = {x for x in forbidden if x.bit_count() % 2 != major}
    flip = added ^ removed
    assert flip.bit_count() == 1
    return 1-major, flip.bit_length()-1


def row_feasible(rows):
    endpoints = defaultdict(list)
    for i, (variables, rhs) in enumerate(rows):
        for e in variables:
            endpoints[e].append(i)
    links = defaultdict(list)
    open_rows = set()
    for ends in endpoints.values():
        if len(ends) == 1:
            open_rows.add(ends[0])
        else:
            u, v = ends
            links[u].append(v)
            links[v].append(u)
    return all(any(v in open_rows for v in comp) or sum(rows[v][1] for v in comp) % 2 == 0
               for comp in graph_components(range(len(rows)), links))


def solve(support, forbidden, edges):
    clean = set()
    dirty = {}
    charge = {}
    for v, table in enumerate(forbidden):
        charge[v], out = classify(table)
        if out is None:
            clean.add(v)
        else:
            dirty[v] = out
    links = defaultdict(list)
    for u, v in edges:
        if u in clean and v in clean:
            links[u].append(v)
            links[v].append(u)
    checks = []
    for comp in graph_components(clean, links):
        inside = set(comp)
        boundary = [e for e, (u,v) in enumerate(edges) if (u in inside) != (v in inside)]
        checks.append((boundary, sum(charge[v] for v in comp) % 2))

    inputs = [set(row)-{row[dirty[v]]} for v, row in enumerate(support) if v in dirty]
    # Here instances are tiny. Among all choices of one input per gate find
    # a choice minimizing their union, independently of the matching lemma.
    pins = min((set(choice) for choice in product(*inputs)), key=len)
    eligible = [(u, v) for e, (u,v) in enumerate(edges) if u in dirty and v in dirty
                and support[u][dirty[u]] != e and support[v][dirty[v]] != e]
    largest = max(len(m) for size in range(len(dirty)//2+1) for m in combinations(eligible,size)
                  if len(set(u for ends in m for u in ends)) == 2*len(m))
    assert len(pins) == len(dirty)-largest
    for bits in product((0,1), repeat=len(pins)):
        fixed = dict(zip(sorted(pins), bits))
        rows = [(list(vs), b) for vs, b in checks]
        for v, out in dirty.items():
            vs = support[v]
            first, second = [e for i,e in enumerate(vs) if i != out]
            if first not in fixed:
                first, second = second, first
            values = []
            for bit in (0,1):
                local = {first:fixed[first], second:bit}
                possible = []
                for y in (0,1):
                    local[vs[out]] = y
                    index = sum(local[e]<<i for i,e in enumerate(vs))
                    if index not in forbidden[v]:
                        possible.append(y)
                assert len(possible) == 1
                values.append(possible[0])
            rows.append(([vs[out]] + ([second] if values[0] != values[1] else []), values[0]))
        reduced = []
        for vs, b in rows:
            reduced.append(([e for e in vs if e not in fixed],
                            (b + sum(fixed[e] for e in vs if e in fixed)) % 2))
        if row_feasible(reduced):
            return True
    return False


def main():
    rng = Random(251126)
    supports = [
        [(0,1)] * 3,
        list(combinations(range(4),2)),
        [(0,1),(0,1),(2,3),(2,3),(0,2),(1,3)],
        [(0,1)]*3 + [(2,3)]*3,
        [(i,(i+1)%6) for i in range(6)] + [(0,3),(1,4),(2,5)],
    ]
    solved = 0
    for edges in supports:
        names = [[] for _ in range(max(max(e) for e in edges)+1)]
        for e,(u,v) in enumerate(edges):
            names[u].append(e)
            names[v].append(e)
        assert all(len(set(row))==3 for row in names)
        for _ in range(200):
            forbidden = []
            for v in names:
                parity = rng.randrange(2)
                table = {x for x in range(8) if x.bit_count()%2 == parity}
                if rng.randrange(2):
                    x = rng.choice(sorted(table))
                    table.remove(x)
                    table.add(x ^ (1<<rng.randrange(3)))
                forbidden.append(table)
            expected = any(all(sum(((assignment>>e)&1)<<i for i,e in enumerate(row)) not in forbidden[v]
                               for v,row in enumerate(names))
                           for assignment in range(1<<len(edges)))
            assert solve(names,forbidden,edges) == expected
            solved += 1
    print(f"{solved} cubic networks: pin matching, contracted equations and verdicts checked.")


if __name__ == "__main__":
    main()
