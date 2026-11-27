"""Check circulation predicates and cut ranks without using a graph library."""

from collections import Counter
from itertools import combinations, product
from random import Random


def incidence(n, edges):
    rows = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        rows[u].append(i)
        rows[v].append(i)
    assert all(len(row) == 3 for row in rows)
    return rows


def syndromes(edges):
    # Binary boundary of every edge subset.
    columns = [(1 << u) ^ (1 << v) for u, v in edges]
    out = [0] * (1 << len(edges))
    for mask in range(1, len(out)):
        last = mask & -mask
        out[mask] = out[mask ^ last] ^ columns[last.bit_length() - 1]
    return out


def component_rank(n, edges, mask):
    parts = [{v} for v in range(n)]
    for j, (u, v) in enumerate(edges):
        if mask >> j & 1:
            a = next(part for part in parts if u in part)
            b = next(part for part in parts if v in part)
            if a != b:
                parts.remove(b)
                a.update(b)
    return n - len(parts)


def check_template(rows, q):
    # Each edge selects one shared color/value flag in one varying literal.
    size = sum(map(len, rows)) // 2
    colors = []
    for edge in range(size):
        adjacent = {colors[old] for row in rows if edge in row for old in row if old < edge}
        colors.append(next(color for color in range(5) if color not in adjacent))
    assert all(len({colors[edge] for edge in row}) == 3 for row in rows)
    possible = []
    for banks in product(range(1 << q), repeat=5):
        forbidden = any(((banks[i] >> a) & (banks[j] >> b) & (banks[k] >> (a ^ b)) & 1)
                        for i, j, k in combinations(range(5), 3)
                        for a in range(q) for b in range(q))
        if not forbidden:
            possible.append(banks)
    checked = 0
    for data in product(range(q), repeat=size):
        hits = any((data[i] ^ data[j] ^ data[k]) != 0 for i, j, k in rows)
        # A selected row must force all three edge selectors and their flags.
        actual = any(all((banks[colors[edge]] >> data[edge]) & 1 for edge in row)
                     for banks in possible for row in rows)
        assert actual == hits
        checked += 1
    return checked


def check(n, edges):
    size = len(edges)
    full = (1 << size) - 1
    rows = incidence(n, edges)
    syn = syndromes(edges)
    code = [m for m, val in enumerate(syn) if val == 0]
    assert len(code) == 1 << (size - n + 1)
    ranks = [component_rank(n, edges, m) for m in range(full + 1)]
    dims = [m.bit_count() - r for m, r in enumerate(ranks)]
    balanced = 0
    for a in range(full + 1):
        b = full ^ a
        lam = ranks[a] + ranks[b] - ranks[full]
        # Conditional on a circulation, compute actual boundary syndromes.
        counts = Counter(syn[x & a] for x in code)
        assert len(counts) == (1 << lam) and len(set(counts.values())) == 1
        if 3 * min(a.bit_count(), b.bit_count()) >= size and min(a.bit_count(), b.bit_count()) > 1:
            shared = sum(any(a >> j & 1 for j in row) and any(b >> j & 1 for j in row)
                         for row in rows)
            assert 6 * (lam - 1) >= shared
            balanced += 1
    random = Random(839867 + n)
    for _ in range(100):
        nodes = [1 << i for i in range(size)]
        total = 0
        while len(nodes) > 1:
            a = nodes.pop(random.randrange(len(nodes)))
            b = nodes.pop(random.randrange(len(nodes)))
            total += dims[a | b] - dims[a] - dims[b]
            nodes.append(a | b)
        assert total == dims[full]
    return balanced


def fixed_outside(edges):
    """Count permitted rows/columns and rectangles in all nonempty fibers."""
    syn = syndromes(edges)
    size = len(edges)
    full = (1 << size) - 1
    code = [m for m, val in enumerate(syn) if val == 0]
    dims = [sum(x & m == x for x in code).bit_length()-1 for m in range(full+1)]
    count = 0
    for roles in product(range(3), repeat=size):
        a = sum(1 << i for i, role in enumerate(roles) if role == 0)
        b = sum(1 << i for i, role in enumerate(roles) if role == 1)
        outside = full ^ (a | b)
        gain = dims[a | b] - dims[a] - dims[b]
        for value in {x & outside for x in code}:
            pairs = {(x & a, x & b) for x in code if x & outside == value}
            rows = {left for left, _ in pairs}
            neighborhoods = {frozenset(right for u, right in pairs if u == left) for left in rows}
            assert len(neighborhoods) == 1 << gain
            assert all(one.isdisjoint(two) for one, two in combinations(neighborhoods, 2))
            count += 1
    return count


def read_intervals():
    """Check the exact charge to consecutive probes on each finite read trace."""
    tested = 0
    for trace in product(range(4), repeat=7):
        if len(set(trace)) != 4:
            continue
        first = {edge: trace.index(edge) for edge in range(4)}
        # With s=4 the balanced cut is just before the third new word.
        cuts = sorted(first.values())[2:3]
        cross = sum(len(set(trace[:cut]) & set(trace[cut:])) for cut in cuts)
        spans = []
        for edge in range(4):
            visits = [i for i, value in enumerate(trace) if value == edge]
            spans.extend(sum(a < cut <= b for cut in cuts) for a, b in zip(visits, visits[1:]))
        assert cross == sum(spans) <= max(spans, default=0) * len(spans)
        tested += 1
    return tested


if __name__ == "__main__":
    tetrahedron = list(combinations(range(4), 2))
    bipartite = [(u, v) for u in range(3) for v in range(3, 6)]
    cube = [(u, u ^ (1 << bit)) for u in range(8) for bit in range(3) if not (u >> bit & 1)]
    cases = sum(check(n, edges) for n, edges in [(4, tetrahedron), (6, bipartite), (8, cube)])
    templates = check_template(incidence(4, tetrahedron), 2)
    fibers = fixed_outside(tetrahedron)
    traces = read_intervals()
    print(f"{cases} balanced splits, {templates} clause inputs, {fibers} conditioned fibers, {traces} read traces")
