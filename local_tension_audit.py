"""Check bounded-dependency coloring extensions and their ternary interval equations."""

import dataclasses
import itertools
from collections import Counter

from simple_permutation_successor import successor
from two_hamilton_paths_sat_audit import (
    NEUTRAL_COLORINGS,
    cycle_edges,
    encode,
    switchable_edges,
    switched_order,
)


def locally_extend(enc, source):
    h = [None] * len(enc.blue)
    for x, p in zip(source, enc.ports):
        h[p] = x
    for own, u, v, dt, tail in enc.splitters:
        h[dt] = h[tail] = x = source[own]
        h[u], h[v] = [c for c in range(3) if c != x]
    k = enc.first_block
    ext = {j: [] for j in range(k, len(h)) if (j - k) % 7 in [0, 6]}
    for order in [enc.red, enc.blue]:
        for a, b in cycle_edges(order):
            if a >= k and b >= k and (a - k) // 7 == (b - k) // 7:
                continue
            if a in ext:
                ext[a].append(b)
            if b in ext:
                ext[b].append(a)
    pr = {}
    for a, neighbors in ext.items():
        assert len(neighbors) == 2
        pr[a] = min(set(range(3)) - {pr.get(b, -1) for b in neighbors})
    for i in range(3):
        for a, neighbors in ext.items():
            if pr[a] == i:
                h[a] = min(set(range(3)) - {h[b] for b in neighbors})
    for a in range(k, len(h), 7):
        h[a : a + 7] = NEUTRAL_COLORINGS[h[a], h[a + 6]]
    p = enc.permutation()
    old = [h[j] for j in enc.red]
    assert p[0] == 0 and len(old) % 2 == 0
    for a, b in list(itertools.pairwise(old)) + [
        (old[i], old[j]) for i, j in itertools.pairwise(p)
    ]:
        assert a != b
    u = min(set(range(3)) - {old[-1], old[p[-1]]})
    v = min(set(range(3)) - {u, old[0]})
    f = old + [u, v]
    new = [(f[0] - 1) % 3]
    for i, x in enumerate(f):
        e = 1 - 2 * (i % 2)
        new.extend(t % 3 for t in (x, x + e, x - e, x, x + e, x - e, x))
    new.append(f[0])
    q = successor(p)
    bs = [(b - a - 1) % 3 for a, b in itertools.pairwise(new)]
    assert set(bs) <= {0, 1}
    S = [0]
    for b in bs:
        S.append((S[-1] + 1 + b) % 3)
    for i, j in itertools.pairwise(q):
        assert (S[max(i, j)] - S[min(i, j)]) ** 2 % 3 == 1
    return len(new)


cn = Counter()
for n in range(1, 5):
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = [e for j, e in enumerate(pairs) if mask >> j & 1]
        enc = encode(n + n % 2, edges)
        for source in itertools.product(range(3), repeat=n):
            if any(source[i] == source[j] for i, j in edges):
                continue
            L = locally_extend(enc, source + (0,) * (n % 2))
            cn["proper-source-tests"] += 1
            cn["blue-interval-equations"] += L - 1
print(cn)

cn = Counter()
edges = list(itertools.combinations(range(4), 2))
e, sw = switchable_edges(4, edges)
for mask in range(1 << len(edges)):
    off = {i for i in range(len(edges)) if mask >> i & 1}
    blue = switched_order(e.blue, sw, off)
    rel = dict(zip(e.blue, blue))
    splitters = [(o, u, v, rel[d], t) for o, u, v, d, t in e.splitters]
    enc = dataclasses.replace(e, blue=blue, splitters=splitters)
    for s in itertools.product(range(3), repeat=4):
        if not all(s[a] != s[b] for j, (a, b) in enumerate(edges) if j not in off):
            continue
        val = list(s)
        for i, (a, b) in enumerate(edges):
            if i in off:
                val.extend((int(s[b] == 0), int(s[a] == 0)))
            else:
                val.extend((0, 1))
        L = locally_extend(enc, val)
        cn["switch-mask-colouring-tests"] += 1
        cn["blue-interval-equations"] += L - 1
print(cn)
