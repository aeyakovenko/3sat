"""Check isolated shared-address read cuts over prime fields and graph partitions."""

from itertools import combinations
from random import Random


def rank_mod(rows, prime):
    basis = {}
    for row in rows:
        reduced = list(row)
        while any(reduced):
            pivot = next(j for j, x in enumerate(reduced) if x)
            if pivot not in basis:
                scale = pow(reduced[pivot], -1, prime)
                basis[pivot] = [x * scale % prime for x in reduced]
                break
            scale = reduced[pivot]
            reduced = [(x - scale*y) % prime for x, y in zip(reduced, basis[pivot])]
    return len(basis)


def slice_word(bits, positions):
    return sum(((bits >> at) & 1) << j for j, at in enumerate(positions))


def audit_cut(m, w, left):
    table = m*w
    left = set(left)
    right = [x for x in range(table + (m.bit_length()-1) + w) if x not in left]
    selected = [[lane for lane in range(w) if i*w+lane in left] for i in range(m)]
    channels = [(i, u) for i in range(m) for u in range(1, 1 << len(selected[i]))]
    rows = [[0]*(1 << len(right)) for _ in range(1 << len(left))]
    word_mask = (1 << w)-1
    for bits in range(1 << (table + (m.bit_length()-1) + w)):
        address = (bits >> table) & (m-1)
        answer = (bits >> (table + (m.bit_length()-1))) & word_mask
        word = (bits >> (address*w)) & word_mask
        direct = int(word == answer)
        rows[slice_word(bits, sorted(left))][slice_word(bits, right)] = direct
        mask = sum(1 << lane for lane in selected[address])
        base = int((answer & mask) == 0)
        rest = int(((word ^ answer) & (word_mask ^ mask)) == 0)
        # Contract the default and the single nonzero left payload for this row.
        value = slice_word(word, selected[address])
        target = slice_word(answer, selected[address])
        via_channels = rest * (base + (int(target == value)-base if value else 0))
        assert via_channels == direct
    expected = 1+len(channels)
    for p in (2, 3, 5):
        assert rank_mod(rows, p) == expected
    return expected


def quartet():
    for side in combinations(range(1, 4), 1):
        left = [0, *side]
        right = sorted(set(range(4)) - set(left))
        rows = [[0]*4 for _ in range(4)]
        for bits in range(16):
            addr, x0, x1, y = [(bits >> i) & 1 for i in range(4)]
            rows[slice_word(bits,left)][slice_word(bits,right)] = int((x1 if addr else x0) == y)
        for prime in (2, 3, 5):
            assert rank_mod(rows, prime) == 3


def spanning_buckets(edges, terminals, control, rng):
    """Cut a random spanning tree, mark cotree half-edges and inspect each region."""
    n = 1 + max(max(e) for e in edges)
    tree = [set() for _ in range(n)]
    original = [set() for _ in range(n)]
    parent = list(range(n))

    def root(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    def add(adj, x, y):
        adj[x].add(y)
        adj[y].add(x)

    marked = set(control)
    order = list(edges)
    rng.shuffle(order)
    for x, y in order:
        add(original, x, y)
        a, b = root(x), root(y)
        if a != b:
            parent[b] = a
            add(tree, x, y)
        else:
            for v in (x, y):
                leaf = len(tree)
                tree.append(set())
                add(tree, v, leaf)
                marked.add(leaf)
    hull = set(range(len(tree)))
    degree = list(map(len, tree))
    remove = [v for v in hull - marked if degree[v] <= 1]
    while remove:
        v = remove.pop()
        hull.remove(v)
        for u in tree[v] & hull:
            degree[u] -= 1
            if degree[u] == 1 and u not in marked:
                remove.append(u)

    ends = {v for v in hull if len(tree[v] & hull) != 2}
    assert marked <= ends
    regions = []
    for first in ends:
        for nxt in tree[first] & hull:
            prev, curr = first, nxt
            path = set()
            while curr not in ends:
                path.add(curr)
                prev, curr = curr, next(iter((tree[curr] & hull) - {prev}))
            if curr < first:
                continue
            region = set(path)
            stack = list(path)
            while stack:
                for other in tree[stack.pop()] - hull - region:
                    region.add(other)
                    stack.append(other)
            assert not (region & marked)
            boundary = sum(len(original[v] - region) for v in region)
            assert boundary <= 2
            regions.append(region & terminals)
    data = terminals - control
    assert set.union(*regions) == data
    assert sum(map(len, regions)) == len(data)
    assert len(regions) <= 2*len(marked)-3
    if len(data) > 3*(2*len(marked)-3):
        assert max(map(len, regions)) >= 4
    return len(regions)


def sample_graph(nleaves, cycles, rng):
    edges = [(0, 1)]
    terminals = {0, 1}
    next_id = 2
    for _ in range(2, nleaves):
        x, y = edges.pop(rng.randrange(len(edges)))
        mid, leaf = next_id, next_id+1
        next_id += 2
        edges.extend(((x,mid),(y,mid),(mid,leaf)))
        terminals.add(leaf)
    for _ in range(cycles):
        i, j = sorted(rng.sample(range(len(edges)), 2), reverse=True)
        a, b = edges.pop(i)
        c, d = edges.pop(j)
        u, v = next_id, next_id+1
        next_id += 2
        edges.extend(((a,u),(b,u),(c,v),(d,v),(u,v)))
    return edges, terminals


def main():
    quartet()
    cuts = 0
    for m, w in ((1,2), (2,1), (2,2), (2,3), (4,1)):
        for mask in range(1 << (m*w)):
            left = [i for i in range(m*w) if mask >> i & 1]
            audit_cut(m, w, left)
            cuts += 1
    for left in (range(8), range(0,8,2), (0, 2, 5), (0, 1, 2, 3)):
        audit_cut(4, 2, left)
        cuts += 1
    rng = Random(7428)
    samples = 0
    for nleaves in (4, 12, 48, 120):
        for cycles in range(6):
            edges, leaves = sample_graph(nleaves, cycles, rng)
            for _ in range(10):
                control = set(rng.sample(sorted(leaves), rng.randrange(2, min(10,nleaves)+1)))
                spanning_buckets(edges, leaves, control, rng)
                samples += 1
    print(f"{cuts} bit cuts over F2, F3, F5; all three quartet cuts; {samples} graph decompositions")


if __name__ == '__main__':
    main()
