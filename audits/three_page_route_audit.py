"""Finite verification of forward paths in the three-page layered and port layouts."""

from itertools import combinations, product
from random import Random


def monotone_maps(width):
    labels = range(width)
    return [tuple(zip(domain, image)) for size in range(width+1)
            for domain in combinations(labels, size) for image in combinations(labels, size)]


def check_pages(size, pages, has_spine=False):
    assert len(pages) == 3
    seen = set()
    for edges in pages:
        endpoints = set()
        closing = []
        for u, v in sorted(edges):
            assert 0 <= u < v < size and u not in endpoints and v not in endpoints
            endpoints.update((u, v))
            while closing and closing[-1] < u:
                closing.pop()
            assert not closing or v < closing[-1]
            closing.append(v)
            assert (u, v) not in seen
            seen.add((u, v))
    if has_spine:
        assert all((v, v+1) in seen for v in range(size-1))


def micro_layout(width, transitions):
    degree = len(transitions[0])
    period = 2*degree
    size = (len(transitions)*period+1)*width

    def position(t, x):
        return t*width + (width-1-x if t % 2 else x)

    pages = [set() for _ in range(3)]
    arcs = []
    paths = []
    macro = [position(s*period, x) for s in range(len(transitions)+1) for x in range(width)]
    for slab, maps in enumerate(transitions):
        assert len(maps) == degree
        start = slab*period
        for k in range(period):
            t = start+k
            for x in range(width):
                pages[t % 2].add((position(t, x), position(t+1, x)))
        for i, matching in enumerate(maps):
            t = start+2*i
            for x, y in matching:
                chord = (position(t, x), position(t+1, y))
                if x != y:  # an identity already occupies its chronological parity page
                    pages[2].add(chord)
                arc = (slab*width+x, (slab+1)*width+y)
                path = ([position(s, x) for s in range(start, t+1)] +
                        [position(s, y) for s in range(t+1, start+period+1)])
                arcs.append(arc)
                paths.append(path)
    all_edges = set.union(*pages)
    for (u, v), path in zip(arcs, paths):
        assert path[0] == macro[u] and path[-1] == macro[v]
        assert all(edge in all_edges for edge in zip(path, path[1:]))
    check_pages(size, pages)

    def shadows(vertex):
        t, pos = divmod(vertex, width)
        x = width-1-pos if t % 2 else pos
        slab, offset = divmod(t, period)
        return {slab*width+x, (slab+1)*width+x} if offset else {slab*width+x}

    for (u, v), path in zip(arcs, paths):
        assert all(shadows(vertex) & {u, v} for vertex in path)
    return size, pages, arcs, macro, shadows, len(paths)


def strict_layout(size, pages):
    incoming = [[] for _ in range(size)]
    outgoing = [[] for _ in range(size)]
    for color, edges in enumerate(pages):
        for u, v in edges:
            outgoing[u].append(color)
            incoming[v].append(color)
    endpoint = {}
    reps = []
    size_strict = 12*size
    spine = [None]*(size_strict-1)
    strict = [set() for _ in range(3)]
    for vertex in range(size):
        roles = sorted(incoming[vertex])+[None]+sorted(outgoing[vertex])
        assert len(roles) <= 4
        for slot, color in enumerate(roles):
            pos = 12*vertex+1+3*slot
            if color is None:
                reps.append(pos)
                continue
            endpoint[vertex, color] = pos
            assert spine[pos-1] is None and spine[pos] is None
            spine[pos-1], spine[pos] = (color+1) % 3, (color+2) % 3
    for color, edges in enumerate(pages):
        for u, v in edges:
            tail, head = endpoint[u, color], endpoint[v, color]
            assert reps[u] < tail < head < reps[v]
            assert tail//12 == u and head//12 == v
            strict[color].add((tail, head))
    for i in range(len(spine)):
        if spine[i] is None:
            previous = spine[i-1] if i else None
            following = spine[i+1] if i+1 < len(spine) else None
            spine[i] = next(c for c in range(3) if c != previous and c != following)
        strict[spine[i]].add((i, i+1))
    check_pages(size_strict, strict, has_spine=True)
    return strict, reps


def adjacency(size, edges):
    outgoing = [[] for _ in range(size)]
    for u, v in set(edges):
        assert u < v
        outgoing[u].append(v)
    return outgoing


def ancestors(outgoing, sources, removed):
    seen = [0]*len(outgoing)
    for i, source in enumerate(sources):
        seen[source] = 1 << i
    for u, later in enumerate(outgoing):
        if u in removed:
            seen[u] = 0
        elif seen[u]:
            for v in later:
                seen[v] |= seen[u]
    return seen


def audit_layouts():
    count = arcs = 0
    for width in range(1, 5):
        maps = monotone_maps(width)
        # All pairs of monotone partial injections up to width four in one slab.
        for f, g in product(maps, repeat=2):
            size, pages, _, _, _, paths = micro_layout(width, [(f, g)])
            strict_layout(size, pages)
            count += 1
            arcs += paths
    return count, arcs


def audit_cuts(width, transitions, cuts):
    size, pages, old_edges, macro, shadows, _ = micro_layout(width, transitions)
    strict, reps = strict_layout(size, pages)
    old = adjacency(len(macro), old_edges)   # expander arcs alone
    routed = adjacency(size, set.union(*pages) | {(u, u+1) for u in range(size-1)})
    ports = adjacency(12*size, set.union(*strict))
    packed_macro = [reps[u] for u in macro]
    count = left = lifted = 0
    for cut in cuts(12*size):
        cut = set(cut)
        microcut = {u//12 for u in cut}
        oldcut = {v for u in microcut for v in shadows(u)}
        assert len(microcut) <= len(cut) and len(oldcut) <= 2*len(microcut)
        # First inclusion for the layered routing; second checks *all* surviving
        # reachabilities, including paths using native spine edges, after port expansion.
        old_mask = ancestors(old, range(len(macro)), oldcut)
        micro_mask = ancestors(routed, macro, microcut)
        all_micro = ancestors(routed, range(size), microcut)
        all_packed = ancestors(ports, reps, cut)
        packed_mask = ancestors(ports, packed_macro, cut)
        assert all(mask & ~micro_mask[u] == 0 for u, mask in zip(macro, old_mask))
        assert all(mask & ~all_packed[rep] == 0 for rep, mask in zip(reps, all_micro))
        assert all(mask & ~packed_mask[rep] == 0 for rep, mask in zip(packed_macro, old_mask))
        left += sum(mask.bit_count() for mask in old_mask) - len(macro) + len(oldcut)
        lifted += sum(mask.bit_count() for mask in all_micro) - size + len(microcut)
        count += 1
    return count, left, lifted


def audit_deletions():
    totals = [0, 0, 0]
    def add(width, transitions, cuts):
        for i, n in enumerate(audit_cuts(width, transitions, cuts)):
            totals[i] += n

    def pairs(n):
        yield ()
        yield from combinations(range(n), 1)
        yield from combinations(range(n), 2)

    # Two nonidentical slabs, full and partial maps, internal/wrap boundaries.
    add(2, [(((0, 1),), ((0, 0), (1, 1))),
            (((1, 0),), ((0, 1),))], pairs)
    rng = Random(20261125)
    def random_cuts(n):
        for _ in range(100):
            yield rng.sample(range(n), rng.randrange(0, n//12+1))
    for _ in range(40):
        width = rng.randrange(2, 6)
        maps = monotone_maps(width)
        degree = rng.randrange(1, 5)
        transitions = [tuple(rng.choice(maps) for _ in range(degree))
                       for _ in range(rng.randrange(2, 6))]
        add(width, transitions, random_cuts)
    return totals


def check_butterflies():
    """Count canonical paths through every physical vertex, using actual colored port arcs."""
    rng = Random(731111)
    instances = pairs = cuts = max_micro_ratio = 0
    for h in range(1, 5):
        w = 1 << h
        idle = ((), ())
        active = []
        for i in range(h):
            bit = 1 << i
            active.append(tuple(tuple((x, x ^ bit) for x in range(w) if (x >> i) & 1 == b)
                                for b in (0, 1)))
        transitions = [idle]*h + active + [idle]*h
        size, pages, _, macro, _, _ = micro_layout(w, transitions)
        strict, reps = strict_layout(size, pages)
        physical = [edge for group in strict for edge in group if edge[1] > edge[0]+1]
        native = set.union(*pages)
        lifts = {}
        for tail, head in physical:
            u, v = tail//12, head//12
            assert (u, v) in native and (u, v) not in lifts
            lifts[u, v] = (*range(reps[u], tail+1), *range(head, reps[v]))
        assert set(lifts) == native

        def node(t, x):
            return t*w + (w-1-x if t % 2 else x)

        for early, late in product(range(h+1), range(2*h, 3*h+1)):
            micromasks = [0]*size
            portmasks = [0]*(12*size)
            for x, target in product(range(w), repeat=2):
                pair = 1 << (w*x + target)
                value = x
                path = [node(4*early, x)]
                for slab in range(early, late):
                    switch_time = None
                    if h <= slab < 2*h:
                        bit = 1 << (slab-h)
                        if (value ^ target) & bit:
                            switch_time = 2*int(bool(value & bit))
                    for slot in range(4):
                        if slot == switch_time:
                            value ^= bit
                        path.append(node(4*slab+slot+1, value))
                assert value == target and (path[0], path[-1]) == (
                    macro[early*w+x], macro[late*w+target])
                for u in path:
                    micromasks[u] |= pair
                for u, v in zip(path, path[1:]):
                    for pos in lifts[u, v]:
                        portmasks[pos] |= pair
                portmasks[reps[path[-1]]] |= pair
            # All w labels are exactly balanced at every crossed macro boundary.
            for slab in range(early, late+1):
                assert all(micromasks[u].bit_count() == w for u in macro[slab*w:(slab+1)*w])
            assert all(mask.bit_count() <= 2*w for mask in micromasks)
            assert all(mask & ~micromasks[pos//12] == 0 for pos, mask in enumerate(portmasks))
            peak = max(mask.bit_count() for mask in micromasks)
            assert peak == 3*w//2
            max_micro_ratio = max(max_micro_ratio, 2*peak//w)
            assert max(mask.bit_count() for mask in portmasks) == peak
            for _ in range(24):
                sample = rng.sample(range(12*size), rng.randrange(w//4+1))
                lost = 0
                for pos in sample:
                    lost |= portmasks[pos]
                assert lost.bit_count() <= 2*w*len(sample)
                assert w*w - lost.bit_count() >= (w*w+1)//2
                cuts += 1
            instances += 1
            pairs += w*w
    return instances, pairs, cuts, max_micro_ratio


if __name__ == "__main__":
    layouts, arcs = audit_layouts()
    print(f"{layouts} exhaustive one-slab layouts at widths 1–4, {arcs} macro arc lifts; "
          "all three pages match and nest before and after port expansion")
    cuts, old_pairs, micro_pairs = audit_deletions()
    print(f"{cuts} multislab physical deletion cases, {old_pairs} strict macro ancestor pairs "
          f"and {micro_pairs} strict micro ancestor pairs preserved")
    layers, pairs, sampled, peak = check_butterflies()
    print(f"{layers} early/late butterfly layer pairs at widths 2, 4, 8, 16; "
          f"{pairs} complete physical canonical paths, peak load {peak}w/2, "
          f"{sampled} bounded deletion samples")
