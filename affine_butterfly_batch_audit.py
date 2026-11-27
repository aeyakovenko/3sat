"""Check affine queries on binary butterflies and the three-layer triangle construction."""

from itertools import product
from random import Random


def path(depth, source, sink):
    """Take the unique path, changing the bits of the current vertex from MSB to LSB."""
    vertex = source
    for bit in reversed(range(depth)):
        digit = (sink >> bit) & 1
        edge = 2 * vertex + digit
        vertex = (vertex & ~(1 << bit)) | (digit << bit)
        yield edge, vertex
    assert vertex == sink


def path_mask(depth, endpoints):
    source, sink = divmod(endpoints, 1 << depth)
    per_layer = 2 << depth
    return sum(1 << (layer * per_layer + e) for layer, (e, _) in enumerate(path(depth, source, sink)))


def projection(depth, layer, endpoints):
    """Return the concatenated target prefix and source suffix, of total length d+1."""
    source, sink = divmod(endpoints, 1 << depth)
    suffix_len = depth - layer
    prefix = sink >> (suffix_len - 1)
    return (prefix << suffix_len) | (source & ((1 << suffix_len) - 1))


def physical_edge(depth, layer, descriptor):
    suffix_len = depth - layer
    prefix, suffix = divmod(descriptor, 1 << suffix_len)
    tail = ((prefix >> 1) << suffix_len) | suffix
    return 2 * tail + (prefix & 1)


def echelon(rows):
    pivots = {}
    for row in rows:
        while row:
            high = row.bit_length() - 1
            if high not in pivots:
                pivots[high] = row
                break
            row ^= pivots[high]
    return list(pivots.values())


def affine_points(anchor, directions):
    points = [anchor]
    for row in echelon(directions):
        points += [p ^ row for p in points]
    return points


def image_mask(depth, anchor, directions):
    result = 0
    for layer in range(depth):
        offset = projection(depth, layer, anchor)
        rows = [projection(depth, layer, v) for v in directions]
        for point in affine_points(offset, rows):
            edge = physical_edge(depth, layer, point)
            result |= 1 << (layer * (2 << depth) + edge)
    return result


def all_affine_spaces(bits):
    """Generate distinct linear subspaces explicitly, then partition into their cosets."""
    universe = range(1 << bits)
    linear = {frozenset({0}): ()}
    for v in universe:
        for span, basis in list(linear.items()):
            if v not in span:
                linear.setdefault(span | {u ^ v for u in span}, (*basis, v))
    for span, basis in linear.items():
        remaining = set(universe)
        while remaining:
            anchor = min(remaining)
            points = {u ^ anchor for u in span}
            remaining -= points
            yield anchor, basis, points


def exhaustive(depth):
    paths = [path_mask(depth, z) for z in range(1 << (2 * depth))]
    spaces = []
    for anchor, basis, points in all_affine_spaces(2 * depth):
        direct = 0
        for z in points:
            direct |= paths[z]
        projected = image_mask(depth, anchor, basis)
        assert direct == projected
        spaces.append((sum(1 << p for p in points), projected))
    graphs = 1 << (depth * (2 << depth))
    for missing in range(graphs):
        unreachable = sum(1 << i for i, used in enumerate(paths) if missing & used)
        for pair_set, union in spaces:
            # Existential nonreachability and its universal reachability complement.
            assert bool(pair_set & unreachable) == bool(union & missing)
    return len(spaces), graphs, len(spaces) * graphs


def larger_spaces():
    rng = Random(227103)
    checks = 0
    for depth in (3, 4, 6):
        for _ in range(60):
            width = 2 * depth
            anchor = rng.getrandbits(width)
            directions = [rng.getrandbits(width) for _ in range(rng.randrange(min(width, 7) + 1))]
            # Add redundant directions to exercise rank drops under the projections.
            if directions:
                directions += [directions[0], directions[0] ^ directions[-1], 0]
            raw = {anchor}
            for v in directions:
                raw.update([u ^ v for u in raw])
            paths = [path_mask(depth, z) for z in raw]
            union = image_mask(depth, anchor, directions)
            all_edges = depth * (2 << depth)
            for _ in range(12):
                missing = sum(1 << i for i in rng.sample(range(all_edges), rng.randrange(1, all_edges + 1)))
                assert any(used & missing for used in paths) == bool(union & missing)
                checks += 1
    return checks


def tripartite_graphs(h, matrices):
    """Compare every individual reachable affine pair with the corresponding triangle."""
    side = 1 << h
    depth = 2 * h
    size = 1 << depth
    stride = 2 * size
    # The affine endpoint family consists of exactly (source=(j,i), sink=(k,j)).
    triples = [(i, j, k, side * j + i, side * k + j) for i, j, k in product(range(side), repeat=3)]
    basis = [(1 << b) << depth for b in range(h)]
    basis += [((side << b) << depth) | (1 << b) for b in range(h)]
    basis += [side << b for b in range(h)]
    assert set(affine_points(0, basis)) == {(s << depth) | t for _, _, _, s, t in triples}
    paths = [path_mask(depth, (s << depth) | t) for _, _, _, s, t in triples]
    # Bits in A,C,B index the allowed vertices at layers 0,h,2h respectively.
    # Test masks on edges using their actual endpoints even when h=1 means that
    # the midpoint test and sink test must be installed on the same edge layer.
    def permitted_graph(a, c, b):
        mask = 0
        for layer, u, digit in product(range(depth), range(size), range(2)):
            place = depth - 1 - layer
            v = (u & ~(1 << place)) | (digit << place)
            if layer == 0 and not (a >> u) & 1:
                continue
            if layer == h and not (c >> u) & 1:
                continue
            if layer == depth - 1 and not (b >> v) & 1:
                continue
            mask |= 1 << (layer * stride + 2 * u + digit)
        return mask

    total = nonempty = mixed = 0
    for a, c, b in matrices:
        graph = permitted_graph(a, c, b)
        triangles = [bool((a >> (side * j + i)) & (c >> (side * k + i)) & (b >> (side * k + j)) & 1)
                     for i, j, k, _, _ in triples]
        answers = [not (used & ~graph) for used in paths]
        assert answers == triangles
        assert any(answers) == any(triangles) and all(not v for v in answers) == (not any(triangles))
        total += 1
        nonempty += any(answers)
        mixed += any(answers) and not all(answers)
    return total, nonempty, mixed


if __name__ == '__main__':
    for d in (1, 2):
        print(f'depth {d}, affine spaces / graphs / batch checks:', exhaustive(d), flush=True)
    print('larger affine batch checks:', larger_spaces(), flush=True)
    print('2x2 tripartite graphs / with triangle / mixed:', tripartite_graphs(1, product(range(16), repeat=3)))
    rng = Random(684205)
    big = [(0, 0, 0), (65535, 65535, 65535)]
    for trial in range(198):
        threshold = (1, 2, 4, 6)[trial % 4]
        big.append(tuple(sum(1 << i for i in range(16) if rng.randrange(8) < threshold) for _ in range(3)))
    print('4x4 tripartite graphs / with triangle / mixed:', tripartite_graphs(2, big))
