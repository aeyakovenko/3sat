"""Check the single-head grid minors and the reserved-edge-point realization."""

from collections import defaultdict
from itertools import islice, pairwise, product

from two_tape_grate_experiment import snake


def serpentine(dimension, side):
    """Visit the full box, scanning parallel lines along the first axis."""
    if dimension == 1:
        return [(x,) for x in range(side)]
    if dimension == 2:
        return list(snake(side))
    order = []
    for i, tail in enumerate(serpentine(dimension - 1, side)):
        line = range(side) if i % 2 == 0 else reversed(range(side))
        order.extend((x,) + tail for x in line)
    return order


def native_edges(walk):
    """Reconstruct chronology and consecutive visits from actual positions."""
    chronological = set()
    returns = set()
    last = {}
    for t, pos in enumerate(walk):
        if t:
            distance = sum(abs(a - b) for a, b in zip(pos, walk[t - 1], strict=True))
            assert distance <= 1, (t, pos, walk[t - 1])
            chronological.add((t - 1, t))
        if pos in last:
            returns.add((last[pos], t))
        last[pos] = t
    return chronological, returns


def audit_sweeps(dimension, side):
    walk = []
    branch = []
    template = serpentine(dimension, side)
    for layer in range(side):
        for axis in range(dimension):
            scan = [p[1:axis + 1] + (p[0],) + p[axis + 1:] for p in template]
            if walk and walk[-1] == scan[-1]:
                scan.reverse()
            assert not walk or walk[-1] == scan[0]
            walk.extend(scan)
            branch.extend((layer,) + p for p in scan)

    chronological, returns = native_edges(walk)
    times = defaultdict(list)
    for t, vertex in enumerate(branch):
        times[vertex].append(t)
    assert len(walk) == dimension * side ** (dimension + 1)
    assert len(times) == side ** (dimension + 1)
    for group in times.values():
        assert len(group) == dimension
        assert all(edge in returns for edge in pairwise(group))

    # Layer neighbors come from returns. Spatial neighbors come from chronology.
    for direction in range(dimension + 1):
        edges = returns if direction == 0 else chronological
        links = {frozenset((branch[a], branch[b])) for a, b in edges}
        for vertex in times:
            if vertex[direction] + 1 < side:
                neighbor = list(vertex)
                neighbor[direction] += 1
                assert frozenset((vertex, tuple(neighbor))) in links
    return len(walk)


def audit_edge_points(dimension):
    n = 18
    edges = [(u, v) for u in range(n) for v in range(u + 1, n)
             if (11 * u + 7 * v) % 13 < 3]
    side = 1
    while side ** dimension < len(edges):
        side += 1
    points = product(range(0, 2 * side, 2), repeat=dimension)
    pads = dict(zip(edges, islice(points, len(edges)), strict=True))
    walk = [(1,) * dimension]
    owners = [0]

    def move(owner, position):
        walk.append(position)
        owners.append(owner)

    def along(owner, axis, value):
        pos = list(walk[-1])
        while pos[axis] != value:
            pos[axis] += 1 if value > pos[axis] else -1
            move(owner, tuple(pos))

    for owner in range(n):
        move(owner, walk[-1])
        for edge, pad in pads.items():
            if owner not in edge:
                continue
            dock = (pad[0] + 1,) + pad[1:]
            along(owner, 1, 1)
            along(owner, 0, dock[0])
            for axis in range(2, dimension):
                along(owner, axis, dock[axis])
            along(owner, 1, dock[1])
            move(owner, pad)
            move(owner, dock)

    _, returns = native_edges(walk)
    visits = defaultdict(list)
    for t, pos in enumerate(walk):
        visits[pos].append(t)
    assert set(owners) == set(range(n)) and owners == sorted(owners)
    for edge, pad in pads.items():
        first, second = visits[pad]
        assert (owners[first], owners[second]) == edge
        assert (first, second) in returns
    return len(edges), len(walk)


if __name__ == "__main__":
    for d, s in product(range(1, 5), (3, 5)):
        steps = audit_sweeps(d, s)
        print(f"Sweeps in dimension {d}, side {s}: {steps} step vertices verified")
    for d in (2, 3, 4):
        count, steps = audit_edge_points(d)
        print(f"Edge points in dimension {d}: {count} edges in {steps} step vertices verified")
