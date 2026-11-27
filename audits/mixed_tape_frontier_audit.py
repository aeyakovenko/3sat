"""Check the mixed-tape transfer paths and the geometric line-block protocol."""

from collections import Counter
from itertools import combinations, product
from random import Random


def make_trace(side, edges):
    """Return physical visits, active transfer owners, hub times, and ideal edges."""
    count = max(max(edge) for edge in edges) + 1
    visits = []
    owners = []
    hubs = {}
    links = set()
    position = [0, 0, 0]
    lanes = range(side * side)

    def plane_cell(vertex, lane):
        return (vertex % 2 * side + lane % side, vertex // 2 * side + lane // side)

    def visit(vertex, lane, index, owner=None):
        target = (*plane_cell(vertex, lane), index)
        for axis, stop in enumerate(target):
            while position[axis] != stop:
                position[axis] += 1 if position[axis] < stop else -1
                visits.append(tuple(position))
                owners.append(owner)
        visits.append(tuple(position))
        owners.append(owner)
        return len(visits) - 1

    for vertex in range(count):
        for lane in lanes:
            hubs[vertex, lane] = visit(vertex, lane, 0)
        for source, dest in edges:
            if source != vertex:
                continue
            for shear in (0, 1):
                for lane in lanes:
                    visit(source, lane, lane, source)
                for lane in reversed(lanes):
                    x, y = lane % side, lane // side
                    mapped = y * side + (x + shear * (2 * y + 1)) % side
                    visit(dest, mapped, lane, source)
                    links.add(((source, lane), (dest, mapped)))

    cells = {plane_cell(v, i): (v, i) for v in range(count) for i in lanes}
    return visits, owners, hubs, links, cells


def audit_trace(side, edges, rng):
    visits, owners, hubs, links, cells = make_trace(side, edges)
    bits = {hub: 1 << n for n, hub in enumerate(hubs.values())}
    plane_last = {}
    line_last = {}
    predecessors = []
    for t, (x, y, index) in enumerate(visits):
        predecessors.append((plane_last.get((x, y), -1), line_last.get(index, -1)))
        plane_last[x, y] = line_last[index] = t
    times = range(len(visits))

    def check(removed):
        marks = set()
        reachable = [0] * (len(visits) + 1)  # The final zero handles predecessor -1.
        for t, (plane_pred, line_pred) in enumerate(predecessors):
            if t in removed:
                x, y, index = visits[t]
                if (x, y) in cells:
                    marks.add(cells[x, y])
                if owners[t] is not None:
                    marks.add((owners[t], index))
            else:
                reachable[t] = reachable[plane_pred] | reachable[line_pred] | bits.get(t, 0)
        assert len(marks) <= 2 * len(removed)
        for source, dest in links:
            if source not in marks and dest not in marks:
                assert reachable[hubs[dest]] & bits[hubs[source]]

    checks = 0
    for size in range(3 if side == 2 else 2):
        for removed in combinations(times, size):
            check(set(removed))
            checks += 1
    for _ in range(100):
        check(set(rng.sample(times, rng.randrange(1, 13))))
        checks += 1
    return len(visits), checks


def audit_line_blocks():
    for width in range(2, 24):
        for entry, command in product((0, width - 1), (-1, 0, 1)):
            pos = entry
            exit_endpoint = width - 1 if command > 0 else 0
            for _ in range(width - 1):
                assert pos // width == 0
                if command and entry != exit_endpoint:
                    pos += command
            assert pos // width == 0
            pos += command
            assert pos // width == command
            assert pos % width in (0, width - 1)


def memory_edges(positions):
    previous = {}
    edges = []
    for t, pos in enumerate(positions):
        if pos in previous:
            edges.append((previous[pos], t))
        previous[pos] = t
    return edges


def check_shift_average(plane, line, tile_width, group_size):
    """Enumerate all grid offsets and rank offsets with exact integer bounds."""
    steps = len(line)
    dimension = len(plane[0])
    chrono = [(t, t + 1) for t in range(steps - 1)]
    auxiliary = memory_edges(line)
    plane_edges = memory_edges(plane)
    edges = chrono + auxiliary + plane_edges

    lifetime = sum(j - i for i, j in auxiliary)
    first = {}
    last = {}
    for t, cell in enumerate(line):
        first.setdefault(cell, t)
        last[cell] = t
    assert lifetime == sum(last[cell] - start for cell, start in first.items())
    live = [sum(i <= k < j for i, j in auxiliary) for k in range(steps - 1)]
    assert lifetime == sum(live)
    for threshold in range(max(live, default=0) + 1):
        removed = {t for k, level in enumerate(live) if level > threshold for t in (k, k + 1)}
        surviving = [(i, j) for i, j in auxiliary if i not in removed and j not in removed]
        assert all(sum(i <= k < j for i, j in surviving) <= threshold for k in range(steps - 1))

    grid_crossings = 0
    for shift in product(range(tile_width), repeat=dimension):
        tiles = [tuple((x + off) // tile_width for x, off in zip(pos, shift)) for pos in plane]
        counts = Counter()
        ranks = []
        for tile in tiles:
            ranks.append(counts[tile])
            counts[tile] += 1
        cross = [(i, j) for i, j in edges if tiles[i] != tiles[j]]
        inner = [(i, j) for i, j in edges if tiles[i] == tiles[j]]
        grid_crossings += len(cross)
        inner_span = sum(ranks[j] - ranks[i] for i, j in inner)
        assert all(tiles[i] == tiles[j] for i, j in plane_edges)
        assert sum(ranks[j] - ranks[i] for i, j in plane_edges) <= tile_width**dimension * steps
        assert sum(ranks[j] - ranks[i] for i, j in auxiliary if tiles[i] == tiles[j]) <= lifetime
        assert inner_span <= (steps - 1) + lifetime + tile_width**dimension * steps

        # A common offset gives each tile the required uniform marginal.
        rank_crossings = 0
        for offset in range(group_size):
            groups = [(tile, (rank + offset) // group_size) for tile, rank in zip(tiles, ranks)]
            assert max(Counter(groups).values()) <= group_size
            cut_inner = [(i, j) for i, j in inner if groups[i] != groups[j]]
            removed = {i for i, _ in cross + cut_inner}
            assert all(groups[i] == groups[j] for i, j in edges if i not in removed and j not in removed)
            rank_crossings += len(cut_inner)
        assert rank_crossings == sum(min(group_size, ranks[j] - ranks[i]) for i, j in inner)
        assert rank_crossings <= inner_span
    assert grid_crossings <= (lifetime + steps - 1) * tile_width**(dimension - 1)


def positions_from_moves(dimension, moves):
    position = [0] * dimension
    points = [tuple(position)]
    for move in moves:
        if move:
            position[abs(move) - 1] += 1 if move > 0 else -1
        points.append(tuple(position))
    return points


def audit_separators():
    for dimension in (2, 3):
        cases = 0
        single_visit = 0
        routes = [positions_from_moves(1, moves) for moves in product((-1, 0, 1), repeat=3)]
        for moves in product(range(-dimension, dimension + 1), repeat=3):
            plane = positions_from_moves(dimension, moves)
            for line in routes:
                check_shift_average(plane, line, tile_width=2, group_size=3)
                cases += 1
                if len(set(line)) == len(line):
                    single_visit += 1
        # Longer sweeps have both once-visited cells and long repeated-cell spans.
        plane = positions_from_moves(dimension, (1, 2, -1, -2) * 3)
        sweep = positions_from_moves(1, (1,) * 7 + (-1,) * 5)
        check_shift_average(plane, sweep, tile_width=3, group_size=4)
        print(f'dimension {dimension}: {cases} four-step walk pairs, including {single_visit} '
              'with a line visiting each cell once; long sweep passed')


if __name__ == '__main__':
    audit_line_blocks()
    rng = Random(20261124)
    examples = ((2, [(0, 1)]), (3, [(0, 1), (0, 2), (1, 2), (2, 3)]))
    for side, edges in examples:
        steps, checks = audit_trace(side, edges, rng)
        print(f'{side} by {side} tiles, {steps} steps, {checks} deletion sets passed')
    audit_separators()
