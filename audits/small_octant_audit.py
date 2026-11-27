"""Check marginal reconstruction and output-sensitive octant reporting."""
from bisect import bisect_right
from itertools import product


def moments(cells):
    return [sum(cells[c] for c in range(8) if c & s == s) for s in range(7)]


def sign(cell):
    return (-1) ** (3 - cell.bit_count())


def offsets(margins):
    return [sum((-1) ** ((s ^ c).bit_count()) * margins[s]
                for s in range(7) if c & s == c) for c in range(8)]


def candidate_cells(count_margins):
    a = offsets(count_margins)
    return [min((c for c in range(8) if sign(c) == s), key=a.__getitem__)
            for s in (1, -1)]


def swept_moments(points, queries, weighted):
    """The time coordinate of a query is the number of earlier updates."""
    result = [[0] * 7 for _ in queries]
    axes = [[(t + 1, x, y)[i] for t, (x, y, _) in enumerate(points)]
            for i in range(3)]
    weights = [w if weighted else 1 for _, _, w in points]
    for s in range(7):
        selected = [i for i in range(3) if s >> i & 1]
        if not selected:
            total = sum(weights)
            for row in result:
                row[0] = total
            continue
        first, last = selected[0], selected[-1]
        second_keys = sorted(set(axes[last]))
        second_ids = {value: i + 1 for i, value in enumerate(second_keys)}
        tree = [0] * (len(second_keys) + 1)
        order = sorted(range(len(points)), key=axes[first].__getitem__)
        inserted = 0
        for j in sorted(range(len(queries)), key=lambda j: queries[j][first]):
            q = queries[j]
            while inserted < len(order) and axes[first][order[inserted]] <= q[first]:
                i = order[inserted]
                inserted += 1
                v = second_ids[axes[last][i]]
                while v < len(tree):
                    tree[v] += weights[i]
                    v += v & -v
            v = bisect_right(second_keys, q[last])
            while v:
                result[j][s] += tree[v]
                v -= v & -v
    return result


class Node:
    """One chronological interval; its x catalogue is cascaded to its children."""
    def __init__(self, points, lo, hi):
        self.lo, self.hi = lo, hi
        self.ids = sorted(range(lo, hi), key=lambda i: (points[i][0], i))
        self.xs = [points[i][0] for i in self.ids]
        self.ys = [points[i][1] for i in self.ids]
        self.tables = []
        for op in (min, max):
            table = [list(range(hi - lo))]
            radius = 1
            while 2 * radius <= hi - lo:
                old = table[-1]
                table.append([op(old[i], old[i + radius], key=self.ys.__getitem__)
                              for i in range(len(old) - radius)])
                radius *= 2
            self.tables.append(table)
        if hi - lo > 1:
            mid = (lo + hi) // 2
            self.left = Node(points, lo, mid)
            self.right = Node(points, mid, hi)
            self.left_prefix = [0]
            for i in self.ids:
                self.left_prefix.append(self.left_prefix[-1] + (i < mid))

    def slices(self, lo, hi, xprefix):
        if self.hi <= lo or hi <= self.lo:
            return
        if lo <= self.lo and self.hi <= hi:
            yield self, xprefix
            return
        left_x = self.left_prefix[xprefix]
        yield from self.left.slices(lo, hi, left_x)
        yield from self.right.slices(lo, hi, xprefix - left_x)

    def report_y(self, lo, hi, bound, low):
        stack = [(lo, hi)]
        table = self.tables[0 if low else 1]
        while stack:
            lo, hi = stack.pop()
            if lo == hi:
                continue
            k = (hi - lo).bit_length() - 1
            a, b = table[k][lo], table[k][hi - (1 << k)]
            extreme = (min if low else max)(a, b, key=self.ys.__getitem__)
            if (self.ys[extreme] <= bound) == low:
                yield self.ids[extreme]
                stack.extend(((lo, extreme), (extreme + 1, hi)))


def report(node, size, query, cell):
    if node is None:
        return
    t, a, b = query
    txlo, txhi = (0, t) if cell & 1 else (t, size)
    for block, xprefix in node.slices(txlo, txhi, bisect_right(node.xs, a)):
        xlo, xhi = (0, xprefix) if cell & 2 else (xprefix, len(block.ids))
        yield from block.report_y(xlo, xhi, b, bool(cell & 4))


def race(points, node, query, marg_weight, marg_count):
    cells = candidate_cells(marg_count)
    reports = [report(node, len(points), query, c) for c in cells]
    total = [0, 0]
    seen = 0
    while True:
        for i, it in enumerate(reports):
            update = next(it, None)
            if update is None:
                c = cells[i]
                return seen, sign(c) * (total[i] - offsets(marg_weight)[c])
            total[i] += points[update][2]
        seen += 1


def direct_cells(points, query, weighted):
    t, a, b = query
    cells = [0] * 8
    for i, (x, y, w) in enumerate(points):
        cell = (i < t) | ((x <= a) << 1) | ((y <= b) << 2)
        cells[cell] += w if weighted else 1
    return cells


def audit_geometry():
    files = tests = 0
    items = list(product((1, 2), (1, 2), (1, 3)))
    for size in range(4):
        queries = list(product(range(size + 1), range(3), range(3)))
        for points in product(items, repeat=size):
            files += 1
            root = Node(points, 0, size) if size else None
            wm = swept_moments(points, queries, True)
            cm = swept_moments(points, queries, False)
            for j, q in enumerate(queries):
                wc = direct_cells(points, q, True)
                cc = direct_cells(points, q, False)
                assert wm[j] == moments(wc) and cm[j] == moments(cc)
                assert race(points, root, q, wm[j], cm[j]) == (min(cc), wc[7])
                for c in range(8):
                    ids = list(report(root, size, q, c))
                    t, a, b = q
                    expected = {i for i, (x, y, _) in enumerate(points)
                                if ((i < t) | ((x <= a) << 1) | ((y <= b) << 2)) == c}
                    assert len(ids) == len(set(ids)) and set(ids) == expected
                tests += 1
    return files, tests


def audit_tables():
    count = 0
    for table in product(range(3), repeat=8):
        m = moments(table)
        a = offsets(m)
        assert [a[i] + sign(i) * table[7] for i in range(8)] == list(table)
        candidates = candidate_cells(m)
        assert min(table[i] for i in candidates) == min(table)
        lower, upper = -a[candidates[0]], a[candidates[1]]
        assert lower <= table[7] <= upper
        assert upper - lower == sum(table[i] for i in candidates)
        count += 1
    return count


def audit_dense():
    left = [(x, y, w) for w in (2, 5, 7) for x in range(1, 5) for y in range(1, 5)]
    right = [(x, y, w) for w in (11, 13) for y in (4, 2, 1, 3) for x in (3, 1, 4, 2)]
    points = left + right
    root = Node(points, 0, len(points))
    queries = list(product(range(0, len(points) + 1, 4), range(1, 5), range(1, 5)))
    wm, cm = (swept_moments(points, queries, b) for b in (True, False))
    largest = 0
    for j, q in enumerate(queries):
        k = min(direct_cells(points, q, False))
        f = direct_cells(points, q, True)[7]
        assert race(points, root, q, wm[j], cm[j]) == (k, f)
        largest = max(largest, k)
    assert largest >= 8
    # Four earlier and four later uniform points at the central query.
    slabs = [tuple(draw.count(i) for i in range(4)) for draw in product(range(4), repeat=4)]
    hitting = sum(min(first + second) for first, second in product(slabs, repeat=2))
    assert hitting == 24 ** 2 and len(slabs) ** 2 == 65536
    return len(queries), largest, hitting


def audit_bands():
    points = [(t, (t * 5) % 7, (t * 3) % 7, t % 5 + 1) for t in range(1, 25)]
    queries = list(product(range(25), range(7), range(7)))
    widths = (4, 3, 2)
    for q in queries:
        # Bands are (lo, hi]; this definition includes zero.
        low = tuple((cut // width) * width - 1 for cut, width in zip(q, widths))
        high = tuple(l + w for l, w in zip(low, widths))
        local = [p for p in points if all(l < v <= h for v, l, h in zip(p, low, high))]
        local_sum = sum(p[3] for p in local if all(v <= cut for v, cut in zip(p, q)))
        recovered = local_sum
        for s in range(1, 8):
            cut = tuple(low[i] if s >> i & 1 else q[i] for i in range(3))
            subtotal = sum(p[3] for p in points if all(v <= vcut for v, vcut in zip(p, cut)))
            recovered -= (-1) ** s.bit_count() * subtotal
        assert recovered == sum(p[3] for p in points if all(v <= cut for v, cut in zip(p, q)))
    return len(queries)


def audit_partition_means():
    side = 4
    axes = []
    for split in range(1 << (side - 1)):
        boundaries = [0, *(i for i in range(1, side) if split >> (i - 1) & 1), side]
        lengths = [hi - lo for lo, hi in zip(boundaries, boundaries[1:])]
        space = [next((l, h) for l, h in zip(boundaries, boundaries[1:]) if l < a <= h)
                 for a in range(1, side + 1)]
        time = [next((l, h) for l, h in zip(boundaries, boundaries[1:]) if l <= t < h)
                for t in range(side)]
        axes.append((space, time, sum(l * l // 4 for l in lengths), sum(l * l for l in lengths)))
    checked = 0
    for at, ax, ay in product(axes, repeat=3):
        mass = smallest = 0
        for t, aa, bb in product(range(side), repeat=3):
            a, b = aa + 1, bb + 1
            tl, th = at[1][t]
            xl, xh = ax[0][aa]
            yl, yh = ay[0][bb]
            counts = [0] * 8
            for rt, x, y in product(range(tl+1, th+1), range(xl+1, xh+1), range(yl+1, yh+1)):
                counts[(rt <= t) | ((x <= a) << 1) | ((y <= b) << 2)] += 1
            smallest += min(counts)
            mass += sum(counts)
        assert smallest == at[2] * ax[2] * ay[2]
        assert mass == at[3] * ax[3] * ay[3]
        checked += 1
    return checked


def audit_collision():
    diag = [(1, 1, 1), (2, 2, 1)]
    anti = [(1, 2, 1), (2, 1, 1)]
    left, right = diag + anti, anti + diag
    # Four updates, with two actual queries in each inter-update interval.
    queries = [(t, 1, 1) if (t, q) == (2, 0) else (t, 2, 2)
               for t in range(5) for q in range(2)]
    w_left = swept_moments(left, queries, True)
    w_right = swept_moments(right, queries, True)
    assert w_left == w_right
    target = [q for q in queries
              if direct_cells(left, q, True)[7] != direct_cells(right, q, True)[7]]
    assert target == [(2, 1, 1)]
    # A threshold from outside this actual query list reveals an intermediate change.
    assert moments(direct_cells(left, (1, 1, 1), True)) != moments(
        direct_cells(right, (1, 1, 1), True))
    return len(queries)


if __name__ == "__main__":
    files, tests = audit_geometry()
    print(f"{files} streams, {tests} geometric queries, {8 * tests} full octant enumerations")
    print(f"{audit_tables()} distinct integer tables: affine reconstruction, tight interval, two candidates")
    print(f"{audit_collision()} query cuts in the four-update collision: all margins equal, one answer differs")
    dense, largest, hits = audit_dense()
    print(f"{dense} dense queries, largest minimum cell {largest}; {hits}/65536 balanced samples hit all eight")
    print(f"{audit_bands()} three-axis band queries reconstructed from local sums and seven coarse terms")
    print(f"{audit_partition_means()} complete axis partitions: exact conditional mean-minimum and mass sums")
