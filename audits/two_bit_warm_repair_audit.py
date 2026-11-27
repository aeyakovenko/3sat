"""Literal-level butterfly and bounded-repair checks. Python standard library only."""

from itertools import combinations, product
from random import Random


def build_base(d, retained):
    # The audit uses degree two. The first six names are two fixed constant triples.
    rows = []
    for ids, values in [((1, 2, 3), (0, 0, 0)), ((4, 5, 6), (0, 1, 0))]:
        for wrong in product((0, 1), repeat=3):
            if wrong != values:
                rows.append(tuple(-v if bit else v for v, bit in zip(ids, wrong)))
    width = 1 << d
    next_id = 10 * (2 * width + 1)
    mutable_rows = []
    trees = []
    for side in range(2):
        level = {}
        for label in range(width):
            j = 1 + side * width + label
            complement, leaf = 10 * j + 2, 10 * j + 3
            mutable_rows.append(len(rows))
            rows.extend([(complement, 1, 2), (leaf, complement, 1),
                         (-leaf, -complement, 1)])
            bits = f'{label:0{d}b}'
            level[bits[::-1] if side == 0 else bits] = leaf
        levels = dict(level)
        for depth in range(d - 1, -1, -1):
            for prefix in sorted({key[:depth] for key in level}):
                left, right = level[prefix+'0'], level[prefix+'1']
                node = next_id
                next_id += 1
                rows.extend([(-left, node, 1), (-right, node, 1), (left, right, -node)])
                level[prefix] = node
                levels[prefix] = node
        trees.append(levels)
    for i in range(d):
        for v in range(width):
            for new in range(2):
                edge_id = 2 * (i * width + v) + new
                bits = f'{v:0{d}b}'
                suffix = bits[i:][::-1]
                prefix = bits[:i] + str(new)
                rows.append((-trees[0][suffix], -trees[1][prefix],
                             5 if retained >> edge_id & 1 else 4))
    used = {abs(v) for row in rows for v in row}
    for v in range(1, next_id):
        if v not in used:
            rows.append((-v, 1, 2))
    header = f'p cnf {next_id-1} {len(rows)}\n'
    lines = [f'{a} {b} {c} 0\n' for a, b, c in rows]
    offsets = set(mutable_rows)
    starts, pos = [], len(header)
    for i, line in enumerate(lines):
        if i in offsets:
            starts.append(pos + line.index(' ') - 1)
        pos += len(line)
    return (header+''.join(lines)).encode(), starts


def parse(file):
    header, *body = file.decode().splitlines()
    _, _, nv, nr = header.split()
    rows = [tuple(map(int, line.split())) for line in body]
    assert len(rows) == int(nr)
    assert all(len(row) == 4 and row[-1] == 0 and
               len({abs(v) for v in row[:3]}) == 3 for row in rows)
    return int(nv), [row[:3] for row in rows]


def forced_model(file):
    nv, rows = parse(file)
    # The two seven-clause groups explicitly fix these named constants.
    for start, expected in [(0, (0, 0, 0)), (7, (0, 1, 0))]:
        cubes = [a for a in product((0, 1), repeat=3)
                 if all(any(a[(abs(v)-1) % 3] == (v > 0) for v in row)
                        for row in rows[start:start+7])]
        assert cubes == [expected]
    values = {i: bit for i, bit in enumerate((0, 0, 0, 0, 1, 0), 1)}
    for _ in range(nv + 1):
        old = len(values)
        for row in rows:
            if any(values.get(abs(a), None) == (a > 0) for a in row):
                continue
            free = [a for a in row if abs(a) not in values]
            if not free:
                return None
            if len(free) == 1:
                values[abs(free[0])] = free[0] > 0
        if len(values) == old:
            assert len(values) == nv
            return values
    raise AssertionError('unit propagation failed to stabilize')


def graph_reaches(d, retained, s, t):
    width, layer = 1 << d, {s}
    for i in range(d):
        pos = d - i - 1
        layer = {(v & ~(1 << pos)) | (a << pos) for v in layer for a in range(2)
                 if retained >> (2 * (i * width + v) + a) & 1}
    return t in layer


def butterfly_checks():
    rng = Random(433)
    tested = positive = 0
    for d in [1, 2]:
        width, edges = 1 << d, 2 * d * (1 << d)
        graphs = range(1 << edges) if d == 1 else [0, (1 << edges)-1] + [
            rng.getrandbits(edges) for _ in range(20)]
        public = None
        for graph in graphs:
            raw, offsets = build_base(d, graph)
            base = forced_model(raw)
            assert base is not None and (public is None or public == base)
            public = base
            for s, t in product(range(width), repeat=2):
                changed = bytearray(raw)
                for pos in [offsets[s], offsets[width+t]]:
                    assert changed[pos] == ord('2')
                    changed[pos] ^= 1
                assert sum((x ^ y).bit_count() for x, y in zip(changed, raw)) == 2
                answer = forced_model(changed)
                assert (answer is not None) == graph_reaches(d, graph, s, t)
                if answer is not None:
                    assert sum(base[v] != answer[v] for v in base) == 2*d+4
                    positive += 1
                tested += 1
    print(f'{tested} two-physical-bit queries, {positive} unique positive repairs')


def representatives(records, budget):
    if not records:
        return []
    blocked, matching = set(), []
    for data, rowid in records:
        if not data:
            return [rowid]
        if data.isdisjoint(blocked):
            blocked.update(data)
            matching.append(rowid)
            if len(matching) == budget + 1:
                return matching
    parts = {}
    for data, rowid in records:
        pivot = min(data & blocked)
        parts.setdefault(pivot, []).append((data-{pivot}, rowid))
    return [i for group in parts.values() for i in representatives(group, budget)]


def representative_checks():
    tested = 0
    for budget in range(5):
        for family in [list(combinations(range(9), 2)),
                       [(0, i, j) for i, j in combinations(range(1, 9), 2)],
                       [(i, (i+1) % 9, (i+3) % 9) for i in range(9)]]:
            records = [(set(data), rowid) for rowid, data in enumerate(family)]
            ids = representatives(records, budget)
            for size in range(budget+1):
                for block in combinations(range(9), size):
                    assert any(data.isdisjoint(block) for data, _ in records) == any(
                        records[i][0].isdisjoint(block) for i in ids)
                    tested += 1
    print(f'{tested} representative-family blocker checks')


def repair_checks():
    rng = Random(214)
    samples = 0
    # Base values all zero. Negative literals are the original true ones.
    for _ in range(80):
        rows = []
        for _ in range(18):
            variables = rng.sample(range(1, 7), 3)
            while True:
                row = tuple(v if rng.randrange(2) else -v for v in variables)
                if min(row) < 0:
                    break
            rows.append(row)
        rows += rows[:4]  # deletions distinguish different copies
        tags = lambda row: frozenset(-v for v in row if v < 0)
        groups = {}
        for i, row in enumerate(rows):
            groups.setdefault(tags(row), []).append(({v for v in row if v > 0} | {i+7}, i))
        h, r = rng.choice([0,1,2,3]), rng.choice([0,1,2])
        index = {key:representatives(records, h+r) for key, records in groups.items()}
        for _ in range(20):
            deleted = set(rng.sample(range(len(rows)), r))
            added = [tuple(v if rng.randrange(2) else -v for v in rng.sample(range(1, 7), 3))
                     for _ in range(r)]

            def violated(row, flipped):
                return all((abs(v) in flipped) != (v > 0) for v in row)

            def search(flipped):
                candidates = list(added)
                for size in range(1, 4):
                    for subset in combinations(flipped, size):
                        candidates += [rows[i] for i in index.get(frozenset(subset), [])
                                       if i not in deleted]
                bad = next((row for row in candidates if violated(row, flipped)), None)
                if bad is None:
                    return True
                return len(flipped) < h and any(
                    search(flipped | {abs(v)}) for v in bad if abs(v) not in flipped)
            active = added + [row for i, row in enumerate(rows) if i not in deleted]
            truth = any(all(not violated(row, subset) for row in active)
                        for size in range(h+1) for subset in combinations(range(1, 7), size))
            assert search(frozenset()) == truth
            samples += 1
    print(f'{samples} repair queries, including radii and edit budgets of zero')


if __name__ == '__main__':
    butterfly_checks()
    representative_checks()
    repair_checks()
