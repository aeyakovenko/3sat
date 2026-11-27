"""Packed recent variables and mixed old/recent dyadic rectangles for complete CSPs."""

from itertools import combinations, product
from math import comb
from random import Random

from complete_csp_dyadic_audit import ConstraintTable, group_keys, solve


class MacroForest:
    """At a fixed dyadic location equal stored patterns have equal identifiers."""

    def __init__(self, n, block):
        self.span = 1 << (max(1, n) - 1).bit_length()
        self.block = block
        self.radix = max(2, 1 << ((self.span.bit_length() - 1) // 2))
        self.children = [None, None]
        ids = [0, 1]
        width = 1
        while width < block:
            next_ids = []
            for code in range(1 << (2 * width)):
                low = code & ((1 << width) - 1)
                high = code >> width
                next_ids.append(len(self.children))
                self.children.append((ids[low], ids[high]))
            width *= 2
            ids = next_ids
        self.chunk_ids = ids
        self.zero_root = ids[0]
        while width < self.span:
            self.children.append((self.zero_root, self.zero_root))
            self.zero_root = len(self.children) - 1
            width *= 2

    def install(self, candidates, start):
        """Install the whole formerly-zero aligned chunk in one batched path update."""
        root = [old for old, _, _ in candidates]
        selected = [q for q, (_, recent, _) in enumerate(candidates) if recent]
        if not selected:
            return root
        nodes = [root[q] for q in selected]
        siblings = []
        width = self.span
        while width > self.block:
            width //= 2
            side = int(bool(start & width))
            pairs = [self.children[node] for node in nodes]
            siblings.append((side, [pair[1 - side] for pair in pairs]))
            nodes = [pair[side] for pair in pairs]
        assert all(node == self.chunk_ids[0] for node in nodes)
        ids = [self.chunk_ids[candidates[q][1]] for q in selected]
        for side, others in reversed(siblings):
            pairs = [(a, b) if side else (b, a) for a, b in zip(others, ids, strict=True)]
            distinct, labels = group_keys(pairs, self.radix)
            first = len(self.children)
            self.children.extend(distinct)
            ids = [first + label for label in labels]
        for q, node in zip(selected, ids, strict=True):
            root[q] = node
        return root

    def decode(self, root, n):
        level = [root]
        for _ in range(self.span.bit_length() - 1):
            level = [child for node in level for child in self.children[node]]
        return tuple(level[:n])


def child_recent(loc, width, side, code, start, block):
    """Root/ancestor code is the entire chunk; internally it is the local substring."""
    half = width // 2
    if width <= block:
        return (code >> (side * half)) & ((1 << half) - 1)
    child_start = (2 * loc + side) * half
    return code if child_start <= start < child_start + half else 0


def query(table, forest, candidates, start, stage=None):
    """stage=None returns packed flags for all future positions in this chunk."""
    dim, width, block = table.k - 1, forest.span, forest.block
    dirs = tuple(product((0, 1), repeat=dim))
    keys, root_labels = group_keys([(0,) * dim + (old,) * dim + (recent,) * dim
                                    for old, recent, _ in candidates], forest.radix)
    layers, count = [], 0
    while True:
        count += len(keys)
        blocks_at_level = forest.span // width
        selected = 1 if width >= block else block // width
        boxes = blocks_at_level**dim
        if stage is not None:
            boxes -= (blocks_at_level - selected)**dim
        union = min(table.n, dim * width)
        assert not table.complete or len(keys) <= boxes * sum(comb(union, t) for t in range(min(dim, union) + 1))
        if width == 1:
            break
        next_keys, starts = [], [0]
        half = width // 2
        for key in keys:
            locs, nodes, code = key[:dim], key[dim:2 * dim], key[2 * dim:]
            pairs = [forest.children[node] for node in nodes]
            for direction in dirs:
                places = tuple(2 * a + e for a, e in zip(locs, direction, strict=True))
                if stage is not None and not any(pos * half < start + block and (pos + 1) * half > start
                                                 for pos in places):
                    continue
                ids = tuple(pair[e] for pair, e in zip(pairs, direction, strict=True))
                words = tuple(child_recent(a, width, e, c, start, block)
                              for a, e, c in zip(locs, direction, code, strict=True))
                next_keys.append(places + ids + words)
            starts.append(len(next_keys))
        keys, labels = group_keys(next_keys, forest.radix)
        layers.append((labels, starts))
        width = half
    flags = []
    for key in keys:
        coords, old, code = key[:dim], key[dim:2 * dim], key[2 * dim:]
        bits = tuple(a | b for a, b in zip(old, code, strict=True))
        if stage is not None:
            flags.append(table.forbidden_extensions(coords, bits, stage))
        else:
            val = 0
            if all(j < start for j in coords):
                for j in range(start, min(start + block, table.n)):
                    val |= table.forbidden_extensions(coords, bits, j) << (2 * (j - start))
            flags.append(val)
    for labels, offsets in reversed(layers):
        parent = []
        for i in range(len(offsets) - 1):
            val = 0
            for q in range(offsets[i], offsets[i + 1]):
                val |= flags[labels[q]]
            parent.append(val)
        flags = parent
    return [flags[label] for label in root_labels], count


def macro_solve(table, block=None):
    if block is None:
        integer_log = max(1, (max(2, table.n)).bit_length() - 1)
        block = 1 << (integer_log.bit_length() - 1)
    forest = MacroForest(table.n, block)
    assert 0 < block <= forest.span and block & (block - 1) == 0
    roots, visits = [forest.zero_root], 0
    for start in range(0, table.n, block):
        active = [(old, 0, 0) for old in roots]
        packed, work = query(table, forest, active, start)
        visits += work
        active = [(old, 0, flags) for old, flags in zip(roots, packed, strict=True)]
        for stage in range(start, min(table.n, start + block)):
            mixed, work = query(table, forest, active, start, stage)
            visits += work
            candidates = []
            for (old, recent, flags), seen in zip(active, mixed, strict=True):
                shift = stage - start
                bans = seen | ((flags >> (2 * shift)) & 3)
                if not (bans & 1):
                    candidates.append((old, recent, flags))
                if not (bans & 2):
                    candidates.append((old, recent | (1 << shift), flags))
            active = candidates
            if not active:
                break
        roots = forest.install(active, start)
        assert len(roots) == len(set(roots))
        if not roots:
            break
    return [forest.decode(root, table.n) for root in roots], visits


def audit():
    rng = Random(917384519)
    instances = visits = runs = 0

    def check(table, widths, expected=None):
        nonlocal instances, visits, runs
        oracle = sorted(table.reference() if expected is None else expected)
        for width in widths:
            found, cells = macro_solve(table, width)
            assert sorted(found) == oracle
            visits += cells
            runs += 1
        instances += 1

    for vs in product(range(4), repeat=3):
        check(ConstraintTable(3, 2, [1 << v for v in vs]), (None, 2))
    for vs in product(range(8), repeat=4):
        check(ConstraintTable(4, 3, [1 << v for v in vs]), (None,))
    for k in (2, 3, 4):
        for n in range(max(1, k-1), 11):
            m = comb(n, k)
            span = 1 << (n - 1).bit_length()
            widths = tuple(b for b in (1, 2, 4, 8) if b <= span)
            check(ConstraintTable(n, k, [1 << ((1 << k) - 1)] * m), widths)
            for _ in range(2):
                check(ConstraintTable(n, k, [rng.randrange(1, (1 << (1 << k))) for _ in range(m)]), widths)
    n = 18
    table = ConstraintTable(n, 3, [1 << 7] * comb(n, 3))
    all_low_weights = [tuple(int(i in supp) for i in range(n))
                       for count in range(3) for supp in combinations(range(n), count)]
    check(table, (None, 8), all_low_weights)
    table = ConstraintTable(13, 3, [1 << rng.randrange(8) for _ in range(comb(13, 3))])
    baseline, _ = solve(table)
    check(table, (None, 4), baseline)
    print(f'{instances} complete instances, {runs} block-size runs, {visits} macro/dyadic keys; '
          'all returned solutions agree')


if __name__ == '__main__':
    audit()
