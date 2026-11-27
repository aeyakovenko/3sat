"""Check forced chunk bits, a mixed ternary rectangle, and cardinality-ordered siblings."""

from bisect import bisect_left
from collections import Counter
from functools import cache
from itertools import combinations, product
from random import Random

from balanced_incomplete_split_audit import independent_weights, layout
from complete_csp_dyadic_audit import group_keys
from complete_csp_macro_audit import MacroForest, query
from incomplete_triple_rectangle_audit import PaddedTriples


def sibling_weights(n, supports, cutoff=None):
    full = (1 << n) - 1
    missing = [[full] * n for _ in range(n)]
    for x, y, z in supports:
        for a, b, c in ((x, y, z), (x, z, y), (y, z, x)):
            missing[a][b] &= ~(1 << c)
    # Each entry is (id, parent id, last, at most first three, D(S), C(parent,last)).
    level = [(0, -1, -1, (), full, full)]
    weights = Counter()
    count = 1
    while level:
        siblings = sorted((p, s, old_link) for _, p, s, _, _, old_link in level)
        next_level = []
        for idx, p, s, first, available, _ in level:
            while available:
                bit = available & -available
                available ^= bit
                x = bit.bit_length() - 1
                link = full
                if s >= 0:
                    at = bisect_left(siblings, (p, x, -1))
                    par, child, cached = siblings[at]
                    assert (par, child) == (p, x)
                    link = cached & missing[s][x]
                head = first + (x,) if len(first) < 3 else first
                if len(head) == 3:
                    weights[head] += 1
                next_level.append((count, idx, x, head, link & available, link))
                count += 1
                if cutoff is not None and count > cutoff:
                    raise OverflowError('independent-set cap exceeded')
        level = next_level
    return weights, count


def install_grouped(forest, rows, start):
    """Top-down unique affected states, then install their new nodes bottom-up."""
    keys, roots = group_keys([(old, recent) for old, recent, _ in rows], forest.radix)
    layers = []
    width = forest.span
    while width > forest.block:
        width //= 2
        side = int(bool(start & width))
        child_keys = [(forest.children[old][side], word) for old, word in keys]
        following, labels = group_keys(child_keys, forest.radix)
        layers.append((side, keys, labels))
        keys = following
    assert all(old == forest.chunk_ids[0] for old, _ in keys)
    value = [forest.chunk_ids[word] for _, word in keys]
    for side, parents, labels in reversed(layers):
        parent_value = []
        for (old, word), label in zip(parents, labels, strict=True):
            if not word:
                node = old
            else:
                other = forest.children[old][1 - side]
                child = value[label]
                node = len(forest.children)
                forest.children.append((other, child) if side else (child, other))
            parent_value.append(node)
        value = parent_value
    return [value[label] for label in roots]


@cache
def separated_flags(width):
    """An old-pair leaf stores interleaved bans on bit zero and bit one."""
    table = [(0, 0)] * (1 << (2 * width))
    for x in range(1, len(table)):
        lo, hi = table[x >> 2]
        table[x] = (2 * lo + (x & 1), 2 * hi + ((x >> 1) & 1))
    return table


def local_chunk(table, start, width):
    real = [i for i in range(start, start + width) if table.old[i] < table.actual_size]
    missing = any(tuple(sorted(table.old[i] for i in t)) not in table.masks for t in combinations(real, 3))
    if missing:
        return None, None
    real_mask = sum(1 << (j - start) for j in real)
    allowed = []
    for word in range(1 << width):
        if word & ~real_mask:
            continue
        for a, b, c in combinations(real, 3):
            va, vb, vc = ((word >> (t - start)) & 1 for t in (a, b, c))
            if (table.forbidden_extensions((a, b), (va, vb), c) >> vc) & 1:
                break
        else:
            allowed.append(word)
    assert len(allowed) <= 1 + len(real) + len(real) * (len(real) - 1) // 2
    return allowed, real_mask


def block_mixed(table, forest, rows, start):
    """One old axis starts at full span. Two recent axes start at the present chunk."""
    width, new_width = forest.span, forest.block
    keys, root_labels = group_keys([(0, 0, 0, a, y, y) for a, y, _ in rows], forest.radix)
    levels, seen = [], 0
    while width > 1:
        seen += len(keys)
        next_keys = []
        both = width == new_width
        half = width // 2
        new_half = new_width // 2 if both else new_width
        for i, j, k, old, first, second in keys:
            for e, child in enumerate(forest.children[old]):
                if both:
                    mask = (1 << new_half) - 1
                    for f, g in product((0, 1), repeat=2):
                        next_keys.append((2*i+e, 2*j+f, 2*k+g, child,
                                          (first >> (new_half*f)) & mask,
                                          (second >> (new_half*g)) & mask))
                else:
                    next_keys.append((2*i+e, j, k, child, first, second))
        keys, labels = group_keys(next_keys, forest.radix)
        levels.append((8 if both else 2, labels))
        width, new_width = half, new_half
    seen += len(keys)
    flags = []
    for old_pos, j, k, old, a, b in keys:
        invalid = False
        if old_pos < start and j < k:
            bans = table.forbidden_extensions((old_pos, start+j), (old, a), start+k)
            invalid = bool((bans >> b) & 1)
        flags.append(invalid)
    for branch, labels in reversed(levels):
        flags = [any(flags[j] for j in labels[i:i+branch]) for i in range(0, len(labels), branch)]
    return [flags[label] for label in root_labels], seen


@cache
def compact_chunk(width):
    """Indexed by (mask, word), keeping selected bits in their original order."""
    size = 1 << width
    entries = []
    for mask in range(size):
        positions = [i for i in range(width) if mask & (1 << i)]
        entries.append([sum(((word >> pos) & 1) << j for j, pos in enumerate(positions))
                        for word in range(size)])
    return entries


def packed_solutions(table, forest, roots, word_bits):
    """Traverse whole chunks, omit padded holes and emit native packed vectors."""
    width = forest.block
    assert width <= word_bits
    code = [None] * (max(forest.chunk_ids) + 1)
    for w, node in enumerate(forest.chunk_ids):
        code[node] = w
    masks = [sum((table.old[pos+j] < table.actual_size) << j for j in range(width))
             for pos in range(0, forest.span, width)]
    compact = compact_chunk(width)
    word_mask = (1 << word_bits) - 1
    for root in roots:
        nodes = [root]
        while len(nodes) < len(masks):
            nodes = [child for node in nodes for child in forest.children[node]]
        out = []
        word = used = 0
        for node, mask in zip(nodes, masks, strict=True):
            chunk = compact[mask][code[node]]
            bits = mask.bit_count()
            # The native implementation never creates a temporary > word_bits.
            room = word_bits - used
            word |= (chunk & ((1 << room) - 1)) << used
            if bits >= room:
                out.append(word)
                word, used = chunk >> room, bits - room
            else:
                used += bits
            assert word <= word_mask and used < word_bits
        if used:
            out.append(word)
        assert len(out) == (table.actual_size + word_bits - 1) // word_bits
        yield out


def output_solver(n, masks, width=None):
    weights, n_ind = sibling_weights(n, masks)
    places, _ = layout(n, weights)
    table = PaddedTriples(places, n, masks)
    if width is None:
        quarter_log = max(1, n.bit_length() // 4)
        width = 1 << (quarter_log.bit_length() - 1)
    forest = MacroForest(len(places), width)
    roots = [forest.zero_root]
    amb = seen = good = bad = 0
    for start in range(0, forest.span, width):
        rows = [(root, 0, 0) for root in roots]
        packed, work = query(table, forest, rows, start)
        seen += work
        valid, real_mask = local_chunk(table, start, width)
        if valid is None:
            bad += 1
            rows = [(root, 0, bans) for root, bans in zip(roots, packed, strict=True)]
            for j in range(start, start + width):
                mix, work = query(table, forest, rows, start, j)
                seen += work
                next_rows = []
                for (old, recent, all_bans), mixed in zip(rows, mix, strict=True):
                    offset = j - start
                    bans = mixed | ((all_bans >> (2 * offset)) & 3)
                    if table.old[j] >= n:
                        bans |= 2
                    for bit in (0, 1):
                        if not ((bans >> bit) & 1):
                            next_rows.append((old, recent | (bit << offset), all_bans))
                rows = next_rows
        else:
            good += 1
            lookup = [False] * (1 << width)
            for y in valid:
                lookup[y] = True
            full = (1 << width) - 1
            candidates = []
            for root, all_bans in zip(roots, packed, strict=True):
                no0, no1 = separated_flags(width)[all_bans]
                no1 |= full & ~real_mask
                ambiguous = real_mask & ~(no0 | no1)
                amb += ambiguous.bit_count()
                if no0 & no1:
                    continue
                if not ambiguous:
                    if lookup[no0]:
                        candidates.append((root, no0, 0))
                else:
                    for y in valid:
                        if not ((no0 & ~y) or (no1 & y)):
                            candidates.append((root, y, 0))
            fails, work = block_mixed(table, forest, candidates, start)
            seen += work
            rows = [row for row, mismatch in zip(candidates, fails, strict=True) if not mismatch]
        roots = install_grouped(forest, rows, start)
        assert len(roots) == len(set(roots))
        if not roots:
            break
    assert amb <= n_ind
    final = [forest.decode(root, forest.span) for root in roots]
    assert all(not row[places[j]] for row in final for j in range(n, forest.span))
    # The externally visible dictionary follows the selected layout; compare the
    # actual words with an independent single-bit decode in canonical name order.
    names = [variable for variable in table.old if variable < n]
    native_width = max(width, n.bit_length())
    answer = []
    for row, words in zip(final, packed_solutions(table, forest, roots, native_width), strict=True):
        named = [0] * n
        for i, var in enumerate(names):
            named[var] = (words[i // native_width] >> (i % native_width)) & 1
        assert tuple(named) == tuple(row[places[j]] for j in range(n))
        answer.append(tuple(named))
    return answer, (amb, seen, good, bad)


def audit():
    rng = Random(270512)
    calls = 0
    total = [0] * 4
    for n in range(3, 11):
        triples = list(combinations(range(n), 3))
        for mode in range(11):
            masks = {t: 1 << rng.randrange(8) for t in triples if rng.randrange(10) >= mode}
            if mode in (1, 2):
                masks = {t: 1 << 7 for t in triples if t[-1] >= n // (mode + 1)}
            weights, ct = sibling_weights(n, masks)
            assert (weights, ct) == independent_weights(n, masks)
            assert sibling_weights(n, masks, ct)[1] == ct
            try:
                sibling_weights(n, masks, ct - 1)
            except OverflowError:
                pass
            else:
                raise AssertionError('sibling budget not enforced')
            brute = [a for a in product((0, 1), repeat=n)
                     if all(not ((mask >> (4*a[x]+2*a[y]+a[z])) & 1) for (x,y,z), mask in masks.items())]
            widths = [q for q in (1, 2, 4, 8) if q <= 1 << (n-1).bit_length()]
            for q in widths:
                found, stats = output_solver(n, masks, q)
                assert sorted(found) == brute
                total = [x+y for x, y in zip(total, stats, strict=True)]
                calls += 1
    for n, exceptional in ((13, 7), (14, 8), (15, 6)):
        masks = {t: 1 << 7 for t in combinations(range(n), 3) if t[-1] >= exceptional}
        expected = {tuple(int(bool(mask & (1 << j))) for j in range(n))
                    for mask in range(1 << n) if mask.bit_count() <= 2 or mask < 1 << exceptional}
        for q in (2, 4, 8):
            found, stats = output_solver(n, masks, q)
            assert set(found) == expected
            total = [x+y for x, y in zip(total, stats, strict=True)]
            calls += 1
    assert all(total)
    print(f'{calls} complete and partial runs, {total[0]} ambiguous row-variable pairs, '
          f'{total[1]} dyadic keys, {total[2]} good chunks and {total[3]} fallback chunks')


if __name__ == '__main__':
    audit()
