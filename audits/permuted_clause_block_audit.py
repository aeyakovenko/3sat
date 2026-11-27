"""Check byte-aligned proper 2-CNF files with arbitrary fixed second-section order."""

from itertools import combinations, groupby, product

from transpose_tape_2cnf_audit import digits, is_satisfiable


def serialize(left, right, order, group_size, width):
    m = len(order)
    assert sorted(order) == list(range(m)) and m % group_size == 0
    assert len(left) == len(right) == m
    coord = m.bit_length()

    def p(j):
        return '1' + digits(j, coord) + '1' * width

    def x(j, value):
        return '2' + digits(j, coord) + digits(value, width)

    aux = '3' + '1' * (coord + width)
    anchors = [f'{p(0)} {aux}', f'{p(0)} -{aux}', f'-{p(m)} {aux}', f'-{p(m)} -{aux}']
    prefix = f'p cnf {aux} {2*m+4}\n' + ''.join(f'{row} 0\n' for row in anchors)
    rows = [f'-{p(j)} {x(j, value)} 0' for j, value in enumerate(left)]
    rows.extend(f'-{x(j, right[i])} {p(j+1)} 0' for i, j in enumerate(order))
    slot = 8 * ((len(rows[0]) + 1 + 7) // 8)
    block = group_size * slot
    prefix = prefix[:-1] + ' ' * (-len(prefix) % block) + '\n'
    assert len(prefix) % block == 0 and all(len(row) < slot for row in rows)
    data = ''.join(row.ljust(slot-1) + '\n' for row in rows)
    return (prefix + data).encode('ascii'), len(prefix), slot


def decode(raw, start, slot, m, width):
    coord = m.bit_length()
    assert len(raw) == start + 2 * m * slot
    header, *anchors = raw[:start].splitlines()
    assert int(header.split()[3]) == 2 * m + 4 and len(anchors) == 4
    assert all(len({abs(int(a)) for a in row.split()[:-1]}) == 2 for row in anchors)

    def unpack(name, tag):
        assert len(name) == 1 + coord + width and name.startswith(tag)
        assert all(byte in b'12' for byte in name[1:])
        bits = name[1:].translate(bytes.maketrans(b'12', b'01'))
        return int(bits[:coord], 2), int(bits[coord:], 2)

    records = []
    for i in range(2*m):
        line = raw[start + i*slot:start + (i+1)*slot]
        neg, pos, zero = line.split()
        assert line.endswith(b'\n') and zero == b'0' and neg.startswith(b'-')
        if i < m:
            p, pad = unpack(neg[1:], b'1')
            j, value = unpack(pos, b'2')
            assert p == j == i
        else:
            j, value = unpack(neg[1:], b'2')
            p, pad = unpack(pos, b'1')
            assert p == j + 1
        assert pad == 0
        records.append((j, value))
    return records[:m], records[m:]


def check(left, right, order, d, width):
    raw, start, slot = serialize(left, right, order, d, width)
    actual_left, actual_right = decode(raw, start, slot, len(order), width)
    assert actual_left == list(enumerate(left)) and actual_right == list(zip(order, right))
    assert is_satisfiable(raw) == (dict(actual_left) != dict(actual_right))
    return raw, start, slot


def minimum(left, right, d, k):
    def selected(records):
        groups = [set(j for j, _ in records[i:i+d]) for i in range(0, len(records), d)]
        return [(index, set.union(*(groups[j] for j in index)))
                for index in combinations(range(len(groups)), k)]

    xs, ys = selected(left), selected(right)
    matches, lg, rg = min((len(a & b), i, j) for i, a in xs for j, b in ys)
    return matches, lg, rg, len(xs) * len(ys)


def audit_layout(label, order, d, k, expected_min):
    m, width = len(order), 3
    left = tuple((j * j + 3*j + j//5) % (1 << width) for j in range(m))
    right = tuple(left[j] for j in order)
    base, start, slot = check(left, right, order, d, width)
    decoded = decode(base, start, slot, m, width)
    count, lg, rg, pairs = minimum(*decoded, d, k)
    assert count == expected_min
    block = d * slot
    assert start % block == (start + m*slot) % block == 0
    for half, data in enumerate((left, right)):
        for pos in range(m):
            for bit in range(width):
                edit = list(data)
                edit[pos] ^= 1 << bit
                pair = (edit, right) if half == 0 else (left, edit)
                raw, start2, slot2 = check(*pair, order, d, width)
                assert (len(raw), start2, slot2) == (len(base), start, slot)
                changed = [u for u, (x, y) in enumerate(zip(base, raw)) if x != y]
                assert len(changed) == 1
                u = changed[0]
                assert {base[u], raw[u]} == {ord('1'), ord('2')}
                assert (u - start) // slot == half*m + pos
                assert u // block == start//block + half*(m//d) + pos//d
    print(f'{label}: cells={m} block_bytes={block} start={start} second={start+m*slot} '
          f'k={k} group_pairs={pairs} min={count} example={lg}/{rg} '
          f'one_bit_mismatches={2*m*width}')


def transpose_splice():
    """Two-bank toy execution with repeated visits and recorded work-path cuts."""
    side, d = 6, 3
    m = side * side
    h = m // d
    order = tuple((i % side) * side + i // side for i in range(m))
    zero = [0] * m
    first, start, slot = check(zero, zero, order, d, 1)
    left, right = decode(first, start, slot, m, 1)
    low, _, _, pairs = minimum(left, right, d, 3)
    assert low == 0
    block = d * slot
    # Each tuple is (input block relative to the first data block, work block).
    visits = [(half*h + g, g % 2) for g in range(h) for _ in range(2) for half in (0, 1)]
    chains = [[i for i, (_, work) in enumerate(visits) if work == w] for w in (0, 1)]
    color, interval = {}, {}
    for w, path in enumerate(chains):
        for off in range(0, len(path), 2):
            rows = path[off:off+2]
            g = visits[rows[0]][0]
            red = (g < h//2) != (g in (1, 9) and off % 4 == 2)
            for i in rows:
                color[i], interval[i] = red, (w, off//2)

    occurrences = [[i for i, (lab, _) in enumerate(visits) if lab == label] for label in range(2*h)]
    colors = [{color[i] for i in occ} for occ in occurrences]
    intervals = [{interval[i] for i in occ} for occ in occurrences]
    right_group = {j: h+i//d for i, (j, _) in enumerate(right)}
    edges = {(j//d, right_group[j]): j for j, _ in left}
    assert len(edges) == m
    cross = {(u, v): j for (u, v), j in edges.items() if colors[u] == {True} and colors[v] == {False}}
    collisions = sum(bool(intervals[u] & intervals[v]) for u, v in edges)
    # Find an actual 4-cycle. Flipping its four low data digits leaves the
    # parity of every affected input block fixed at each segment boundary.
    cycle = next([cross[u, v] for u in us for v in vs]
                 for us in combinations(range(h), 2) for vs in combinations(range(h, 2*h), 2)
                 if all((u, v) in cross for u in us for v in vs))
    changed = [int(j in cycle) for j in range(m)]
    second, s2, z2 = check(changed, [changed[j] for j in order], order, d, 1)
    assert (s2, z2) == (start, slot) and first[:start] == second[:start]

    def input_block(raw, label):
        return raw[start + label*block:start + (label+1)*block]

    mixed = bytearray(first)
    for label, palette in enumerate(colors):
        if palette == {False}:
            mixed[start+label*block:start+(label+1)*block] = input_block(second, label)
        elif len(palette) == 2:
            assert input_block(first, label) == input_block(second, label)
    mixed = bytes(mixed)
    a, b = decode(mixed, start, slot, m, 1)
    assert {j for j, value in a if value != dict(b)[j]} == set(cycle)
    assert not is_satisfiable(first) and not is_satisfiable(second) and is_satisfiable(mixed)

    def replay(raw):
        control, work = 0, [0, 0]
        tape = []
        for label, w in visits:
            chunk = input_block(raw, label)
            state = (control, work[w])
            parity = sum(chunk) % 2
            control, work[w] = work[w] ^ parity, control ^ work[w] ^ parity
            tape.append((state, (control, work[w]), chunk))
        return tape

    t1, t2, tm = map(replay, (first, second, mixed))
    assert any(x[2] != y[2] for x, y in zip(t1, t2))
    for i in range(len(visits)):
        assert t1[i][:2] == t2[i][:2]
        assert tm[i] == (t1[i] if color[i] else t2[i])
    cuts = sum(interval[i] != interval[j] for path in chains for i, j in zip(path, path[1:]))
    print(f'transpose_6x6: rectangle_pairs={pairs} minimum={low} visits={len(visits)} '
          f'work_path_cuts={cuts} same_interval_slots={collisions} red_left_blue_right={len(cross)} '
          f'mixed_palette_groups={sum(len(c)==2 for c in colors)} spliced_mismatches={cycle}')


def global_changes(requests, scales):
    """Count constant-block runs in each bank after deinterleaving it."""
    return tuple(sum(sum(1 for _ in groupby(a // scale for b, a in requests if b == bank))
                     for bank in (0, 1)) for scale in scales)


def segment_record(requests, incoming, scales, cap):
    last = list(incoming)
    counts = [0] * len(scales)
    for bank, a in requests:
        old = last[bank]
        for i, scale in enumerate(scales):
            counts[i] += old is None or a // scale != old // scale
        last[bank] = a
    rounded = tuple(1 << (min(v, cap).bit_length()-1) if v else 0 for v in counts)
    assert all(x >= y for x, y in zip(rounded, rounded[1:]))
    assert all(v <= c and 2*v >= min(c, cap) for v, c in zip(rounded, counts))
    return (incoming, tuple(last), rounded), tuple(counts)


def profile(segments, scales, cap):
    last, records, counts = (None, None), [], []
    for segment in segments:
        rec, changes = segment_record(segment, last, scales, cap)
        last = rec[1]
        records.append(rec)
        counts.append(changes)
    total = global_changes([e for seg in segments for e in seg], scales)
    assert tuple(map(sum, zip(*counts))) == total
    lower = tuple(map(sum, zip(*(rec[2] for rec in records))))
    # min(total, cap) dominates every reached threshold R_i <= cap.
    assert all(q <= t and 2*q >= min(t, cap) for q, t in zip(lower, total))
    return records, total, lower


def multiscale():
    scales = (1, 2, 4)
    alphabet = tuple(product(range(2), range(4)))
    audited = 0
    for trace in product(alphabet, repeat=4):
        for mask in range(8):
            cuts = [0] + [j for j in range(1, 4) if mask & (1 << (j-1))] + [4]
            profile([trace[l:r] for l, r in zip(cuts, cuts[1:])], scales, cap=3)
            audited += 1
    # At scale four each segment starts with exactly one charged request.
    # A native conditional probe inside its coarse block changes the fine
    # profile by one, while preserving all rounded counts and endpoints.
    def visit(base, extra):
        addresses = [base, base+2, base+3] + ([base+1] if extra else []) + [base]
        return [(0, addresses[0]), (1, 0)] + [(0, v) for v in addresses[1:]]

    def toy(bits):
        return [[(0, 0)], [(1, 0)], visit(4, bits[0]), visit(0, bits[1])]

    reports = [profile(toy(bits), scales, cap=16) for bits in ((0, 0), (1, 1), (0, 1))]
    assert reports[0][0] == reports[1][0] == reports[2][0]
    source_a, source_b, mixed = toy((0, 0)), toy((1, 1)), toy((0, 1))
    assert source_a[2] != source_b[2] and source_a[3] != source_b[3]
    assert mixed == source_a[:3] + source_b[3:]
    records, middle, lower = reports[2]
    assert all(r[2][-1] == 1 for r in records)
    assert reports[0][1][0] < middle[0] < reports[1][1][0]
    assert all(real >= credited for real, credited in zip(middle, lower))

    # A negative control uses genuine size-2 segment boundaries in bank 1.
    # Incoming addresses 0 and 1 in bank 0 have the same coarse ID. Copying
    # segments alternately now suppresses the supposed fine boundary changes.
    def control(seed):
        return [[(0, seed)]] + [[(1, 2*(i % 2)), (0, (i+1+seed) % 2)] for i in range(6)]

    a, b = control(0), control(1)
    broken = [a[i] if i % 2 == 0 else b[i] for i in range(len(a))]
    ra, rb, rm = [profile(s, scales, cap=16) for s in (a, b, broken)]

    def coarse(pair):
        return tuple(None if addr is None else addr//2 for addr in pair)

    assert all(q[1] == 1 for _, _, q in ra[0])
    assert [(coarse(i), coarse(o), q) for i, o, q in ra[0]] == [
        (coarse(i), coarse(o), q) for i, o, q in rb[0]]
    assert ra[0] != rb[0] and rm[1][0] < ra[2][0]
    print(f'multiscale: traces={len(alphabet)**4} partitions={audited} scales={scales} '
          f'source_totals={reports[0][1]}/{reports[1][1]} mixed={middle} pooled_lower={lower} '
          f'coarse_only_splice_credited={ra[2][0]} actual={rm[1][0]}')


def main():
    all_words = list(product(range(2), repeat=4))
    orders = ((0, 1, 2, 3), (1, 3, 0, 2))
    for order in orders:
        for left in all_words:
            for right in all_words:
                check(left, right, order, 2, 1)
    print(f'exhaustive_4_cell_files={len(orders)*len(all_words)**2}')
    audit_layout('identity', tuple(range(32)), 4, 3, 0)
    audit_layout('affine_5i_plus_1_mod_32', tuple((5*i+1) % 32 for i in range(32)), 4, 3, 2)
    fano = tuple(((g+s) % 7)*3 + j for g in range(7) for j, s in enumerate((0, 1, 3)))
    audit_layout('cyclic_013_mod_7', fano, 3, 3, 2)
    transpose_splice()
    multiscale()


if __name__ == '__main__':
    main()
