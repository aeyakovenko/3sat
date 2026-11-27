"""Independent semantic and aligned-word checks on the actual row-query DIMACS bytes."""

from itertools import permutations, product
from random import Random

from packed_residue_dimacs import parse_proper_dimacs
from packed_row_queries import (
    RowQueryLayout,
    mgg_codebook,
    mgg_segment,
    mgg_step,
    mgg_transition,
)


def verify_pads(clauses):
    assert all({abs(lit) for lit in c} == {1, 2, 3} for c in clauses[:7])
    legal = [
        bits
        for bits in product((False, True), repeat=3)
        if all(any(bits[abs(lit) - 1] == (lit > 0) for lit in c) for c in clauses[:7])
    ]
    assert legal == [(False, False, False)]


def evaluate(clauses, layout, row, column):
    # Ordinary unit propagation on emitted clauses, with only the three
    # independently verified pads and the chosen witness initialized.
    values = [None] * (layout.variable_count + 1)
    values[1:4] = [False] * 3
    for n, selectors in (
        (row, layout.row_selectors),
        (column, layout.column_selectors),
    ):
        for i, variable in enumerate(selectors):
            values[variable] = bool(n >> i & 1)
    pending = clauses
    while pending:
        later = []
        progress = False
        for clause in pending:
            free = []
            for literal in clause:
                val = values[abs(literal)]
                if val is None:
                    free.append(literal)
                elif val == (literal > 0):
                    break
            else:
                if not free:
                    return None
                if len(free) == 1:
                    values[abs(free[0])] = free[0] > 0
                    progress = True
                else:
                    later.append(free)
        if later and not progress:
            raise AssertionError(
                "selector assignment left residual unconstrained choices"
            )
        pending = later
    assert None not in values[1:]
    return values


def physical_packet_fields(layout, data):
    header, *_ = data.splitlines()
    assert [int(i) for i in header.split()[2:]] == [
        layout.variable_count,
        layout.clause_count,
    ]
    start = len(layout.public)
    assert (
        8 * layout.word_bytes
        == layout.word_coefficient * (8 * len(data) + 1).bit_length()
    )
    assert start % layout.word_bytes == 0
    assert len(data) == start + layout.packet_count * layout.word_bytes
    result = []
    for pos in range(start, len(data), layout.word_bytes):
        nums = list(map(int, data[pos : pos + layout.word_bytes].split()))
        if layout.half_names is not None and nums[0] in layout.half_names:
            assert nums == [nums[0], 1, 2, 0, 4, 1, 2, 0]
            result.append((layout.half_slot, nums[0] - layout.half_names.start))
            continue
        flag, name = -nums[0], nums[1]
        assert nums == [-flag, name, 1, 0, flag, -name, 1, 0]
        if flag in layout.data_flags:
            assert name in layout.data_names
            result.append(
                (flag - layout.data_flags.start, name - layout.data_names.start)
            )
        else:
            assert flag in layout.query_flags and name in layout.query_names
            result.append(
                (
                    layout.data_count + flag - layout.query_flags.start,
                    name - layout.query_names.start,
                )
            )
    return result


def check_file(layout, rows, queries, order, crosscheck_library=False, half=None):
    data = layout.render(rows, queries, order, half=half)
    packets = physical_packet_fields(layout, data)
    assert [j for j, _ in packets] == list(order)
    ordered = [0] * len(order)
    for j, value in packets:
        ordered[j] = value
    flat = [rows[j] >> i & 1 for j in range(layout.k) for i in range(layout.columns)]
    h = layout.packet_bits
    for j in range(len(flat)):
        assert (ordered[j // h] >> (j % h) & 1) == flat[j]
    if half is not None:
        assert ordered[layout.half_slot] == half
    ell = layout.columns.bit_length() - 1
    g = layout.queries_per_packet
    if layout.segment_codebook is None:
        expected = queries
        for j in range(layout.k):
            assert (
                ordered[layout.data_count + j // g] >> (ell * (j % g))
            ) % layout.columns == queries[j]
    else:
        assert (
            list(queries)
            == ordered[layout.data_count : layout.data_count + layout.query_count]
        )
        expected = [
            layout.segment_codebook[queries[j // g]][j % g] for j in range(layout.k)
        ]

    clauses = parse_proper_dimacs(data)
    verify_pads(clauses)
    split = len(clauses) - 2 * layout.packet_count
    assert clauses[split - 2][0] < 0 and clauses[split - 1][0] > 0
    unsignaled = clauses[: split - 2] + clauses[split:]
    misses = 0
    for row in range(layout.k):
        for column in range(layout.columns):
            in_half = half is None or row // (layout.k // 2) == half
            should_work = (
                in_half and column == expected[row] and not (rows[row] >> column & 1)
            )
            assignment = evaluate(clauses, layout, row, column)
            assert (assignment is not None) == should_work
            misses += assignment is not None
            if crosscheck_library and in_half:
                full = evaluate(unsignaled, layout, row, column)
                assert full is not None
                for mask, v in enumerate(layout.data_names):
                    assert full[v] == bool(
                        mask >> ((row * layout.columns + column) % h) & 1
                    )
                for mask, v in enumerate(layout.query_names):
                    if layout.segment_codebook is None:
                        entry = (mask >> (ell * (row % g))) & (layout.columns - 1)
                    else:
                        entry = layout.segment_codebook[mask][row % g]
                    assert full[v] == (entry == column)
    return misses


def check_mgg():
    # Each row is an affine map (x,y) ↦ (a*x+b*y+e, c*x+d*y+f).
    shears = (
        (1, 2, 0, 1, 0, 0),
        (1, -2, 0, 1, 0, 0),
        (1, 2, 0, 1, 1, 0),
        (1, -2, 0, 1, -1, 0),
        (1, 0, 2, 1, 0, 0),
        (1, 0, -2, 1, 0, 0),
        (1, 0, 2, 1, 0, 1),
        (1, 0, -2, 1, 0, -1),
    )
    maps = shears + ((1, 0, 0, 1, 0, 0),) * 8

    def step(m, pos, nibble):
        y, x = divmod(pos, m)
        a, b, c, d, e, f = maps[nibble]
        return ((a * x + b * y + e) % m) + m * ((c * x + d * y + f) % m)

    def reference(m, start, tag):
        pos = start
        for digit in reversed(format(tag, "0160x")):
            pos = step(m, pos, int(digit, 16))
        return pos

    for m in (2, 4, 8, 16):
        for label in range(16):
            targets = [mgg_step(m * m, pos, label) for pos in range(m * m)]
            assert sorted(targets) == list(range(m * m))
            for pos, new in enumerate(targets):
                assert new == step(m, pos, label)
                assert pos == mgg_step(m * m, new, label ^ 1 if label < 8 else label)

    rng = Random(41660)
    tags = [0, (1 << 640) - 1, 14, 5 << 636, 15 | (3 << 636)]
    tags.extend(rng.getrandbits(640) for _ in range(12))
    for m in (4, 32, 128):
        for tag in tags:
            pos = rng.randrange(m * m)
            end = mgg_transition(m * m, pos, tag)
            assert end == reference(m, pos, tag)
            digits = [tag >> (4 * j) & 15 for j in range(160)]
            inverse = sum(
                (l ^ 1 if l < 8 else l) << (4 * j)
                for j, l in enumerate(reversed(digits))
            )
            assert mgg_transition(m * m, end, inverse) == pos
    for m in (4, 16, 128):
        pos = rng.randrange(m * m)
        labels = [tags[-1], tags[-2], tags[-3]]
        seed = pos + (m * m) * sum(t << (640 * j) for j, t in enumerate(labels))
        expected = [pos]
        for t in labels:
            expected.append(reference(m, expected[-1], t))
        assert mgg_segment(m * m, 4, seed) == tuple(expected)
    assert list(mgg_codebook(16, 1, 4)) == [(i,) for i in range(16)]
    try:
        mgg_codebook(16, 2, 8)
    except ValueError:
        pass
    else:
        raise AssertionError("an oversized seed would be silently enumerated")

    # Use sampled actual powered walks as a small public table. The full
    # 640-bit transition alphabet is never enumerated in this test.
    subtable = [
        mgg_segment(4, 2, (tag << 2) | (j % 4)) for j, tag in enumerate(tags[:8])
    ]
    layout = RowQueryLayout(4, 4, 4, segment_codebook=subtable)
    q = [1, 5]
    columns = [x for s in q for x in subtable[s]]
    rows = [1 << x for x in columns]
    slots = [*range(layout.packet_count)][::-1]
    assert check_file(layout, rows, q, slots, crosscheck_library=True) == 0
    rows[2] = 0
    assert check_file(layout, rows, q, slots) == 1
    print(
        "MGG: 16 labelled permutations and their inverses on four tori; 51 powered edge "
        "labels, multiperiod seeds and two DIMACS files for sampled powered walks."
    )


def check_affine_cut_identity():
    # Restrict each actual powered seed to its low four bits. At y=0 the
    # higher zero nibbles preserve the endpoint of the first labelled move.
    k = 4
    book = [mgg_segment(4, 2, seed) for seed in range(16)]
    seed_for_path = {(0, 0): 0, (0, 1): 8, (1, 0): 13, (1, 1): 1}
    assert all(book[seed] == path for path, seed in seed_for_path.items())
    layout = RowQueryLayout(k, 4, 4, segment_codebook=book, half_tag=True)
    rng = Random(717)
    opposite = 0
    for x in range(1 << k):
        # Exactly two ones per row. Among columns 0 and 1 only x_i is good.
        rows = [4 | (1 << ((x >> i) & 1)) for i in range(k)]
        order = rng.sample(range(layout.packet_count), layout.packet_count)
        tag_start = len(layout.public) + order.index(layout.half_slot) * layout.word_bytes
        answer_row = 0
        for y in range(1 << k):
            bits = tuple((y >> i) & 1 for i in range(k))
            seeds = [seed_for_path[bits[i:i + 2]] for i in range(0, k, 2)]
            left, right = (layout.render(rows, seeds, order, half=h) for h in (0, 1))
            assert len(left) == len(right)
            differences = [i for i, (u, v) in enumerate(zip(left, right)) if u != v]
            assert len(differences) == 1
            pos = differences[0]
            assert tag_start <= pos < tag_start + layout.word_bytes
            assert (left[pos], right[pos]) == (ord("2"), ord("3"))
            misses = [check_file(layout, rows, seeds, order, half=h) for h in (0, 1)]
            differing = x ^ y
            assert misses == [(differing & 3).bit_count(), (differing >> 2).bit_count()]
            opposite += bool(misses[0]) != bool(misses[1])
            if misses == [0, 0]:
                answer_row |= 1 << y
        assert answer_row == 1 << x
    assert opposite == 96
    print("Affine-cut equality: the decoded 16-by-16 matrix is the identity over F2; "
          "512 proper DIMACS files, 256 one-bit tag pairs, 96 opposite-verdict pairs.")


def check_shared_row_group_table():
    # Use four genuine 640-bit labels without enumerating the full alphabet.
    # The second shear in the last label follows the first in execution order.
    stay = int("8" * 160, 16)
    labels = (stay, (stay & ~15) | 2, (stay & ~15) | 6, (stay & ~255) | 0x62)
    columns, group_length, word_bits = 4, 2, 3
    pieces = [(start, mgg_transition(columns, start, label))
              for label in labels for start in range(columns)]

    def pack(bits):
        return tuple(sum(bit << i for i, bit in enumerate(bits[start:start + word_bits]))
                     for start in range(0, len(bits), word_bits))

    def extract(words, index):
        return (words[index // word_bits] >> (index % word_bits)) & 1

    # Each entry depends only on row offset, mask, and packed query-word index.
    shared = [{mask: pack([(mask >> piece[j]) & 1 for piece in pieces])
               for mask in range(1 << columns)} for j in range(group_length)]

    def group_words(left, right):
        return tuple(a & b for a, b in zip(shared[0][left], shared[1][right]))

    for left, right in product(range(1 << columns), repeat=2):
        packed = group_words(left, right)
        for i, (a, b) in enumerate(pieces):
            assert extract(packed, i) == ((left >> a) & (right >> b) & 1)

    # Exhaust the four-row segment seeds over the sampled alphabet. After
    # a boundary the new piece starts at path[2], which includes the move
    # from path[1] to path[2] supplied by the middle transition.
    segments = []
    for moves in product(range(len(labels)), repeat=3):
        for start in range(columns):
            seed = start + columns * sum(labels[m] << (640 * i) for i, m in enumerate(moves))
            path = mgg_segment(columns, 4, seed)
            indices = (start + columns * moves[0], path[2] + columns * moves[2])
            assert tuple(pieces[i] for i in indices) == (path[:2], path[2:])
            segments.append((path, indices))

    baseline = tuple(j * 31 for j in range(8))
    rows = []
    for idx in baseline:
        for column in segments[idx][0]:
            rows.append((1 << column) | (1 << ((column + 1) % columns)))
    groups = [group_words(rows[i], rows[i + 1]) for i in range(0, len(rows), 2)]
    cases = [tuple((i + j) % len(segments) for j in baseline)
             for i in range(len(segments))]
    for j in (0, 4):
        # One offending segment in either half, all other segments good.
        wrong = next(i for i, (path, _) in enumerate(segments)
                     if any(not (rows[4*j + t] >> c & 1) for t, c in enumerate(path)))
        cases.append(baseline[:j] + (wrong,) + baseline[j + 1:])
    observed = set()
    reset_would_fail = False
    for case in cases:
        selected = [c for i in case for c in segments[i][0]]
        gathered = []
        for j, idx in enumerate(case):
            path, (first, second) = segments[idx]
            gathered.extend((extract(groups[2*j], first), extract(groups[2*j + 1], second)))
            wrong_start = second - path[2] + path[0]
            reset_would_fail |= extract(groups[2*j + 1], wrong_start) != gathered[-1]
        half_verdicts = []
        for h in (0, 1):
            flags = gathered[8*h:8*h + 8]
            words = pack(flags)
            # The final short word must compare against only its two live bits.
            miss = words != pack([1] * len(flags))
            assert miss == any(not (rows[i] >> selected[i] & 1)
                               for i in range(16*h, 16*h + 16))
            half_verdicts.append(miss)
        observed.add(tuple(half_verdicts))
    assert reset_would_fail and len(observed) == 4
    print("Shared row-group table: 4,096 mask/path predicates, all 256 powered-walk "
          "segments on the four-label subalphabet, 258 whole queries and both half tags; "
          "resetting at a boundary changes a group bit and packed flags cross words.")


def audit():
    check_mgg()
    check_affine_cut_identity()
    check_shared_row_group_table()
    small = RowQueryLayout(2, 2, 2, 2)
    all_slots = list(permutations(range(small.packet_count)))
    yes = no = count = 0
    for rows in product(range(4), repeat=2):
        for queries in product(range(2), repeat=2):
            for order in all_slots:
                misses = check_file(small, rows, queries, order)
                yes += bool(misses)
                no += not misses
                count += 1
    rng = Random(532068)
    large = 0
    for k, b, h, g in ((8, 2, 8, 8), (16, 4, 8, 4), (8, 2, 4, 2)):
        layout = RowQueryLayout(k, b, h, g)
        order = rng.sample(range(layout.packet_count), layout.packet_count)
        queries = [rng.randrange(b) for _ in range(k)]
        rows = [rng.randrange(1 << b) | (1 << column) for column in queries]
        assert check_file(layout, rows, queries, order, crosscheck_library=True) == 0
        selected = rng.sample(range(k), k // 2)
        for j in selected:
            rows[j] ^= 1 << queries[j]
        assert check_file(layout, rows, queries, order) == len(selected)
        large += 2
    # A shared table of genuine two-choice walks on eight columns. The
    # 4*3 raw column bits for each path would exceed the eight-bit data packet.
    book = []
    for seed in range(64):
        path = [seed & 7]
        for j in range(3):
            path.append((path[-1] + (1 if seed >> (3 + j) & 1 else -1)) % 8)
        book.append(path)
    layout = RowQueryLayout(16, 8, 8, segment_codebook=book)
    ordering = rng.sample(range(layout.packet_count), layout.packet_count)
    seeds = [1, 19, 19, 63]
    columns = [col for seed in seeds for col in book[seed]]
    rows = [1 << col for col in columns]
    assert check_file(layout, rows, seeds, ordering, crosscheck_library=True) == 0
    rows[7] = 0
    assert check_file(layout, rows, seeds, ordering) == 1
    changed = seeds.copy()
    changed[2] = 2
    orig, edit = (
        layout.render(rows, seeds, ordering),
        layout.render(rows, changed, ordering),
    )
    delta = {
        i // layout.word_bytes for i, (x, y) in enumerate(zip(orig, edit)) if x != y
    }
    assert delta == {
        len(layout.public) // layout.word_bytes + ordering.index(layout.data_count + 2)
    }
    # Duplicated paths retain separate seed IDs without adding SAT witnesses.
    long_book = [tuple((seed + j) % 4 for j in range(8)) for seed in (0, 1, 1, 3)]
    layout = RowQueryLayout(16, 4, 8, segment_codebook=long_book, word_coefficient=64)
    order = rng.sample(range(layout.packet_count), layout.packet_count)
    assert check_file(layout, [0] * 16, [1, 2], order, crosscheck_library=True) == 16
    # Retain B,h,d,C when halving the problem size. Exercise both native
    # query modes and mix all three kinds of packet at real physical addresses.
    for k, table in ((16, None), (8, book)):
        layout = RowQueryLayout(
            k,
            8,
            8,
            queries_per_packet=2 if table is None else 4,
            segment_codebook=table,
            half_tag=True,
            word_coefficient=64,
        )
        inherited = RowQueryLayout(
            k // 2,
            layout.columns,
            layout.packet_bits,
            layout.queries_per_packet,
            segment_codebook=table,
            half_tag=True,
            word_coefficient=64,
        )
        for tagged in (layout, inherited):
            query = (
                [j % 8 for j in range(tagged.k)]
                if table is None
                else [19] * tagged.query_count
            )
            rows = [255] * tagged.k
            rows[0] = rows[1] = 0
            # Tag position varies; in particular there are data after a query.
            order = [0, tagged.data_count, tagged.half_slot]
            order += [i for i in range(tagged.packet_count) if i not in order]
            raw0 = tagged.render(rows, query, order, half=0)
            raw1 = tagged.render(rows, query, order, half=1)
            changes = [i for i, (u, v) in enumerate(zip(raw0, raw1)) if u != v]
            assert len(changes) == 1 and len(raw0) == len(raw1)
            changed = changes[0]
            assert raw0[changed] == ord("2") and raw1[changed] == ord("3")
            assert (raw0[changed] ^ raw1[changed]).bit_count() == 1
            assert (changed - len(tagged.public)) // tagged.word_bytes == order.index(
                tagged.half_slot
            )
            assert check_file(tagged, rows, query, order, half=0) == 2
            assert check_file(tagged, rows, query, order, half=1) == 0
    print(
        "Four opposite-verdict pairs in both query modes and inherited half sizes "
        "differ in exactly one physical bit; complete raw model counts are 2 and 0."
    )
    print(
        "Shared segment mode: all 64 walk functions checked, both verdicts, a one-word "
        "seed edit, duplicated seed paths and eight rows per seed; exact word widths verified."
    )
    print(
        f"{count} actual small files ({yes} SAT, {no} UNSAT) including every packet permutation."
    )
    print(
        f"{large} additional files; all mask outputs checked at every selector; "
        "each miss has one complete assignment, with up to eight queries per word."
    )


if __name__ == "__main__":
    audit()
