"""Check a rectangular word transpose and batched proper DIMACS on one database."""

from functools import cache
from itertools import product
from random import Random

from packed_residue_dimacs import parse_proper_dimacs
from packed_row_queries import RowQueryLayout, mgg_segment, mgg_transition
from packed_row_queries_audit import evaluate, physical_packet_fields


def pack(values, bits):
    return sum(value << (bits * i) for i, value in enumerate(values))


def transpose_tiles(words, fields, width):
    """Swap row index bits with the low field-index bits in every square tile."""
    panel = len(words)
    assert panel & (panel - 1) == 0 and fields % panel == 0
    result = list(words)
    stride = 1
    while stride < panel:
        shift = stride * width
        mask = pack([0 if j & stride else (1 << width) - 1 for j in range(fields)], width)
        for row in range(panel):
            if not row & stride:
                other = row + stride
                changed = ((result[row] >> shift) ^ result[other]) & mask
                result[row] ^= changed << shift
                result[other] ^= changed
        stride *= 2
    return result


def check_transpose():
    cases = 0
    for field_count in (1, 2, 4, 8):
        for panel in (1, 2, 4, 8):
            if panel > field_count:
                continue
            for width in (1, 3, 4):
                # Each basis bit gets its prescribed image, including rectangular tiles.
                for row, col, bit in product(range(panel), range(field_count), range(width)):
                    source = [0] * panel
                    source[row] = 1 << (width * col + bit)
                    expected = [0] * panel
                    expected[col % panel] = 1 << (width * (col - col % panel + row) + bit)
                    assert transpose_tiles(source, field_count, width) == expected
                    cases += 1
    return cases


LABELS = (0, 2, 4, 6)


def walk(seed):
    start, moves = seed
    raw = start + 4 * sum(LABELS[m] << (640 * j) for j, m in enumerate(moves))
    return mgg_segment(4, 4, raw)


@cache
def advance(rows, starts, lanes, panel):
    """One entry of the universal CPU lookup table for two rows and four columns."""
    ending = []
    misses = []
    for i in range(panel):
        column = (starts >> (2 * i)) & 3
        piece = (lanes >> (4 * i)) & 15
        miss = False
        for j, row in enumerate(rows):
            miss |= not (row >> column & 1)
            column = mgg_transition(4, column, LABELS[(piece >> (2 * j)) & 3])
        ending.append(column)
        misses.append(int(miss))
    return pack(ending, 2), pack(misses, 1)


def panel_answers(rows, seeds):
    """For four-row segments use two packed fields per seed, two labels per field."""
    answer = 0
    panel = len(seeds)
    for seg in range(len(rows) // 4):
        starts = []
        words = []
        for query in seeds:
            start, moves = query[seg]
            starts.append(start)
            words.append(pack([pack(moves[:2], 2), pack([moves[2], 0], 2)], 4))
        state = pack(starts, 2)
        transposed = transpose_tiles(words, 2, 4)
        for j in range(2):
            lanes = transposed[j % panel] >> (4 * (j - j % panel))
            start_row = 4 * seg + 2 * j
            state, misses = advance(tuple(rows[start_row:start_row + 2]), state, lanes, panel)
            answer |= misses
    return [(answer >> i) & 1 for i in range(panel)]


def check_formulas():
    rng = Random(7183)
    code = [(start, moves) for start in range(4) for moves in
            ((0, 1, 2), (1, 3, 0), (3, 1, 3), (2, 2, 1))]
    book = [walk(seed) for seed in code]
    tested = combinations = 0
    seen = set()
    for q in (2, 4):
        layout = RowQueryLayout(8, 4, 4, segment_codebook=book, batch_size=q)
        assert layout.data_count == 8 and layout.query_count == 2 * q
        for trial in range(24):
            ids = [[rng.randrange(len(code)) for _ in range(2)] for _ in range(q)]
            paths = [book[a] + book[b] for a, b in ids]
            if trial == 0:
                rows = [15] * 8
            elif trial == 1:
                rows = [0] * 8
            else:
                rows = [rng.randrange(16) | (1 << c) for c in paths[trial % q]]
            expected = [any(not (rows[j] >> c & 1) for j, c in enumerate(path))
                        for path in paths]
            pieces = [[code[a], code[b]] for a, b in ids]
            packed = []
            for j in range(0, q, 2):
                packed.extend(panel_answers(rows, pieces[j:j + 2]))
            assert packed == expected
            for j in range(q):
                assert panel_answers(rows, pieces[j:j + 1]) == [expected[j]]
            order = rng.sample(range(layout.packet_count), layout.packet_count)
            flat_ids = [i for query in ids for i in query]
            raw = layout.render(rows, flat_ids, order)
            assert dict(physical_packet_fields(layout, raw)) == dict(enumerate(rows + flat_ids))
            clauses = parse_proper_dimacs(raw)
            for j, path in enumerate(paths):
                pins = tuple((v if j >> bit & 1 else -v, 1, 2)
                             for bit, v in enumerate(layout.batch_selectors))
                witnesses = {(row, col) for row in range(8) for col in range(4)
                             if evaluate(clauses + pins, layout, row, col) is not None}
                assert witnesses == {(row, col) for row, col in enumerate(path)
                                     if not (rows[row] >> col & 1)}
                assert bool(witnesses) == expected[j]
                combinations += 32
            seen.add((any(expected), all(expected)))
            tested += 1
    assert seen == {(False, False), (True, False), (True, True)}
    return tested, combinations


def check_pair_rank():
    # Powered +/- one along the torus x-axis, for every value of y.
    held = int("8" * 160, 16)
    move = ((held & ~255) | 0x12, (held & ~255) | 0x30)
    torus_moves = 0
    for columns in (4, 16, 64, 256):
        side = 1 << ((columns.bit_length() - 1) // 2)
        for vertex in range(columns):
            x, y = vertex % side, vertex // side
            for label, delta in zip(move, (1, -1)):
                assert mgg_transition(columns, vertex, label) == y * side + (x + delta) % side
                torus_moves += 1

    # Two lanes and two rows give four independent payload bits.
    book = []
    for p, first, last in product(range(2), repeat=3):
        label = held if first == last else move[first]
        path = mgg_segment(4, 2, 2 * p + first + 4 * label)
        assert path == (2 * p + first, 2 * p + last)
        book.append(path)
    layout = RowQueryLayout(2, 4, 4, segment_codebook=book, batch_size=2, half_tag=True)
    opposite = 0
    for x in range(16):
        rows = [sum(1 << (2 * p + ((x >> (2 * i + p)) & 1)) for p in range(2))
                for i in range(2)]
        identity_row = 0
        order = Random(901 + x).sample(range(layout.packet_count), layout.packet_count)
        for y in range(16):
            seeds = [4 * p + 2 * ((y >> p) & 1) + ((y >> (2 + p)) & 1)
                     for p in range(2)]
            files = [layout.render(rows, seeds, order, half=h) for h in (0, 1)]
            assert sum((a ^ b).bit_count() for a, b in zip(*files)) == 1
            verdicts = []
            for h, data in enumerate(files):
                clauses = parse_proper_dimacs(data)
                assert dict(physical_packet_fields(layout, data))[layout.half_slot] == h
                any_miss = False
                for p in range(2):
                    v = layout.batch_selectors[0]
                    pin = (v if p else -v, 1, 2)
                    for i in range(2):
                        for c in range(4):
                            works = evaluate(clauses + (pin,), layout, i, c) is not None
                            expect = i == h and c == book[seeds[p]][i] and not (rows[i] >> c & 1)
                            assert works == expect
                            any_miss |= works
                verdicts.append(any_miss)
            opposite += verdicts[0] != verdicts[1]
            if not any(verdicts):
                identity_row |= 1 << y
        assert identity_row == 1 << x
    assert opposite == 96
    return torus_moves, opposite


def check_wildcards():
    # One 2-by-2 square. Corners 0 and 1 test a bit; corner 2 ignores it.
    def square_label(start, end):
        labels = []
        for bit, plus, minus in ((0, (2, 1), (0, 3)), (1, (6, 5), (4, 7))):
            target = end >> bit & 1
            if target != (start >> bit & 1):
                labels.extend(plus if target else minus)
        return pack(labels + [8] * (160 - len(labels)), 4)

    book = []
    for first, last in product(range(3), repeat=2):
        raw = first + 4 * square_label(first, last)
        path = mgg_segment(4, 2, raw)
        assert path == (first, last)
        book.append(path)
    layout = RowQueryLayout(2, 4, 4, segment_codebook=book)
    count = 0
    for x in product(range(2), repeat=2):
        rows = [4 | (1 << bit) for bit in x]
        for j, pattern in enumerate(book):
            clauses = parse_proper_dimacs(layout.render(rows, [j]))
            witnesses = [(i, c) for i in range(2) for c in range(4)
                         if evaluate(clauses, layout, i, c) is not None]
            assert witnesses == [(i, c) for i, c in enumerate(pattern) if c < 2 and c != x[i]]
            count += 1
    return count


def check_block_pairs():
    book = [(2 * p + a, 2 * p + b) for p, a, b in product(range(2), repeat=3)]
    layout = RowQueryLayout(4, 4, 4, segment_codebook=book, batch_size=2, row_blocks=4)
    order = Random(711).sample(range(layout.packet_count), layout.packet_count)
    tag_index = order.index(layout.half_slot)
    tag_start = len(layout.public) + tag_index * layout.word_bytes
    rows = [5, 6, 9, 10]
    payload = [[int(not (rows[i] >> (2 * p) & 1)) for i in range(4)] for p in range(2)]
    opposite = tested = 0
    for miss_mask in range(16):
        # Every subset of bad blocks occurs; the responsible query alternates.
        target = [[payload[p][i] ^ int((miss_mask >> i & 1) and i % 2 == p)
                   for i in range(4)] for p in range(2)]
        seeds = [4 * p + 2 * target[p][i] + target[p][i + 1]
                 for p in range(2) for i in (0, 2)]
        common = None
        for u, v in product(range(4), repeat=2):
            files = [layout.render(rows, seeds, order, half=h, blocks=(u, v)) for h in (0, 1)]
            diffs = [i for i, (a, b) in enumerate(zip(*files)) if a != b]
            assert len(diffs) == 1 and tag_start <= diffs[0] < tag_start + layout.word_bytes
            assert files[0][diffs[0]] ^ files[1][diffs[0]] == 1
            verdicts = []
            for h, raw in enumerate(files):
                clauses = parse_proper_dimacs(raw)
                unchanged = tuple(raw[len(layout.public) + i*layout.word_bytes:
                                      len(layout.public) + (i+1)*layout.word_bytes]
                                  for i, logical in enumerate(order)
                                  if logical < layout.block_slots.start)
                if common is None:
                    common = unchanged
                assert unchanged == common
                chosen = (u, v)[h]
                any_miss = False
                for p in range(2):
                    bit = layout.batch_selectors[0]
                    pin = (bit if p else -bit, 1, 2)
                    for i, c in product(range(4), repeat=2):
                        works = evaluate(clauses + (pin,), layout, i, c) is not None
                        want = i == chosen and c == 2*p + target[p][i] and not (rows[i] >> c & 1)
                        assert works == want
                        any_miss |= works
                assert any_miss == bool(miss_mask >> chosen & 1)
                verdicts.append(any_miss)
                tested += 1
            opposite += verdicts[0] != verdicts[1]
    assert opposite == 96
    return tested, opposite


if __name__ == "__main__":
    basis = check_transpose()
    files, assignments = check_formulas()
    movements, opposite = check_pair_rank()
    wildcards = check_wildcards()
    pair_files, pair_opposite = check_block_pairs()
    print(f"{basis} transpose basis bits; {files} proper shared-data DIMACS files; "
          f"{assignments} query/row/column selector assignments; all verdicts agree.")
    print(f"{movements} powered translations; 512 two-tag files on two pairs of columns; "
          f"16-by-16 identity; 256 one-bit changes, {opposite} opposite verdicts; "
          f"{wildcards} physical wildcard queries.")
    print(f"{pair_files} fully queried four-block files; all ordered block pairs and "
          f"all bad-block masks; {pair_opposite} opposite one-bit pairs.")
