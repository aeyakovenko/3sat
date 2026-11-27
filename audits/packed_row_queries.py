"""Word-aligned proper 3-CNF for a missing entry among k publicly indexed row queries."""

from itertools import product


def lower_power_of_two(n):
    return 1 << (n.bit_length() - 1)


def power_of_two(n):
    return n > 0 and n & (n - 1) == 0


MGG_STEPS = 160
MGG_LABEL_BITS = 4
MGG_TRANSITION_BITS = MGG_STEPS * MGG_LABEL_BITS


def mgg_column_bits(columns):
    """The column space is the square torus Z_m², with x in the low bits."""
    bits = columns.bit_length() - 1
    if columns < 4 or not power_of_two(columns) or bits % 2:
        raise ValueError("MGG columns must be a power of four at least four")
    return bits


def mgg_step(columns, vertex, label):
    """Eight directed shears in inverse pairs 0/1,...,6/7, and eight stays."""
    bits = mgg_column_bits(columns) // 2
    if not 0 <= vertex < columns or not 0 <= label < 16:
        raise ValueError("invalid MGG vertex or nibble")
    mask = (1 << bits) - 1
    x, y = vertex & mask, vertex >> bits
    if label < 4:
        step = 2 * y + (label >> 1)
        x = (x - step if label & 1 else x + step) & mask
    elif label < 8:
        step = 2 * x + ((label - 4) >> 1)
        y = (y - step if label & 1 else y + step) & mask
    return x | (y << bits)


def mgg_transition(columns, start, label):
    """Execute exactly 160 nibbles, least significant first, including leading zeros."""
    if label < 0 or label.bit_length() > MGG_TRANSITION_BITS:
        raise ValueError("expected a 640-bit powered-edge label")
    vertex = start
    for _ in range(MGG_STEPS):
        vertex = mgg_step(columns, vertex, label & 15)
        label >>= MGG_LABEL_BITS
    return vertex


def mgg_segment(columns, length, seed):
    """Decode a start vertex and length-1 independent 640-bit labels from one seed."""
    bits = mgg_column_bits(columns)
    if not power_of_two(length):
        raise ValueError("segment length must be a power of two")
    if seed < 0 or seed.bit_length() > bits + MGG_TRANSITION_BITS * (length - 1):
        raise ValueError("segment seed exceeds its declared width")
    path = [seed & (columns - 1)]
    seed >>= bits
    transition_mask = (1 << MGG_TRANSITION_BITS) - 1
    for _ in range(length - 1):
        path.append(mgg_transition(columns, path[-1], seed & transition_mask))
        seed >>= MGG_TRANSITION_BITS
    return tuple(path)


def mgg_codebook(columns, length, packet_bits):
    """Yield the exact table for segment_codebook, in packed seed order.

    There are 2^(log2(columns)+640*(length-1)) paths. Individual seeds can
    be decoded with mgg_segment without constructing the table.
    """
    bits = mgg_column_bits(columns)
    if (
        not power_of_two(length)
        or bits + MGG_TRANSITION_BITS * (length - 1) > packet_bits
    ):
        raise ValueError("segment seed must fit in the specified packet")
    return (
        mgg_segment(columns, length, seed)
        for seed in range(1 << (bits + MGG_TRANSITION_BITS * (length - 1)))
    )


def clause_bytes(a, b, c):
    return f"{a} {b} {c} 0\n".encode("ascii")


class RowQueryLayout:
    """Build one public layout. Row and column selector variables are little-endian."""

    def __init__(
        self,
        k,
        columns=None,
        packet_bits=None,
        queries_per_packet=None,
        *,
        segment_codebook=None,
        half_tag=False,
        word_coefficient=32,
        batch_size=1,
        row_blocks=None,
    ):
        if k < 2 or not power_of_two(k):
            raise ValueError("k must be a power of two at least two")
        if not power_of_two(batch_size):
            raise ValueError("batch size must be a positive power of two")
        if row_blocks is not None:
            if not power_of_two(row_blocks) or row_blocks > k:
                raise ValueError("row block count must be a power of two dividing k")
            half_tag = True
        row_bits = k.bit_length() - 1
        h = (
            packet_bits
            if packet_bits is not None
            else lower_power_of_two(max(2, row_bits // 8))
        )
        b = (
            columns
            if columns is not None
            else min(h, lower_power_of_two(max(2, row_bits // row_bits.bit_length())))
        )
        if not (
            power_of_two(h) and power_of_two(b) and 2 <= b <= h and (k * b) % h == 0
        ):
            raise ValueError(
                "B and h must be powers of two with 2 <= B <= h dividing kB"
            )
        column_bits = b.bit_length() - 1
        self.segment_codebook = None
        if segment_codebook is None:
            g = (
                queries_per_packet
                if queries_per_packet is not None
                else lower_power_of_two(min(k, h // column_bits))
            )
            if g * column_bits > h:
                raise ValueError("independent queries must fit in h bits")
        else:
            book = tuple(tuple(path) for path in segment_codebook)
            if not book or len(book) > 1 << h:
                raise ValueError("the seed table must have between 1 and 2^h paths")
            g = len(book[0])
            if queries_per_packet is not None and queries_per_packet != g:
                raise ValueError("segment length differs from queries_per_packet")
            if any(
                len(path) != g or any(not 0 <= x < b for x in path) for path in book
            ):
                raise ValueError(
                    "every path must have the same length and valid columns"
                )
            self.segment_codebook = book
        if not power_of_two(g) or g > k:
            raise ValueError("segment length must be a power of two dividing k")

        self.k = k
        self.columns = b
        self.packet_bits = h
        self.queries_per_packet = g
        self.data_count = k * b // h
        self.batch_size = batch_size
        self.query_count = batch_size * (k // g)
        self.row_blocks = row_blocks
        block_start = self.data_count + self.query_count
        self.block_slots = range(block_start, block_start + (2 if row_blocks is not None else 0))
        self.half_slot = self.block_slots.stop if half_tag else None
        self.packet_count = self.block_slots.stop + int(half_tag)
        self.half_names = None

        clauses = []
        variables = 4
        pad, zero, _ = 1, 2, 3
        one = 4
        for signs in product((1, -1), repeat=3):
            if signs != (1, 1, 1):
                clauses.append(tuple(s * v for s, v in zip(signs, (1, 2, 3))))
        clauses.append((one, pad, zero))

        def reserve(n):
            nonlocal variables
            first = variables + 1
            variables += n
            return range(first, variables + 1)

        def new():
            return reserve(1).start

        def equivalent(x, y):
            clauses.extend(((-x, y, pad), (x, -y, pad)))

        def mux(s, lo, hi):
            if lo == hi:
                return lo
            out = new()
            clauses.extend(
                ((s, -lo, out), (s, lo, -out), (-s, -hi, out), (-s, hi, -out))
            )
            return out

        def conjunction(a, b):
            v = new()
            clauses.extend(((-a, -b, v), (a, -v, pad), (b, -v, pad)))
            return v

        self.row_selectors = reserve(row_bits)
        self.column_selectors = reserve(column_bits)
        self.batch_selectors = reserve(batch_size.bit_length() - 1)
        address = list(self.column_selectors) + list(self.row_selectors)
        data_low = h.bit_length() - 1
        query_low = g.bit_length() - 1

        def choose(flags, selectors):
            values = list(flags)
            for s in selectors:
                values = [
                    mux(s, values[i], values[i + 1]) for i in range(0, len(values), 2)
                ]
            assert len(values) == 1
            return values[0]

        # For a lookup table, level p contains the functions on 2^p lanes
        # in numeric mask order. Equal lower and upper halves reuse a literal.
        def library(previous, bits_per_leaf, selectors):
            width = bits_per_leaf
            for s in selectors:
                size = 1 << width
                previous = [
                    mux(s, previous[mask % size], previous[mask // size])
                    for mask in range(size * size)
                ]
                width *= 2
            aliases = reserve(len(previous))
            for flag, value in zip(aliases, previous):
                equivalent(flag, value)
            return aliases

        self.data_names = library([zero, one], 1, address[:data_low])
        tests = [-self.column_selectors[0], self.column_selectors[0]]
        for s in self.column_selectors[1:]:
            tests = [conjunction(a, sign) for sign in (-s, s) for a in tests]
        low_row = self.row_selectors[:query_low]
        if self.segment_codebook is None:
            self.query_names = library(tests, column_bits, low_row)
        else:
            # Precompute the equality predicate once per seed, independent of
            # the number of segments. Each actual segment only names one gate.
            self.query_names = reserve(len(self.segment_codebook))
            for flag, path in zip(self.query_names, self.segment_codebook):
                equal = choose([tests[col] for col in path], low_row)
                equivalent(flag, equal)

        self.data_flags = reserve(self.data_count)
        self.query_flags = reserve(self.query_count)

        data = choose(self.data_flags, address[data_low:])
        query_address = list(self.row_selectors[query_low:]) + list(self.batch_selectors)
        match = choose(self.query_flags, query_address)
        tag_bit = self.row_selectors[-1]
        if row_blocks is not None:
            # Each public predicate tests a high row index. Give it a positive
            # dense name so the two packet values are independent of the tag.
            bits = row_blocks.bit_length() - 1
            block_tests = [one]
            if bits:
                selectors = self.row_selectors[-bits:]
                block_tests = [-selectors[0], selectors[0]]
                for selector in selectors[1:]:
                    block_tests = [conjunction(a, sign) for sign in (-selector, selector)
                                   for a in block_tests]
            self.block_names = reserve(row_blocks)
            for alias, test in zip(self.block_names, block_tests):
                equivalent(alias, test)
            self.block_flags = reserve(2)
            tag_bit = new()
            selected_block = mux(tag_bit, self.block_flags[0], self.block_flags[1])
            clauses.append((selected_block, pad, zero))
        if half_tag:
            # Every skipped ID is fixed. The two positive name spellings
            # differ only by the low ASCII bit of their final digit, 2/3.
            for filler in reserve((2 - (variables + 1)) % 10):
                clauses.append((-filler, pad, zero))
            self.half_names = reserve(2)
            equivalent(self.half_names[0], -tag_bit)
            equivalent(self.half_names[1], tag_bit)
        clauses.extend(((-data, pad, zero), (match, pad, zero)))
        self.variable_count = variables
        self.clause_count = len(clauses) + 2 * self.packet_count
        public = f"p cnf {variables} {self.clause_count}\n".encode("ascii")
        if batch_size > 1:
            public += f"c walk-batch {k} {b} {h} {g} {batch_size}\n".encode("ascii")
        if row_blocks is not None:
            public += f"c walk-blocks {k} {b} {h} {g} {batch_size} {row_blocks}\n".encode("ascii")
        public += b"".join(clause_bytes(*c) for c in clauses)
        digits = len(str(variables))
        # Exact word width: w = C * ceil(log2(N+2)) bits for the *final* N.
        # Only public whitespace is padded. In the production parameter range
        # the padding and the whole resulting file have the original asymptotic size.
        if word_coefficient < 32 or word_coefficient % 8:
            raise ValueError("word_coefficient must be a multiple of eight at least 32")
        self.word_coefficient = word_coefficient
        minimum_bytes = 6 * (digits + 1) + 12
        ell = max(1, (8 * len(public)).bit_length())
        while True:
            word = (word_coefficient // 8) * ell
            full_words = (len(public) + word - 1) // word + self.packet_count
            lower = 1 << (ell - 1)
            full_words = max(full_words, (lower - 2) // (8 * word) + 1)
            if word >= minimum_bytes and 8 * word * full_words + 2 <= 1 << ell:
                break
            ell += 1
        self.word_bytes = word
        self.public = public.ljust((full_words - self.packet_count) * word, b" ")

    def packet(self, number, value):
        if self.half_slot is not None and number == self.half_slot:
            if value not in (0, 1):
                raise ValueError("expected half 0 or 1")
            clauses = clause_bytes(self.half_names[value], 1, 2) + clause_bytes(4, 1, 2)
        else:
            if 0 <= number < self.data_count:
                names = self.data_names
                flag = self.data_flags[number]
            elif self.data_count <= number < self.data_count + self.query_count:
                names = self.query_names
                flag = self.query_flags[number - self.data_count]
            elif number in self.block_slots:
                names = self.block_names
                flag = self.block_flags[number - self.block_slots.start]
            else:
                raise ValueError("packet number out of range")
            if not 0 <= value < len(names):
                raise ValueError("packet value out of range")
            name = names[value]
            clauses = clause_bytes(-flag, name, 1) + clause_bytes(flag, -name, 1)
        return clauses.ljust(self.word_bytes - 1, b" ") + b"\n"

    def masks(self, rows, queries):
        """Pack shared rows and batch-major columns or segment seed IDs."""
        if len(rows) != self.k:
            raise ValueError("one data word required per bank")
        b, g = self.columns, self.queries_per_packet
        if any(not 0 <= x < (1 << b) for x in rows):
            raise ValueError("invalid B-bit row word")
        per_data = self.packet_bits // b
        masks = [
            sum(rows[i + j] << (b * j) for j in range(per_data))
            for i in range(0, self.k, per_data)
        ]
        if self.segment_codebook is not None:
            if len(queries) != self.query_count or any(
                not 0 <= seed < len(self.query_names) for seed in queries
            ):
                raise ValueError("expected one valid codebook seed per segment")
            return masks + list(queries)
        if len(queries) != self.k * self.batch_size or any(not 0 <= j < b for j in queries):
            raise ValueError("expected one valid query column per bank")
        ell = b.bit_length() - 1
        masks.extend(
            sum(queries[i + j] << (ell * j) for j in range(g))
            for i in range(0, len(queries), g)
        )
        return masks

    def render(self, rows, queries, slot_order=None, *, half=None, blocks=None):
        """slot_order gives the logical packet at each successive aligned physical slot."""
        values = self.masks(rows, queries)
        if self.row_blocks is not None:
            if blocks is None or len(blocks) != 2 or not all(0 <= i < self.row_blocks for i in blocks):
                raise ValueError("expected an ordered pair of row blocks")
            values.extend(blocks)
        elif blocks is not None:
            raise ValueError("select row_blocks to include block selectors")
        if self.half_slot is not None:
            if half not in (0, 1):
                raise ValueError("the half-tag layout requires half=0 or half=1")
            values.append(half)
        elif half is not None:
            raise ValueError("select half_tag=True to include a half tag")
        if slot_order is None:
            slot_order = range(self.packet_count)
        seen = bytearray(self.packet_count)
        chunks = [self.public]
        for j in slot_order:
            if not 0 <= j < self.packet_count or seen[j]:
                raise ValueError("expected a permutation of the packet slots")
            seen[j] = 1
            chunks.append(self.packet(j, values[j]))
        if not all(seen):
            raise ValueError("missing packet slot")
        return b"".join(chunks)
