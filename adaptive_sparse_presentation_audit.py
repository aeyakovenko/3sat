"""Finite checks for compact verification of a sparse presentation. Run with python3 -B adaptive_sparse_presentation_audit.py."""

from bisect import bisect_right
import ctypes
from ctypes.util import find_library
from itertools import combinations, permutations, product
from random import Random

from table_probe_context_audit import parse, satisfiable
from free_presentation_audit import trace_checks


def check_hash_bound():
    pairs = tight = 0
    for width in range(2, 8):
        size = 1 << width
        odds = range(1, size, 2)
        for bank_bits in range(1, width + 1):
            banks = 1 << bank_bits
            rows = [[(a * x % size) >> (width - bank_bits) for a in odds]
                    for x in range(size)]
            for first, second in combinations(rows, 2):
                collisions = sum(x == y for x, y in zip(first, second))
                assert collisions * banks <= 2 * len(odds)
                tight += collisions * banks == 2 * len(odds)
                pairs += 1
    print(f"Multiply-shift: {pairs} pair/width/bank tests, {tight} at 2/B.")


class SparsePad:
    """Zero-based ordinals, public universe and weight, no directory at offset zero."""
    def __init__(self, universe, keys):
        self.count = len(keys)
        self.low_width = (universe // self.count).bit_length() - 1 if keys else 0
        scale = 1 << self.low_width
        self.low = [key % scale for key in keys]
        self.high = [0] * (self.count + (universe + scale - 1) // scale) if keys else []
        for i, key in enumerate(keys):
            self.high[i + key // scale] = 1
        width = universe.bit_length()
        self.stride = width * width
        self.directory = []
        prefix = 0
        for position, bit in enumerate(self.high):
            if position and position % self.stride == 0:
                self.directory.append(prefix)
            prefix += bit
        self.bits = self.count * self.low_width + len(self.high) + width * len(self.directory)
        assert len(self.high) <= 3 * self.count
        assert width * len(self.directory) <= 3 * self.count // width

    def key(self, i):
        block = bisect_right(self.directory, i)
        rank = self.directory[block - 1] if block else 0
        start = block * self.stride
        for position in range(start, min(start + self.stride, len(self.high))):
            if self.high[position]:
                if rank == i:
                    return ((position - i) << self.low_width) | self.low[i]
                rank += 1
        raise AssertionError("Missing select reply")


def check_sparse():
    pads = queries = indexed = 0
    rng = Random(3817)
    for size in (*range(1, 14), 1024, 4096):
        samples = (range(1 << size) if size < 14 else
                   (rng.getrandbits(size) & rng.getrandbits(size) for _ in range(32)))
        for mask in samples:
            keys = [i for i in range(size) if mask >> i & 1]
            encoded = SparsePad(size, keys)
            assert [encoded.key(i) for i in range(len(keys))] == keys
            queries += len(keys)
            pads += 1
            indexed += bool(encoded.directory)
    print(f"Sparse support: {pads} pads, {queries} select replies, {indexed} with nonempty directory.")
    sample = SparsePad(65536, list(range(0, 65536, 16)))
    assert sample.bits == 25052
    print("Universe 65536, weight 4096: 25052 bits with the directory, dimensions given.")


# Data locations for (positive unit, negative unit) on each of eight variables.
# The layout is a reindexing of the selector bits, with the same model predicate.
PAIRS = [(14, 11), (6, 4), (15, 10), (3, 1), (0, 13), (5, 8), (7, 12), (2, 9)]


def bank_position(a, x):
    return divmod(a * x % 16, 4)


def split_mask(a):
    return sum(int(bank_position(a, x)[0] != bank_position(a, y)[0]) << i
               for i, (x, y) in enumerate(PAIRS))


def masks(table):
    return tuple(sum(((table >> pair[j]) & 1) << i for i, pair in enumerate(PAIRS))
                 for j in range(2))


def check_catalog():
    splits = [split_mask(a) for a in range(1, 16, 2)]
    assert max(splits) < 255 and splits[0] | splits[1] == 255
    positives = unsafe = lost = 0
    for table in range(1 << 16):
        pos, neg = masks(table)
        # A common challenge is blocked if both layouts collide on its second
        # read, or the two authentic unit bits really conflict.
        blocked = [(pos & (~mask | neg)) & 255 for mask in splits]
        good = neg != 255 and not (blocked[0] & blocked[1])
        expected = neg != 255 and pos & neg == 0
        assert good == expected
        positives += expected
        lost += expected and all(blocked)
        # Unsound alternative: in layout 1 discard challenges whose reads collide.
        unsafe += not expected and neg != 255 and not (pos & neg & splits[0])
    assert positives == 6560 and lost > 0 and unsafe > 0
    print(f"16-bit files: {positives}/65536 positive, {lost} positives fail every single layout; "
          f"skipping collisions in layout 1 accepts {unsafe} negatives.")


class Formula:
    def __init__(self):
        self.last = 3
        self.rows = [tuple(-i if bit else i for i, bit in enumerate(setting, 1))
                     for setting in product(range(2), repeat=3) if any(setting)]

    def new(self):
        self.last += 1
        return self.last

    def clause(self, *literals):
        used = {abs(x) for x in literals}
        assert len(used) == len(literals) <= 3 and not used.intersection((1, 2, 3))
        self.rows.append(tuple(literals) + (1, 2, 3)[:3 - len(literals)])

    def any_of(self, flags):
        value = flags[0]
        for flag in flags[1:]:
            output = self.new()
            self.clause(-value, output)
            self.clause(-flag, output)
            self.clause(value, flag, -output)
            value = output
        self.clause(value)

    def bank(self, data):
        high, low, reply = (self.new() for _ in range(3))
        library = []
        for mask in range(4):
            matches = self.new()
            library.append(matches)
            for lane in range(2):
                inactive = low if lane == 0 else -low
                bit_agrees = reply if mask >> lane & 1 else -reply
                self.clause(inactive, -matches, bit_agrees)
                self.clause(inactive, matches, -bit_agrees)
        for group in range(2):
            mask = data[2 * group] + 2 * data[2 * group + 1]
            self.clause(high if group == 0 else -high, library[mask])
        return high, low, reply

    def bytes(self):
        return (f"p cnf {self.last} {len(self.rows)}\n" +
                "".join(" ".join(map(str, row)) + " 0\n" for row in self.rows)).encode()


def defect_file(table, layouts, missing):
    """A defect is a unit conflict or a failed witness that negative unit 'missing' is absent."""
    form = Formula()
    selected = [form.new() for _ in range(9)]
    form.any_of(selected)
    for a in layouts:
        permuted = [0] * 16
        for index in range(16):
            permuted[a * index % 16] = (table >> index) & 1
        banks = [form.bank(permuted[i:i + 4]) for i in range(0, 16, 4)]

        def require_one(challenge, index):
            bank, slot = bank_position(a, index)
            high, low, reply = banks[bank]
            for literal in (high if slot & 2 else -high, low if slot & 1 else -low, reply):
                form.clause(-selected[challenge], literal)

        for i, (positive, negative) in enumerate(PAIRS):
            require_one(i, positive)
            if bank_position(a, positive)[0] != bank_position(a, negative)[0]:
                require_one(i, negative)
        require_one(8, PAIRS[missing][1])
    return form.bytes()


def solver():
    """Use libz3 when present, otherwise use the journal's generic DPLL."""
    path = find_library("z3")
    if not path:
        return lambda clauses, count: satisfiable(clauses)
    lib = ctypes.CDLL(path)
    ptr = ctypes.c_void_p
    lib.Z3_mk_config.restype = ptr
    lib.Z3_mk_context.argtypes = [ptr]
    lib.Z3_mk_context.restype = ptr
    lib.Z3_del_config.argtypes = [ptr]
    lib.Z3_del_context.argtypes = [ptr]
    lib.Z3_eval_smtlib2_string.argtypes = [ptr, ctypes.c_char_p]
    lib.Z3_eval_smtlib2_string.restype = ctypes.c_char_p

    def solve(clauses, count):
        config = lib.Z3_mk_config()
        ctx = lib.Z3_mk_context(config)
        lib.Z3_del_config(config)
        try:
            lines = [f"(declare-const x{i} Bool)" for i in range(1, count + 1)]
            for clause in clauses:
                terms = [f"x{x}" if x > 0 else f"(not x{-x})" for x in clause]
                lines.append("(assert (or " + " ".join(terms) + "))")
            lines.append("(check-sat)")
            result = lib.Z3_eval_smtlib2_string(ctx, "\n".join(lines).encode()).strip()
            assert result in (b"sat", b"unsat"), result
            return result == b"sat"
        finally:
            lib.Z3_del_context(ctx)
    return solve


def check_files():
    rng = Random(4883)
    solve = solver()
    cases = defects = 0
    for layouts in ((1,), (3,), (1, 3)):
        for trial in range(64):
            table = rng.getrandbits(16)
            if trial % 2 == 0:
                for p, n in PAIRS:
                    if table >> p & 1:
                        table &= ~(1 << n)
            pos, neg = masks(table)
            missing = rng.randrange(8)
            bad = bool(neg >> missing & 1)
            for i in range(8):
                stops = [bool((pos >> i & 1) and ((neg >> i & 1) or not (split_mask(a) >> i & 1)))
                         for a in layouts]
                bad |= all(stops)
            raw = defect_file(table, layouts, missing)
            assert solve(*parse(raw)) == bad
            defects += bad
            cases += 1
    print(f"Physical adaptive defect tests: {cases} parsed proper DIMACS files, {defects} satisfiable.")


def guarded_file(checks):
    pin_rows = [" ".join(str(-j if bit else j) for j, bit in enumerate(setting, 1)) + " 0\n"
                for setting in product(range(2), repeat=3) if any(setting)]
    assert sum(map(len, pin_rows)) == 68
    rows = pin_rows + ["-1 2 3 0\n" if ok else " 1 2 3 0\n" for ok in checks]
    raw = (f"p cnf 3 {len(rows)}\n" + "".join(rows)).encode()
    assert 8 * len(raw) == 8 * (77 + len(str(len(rows))) + 9 * len(checks))
    return raw


def check_rare():
    cases = 0
    for blocks, stride in ((1, 3), (2, 4), (4, 3)):
        hits = []
        for pad in range(1 << (blocks * stride)):
            fields = [(pad >> (i * stride)) % (1 << stride) for i in range(blocks)]
            raw = guarded_file([f == 1 for f in fields])
            if satisfiable(parse(raw)[0]):
                hits.append(pad)
            cases += 1
        assert hits == [sum(1 << (i * stride) for i in range(blocks))]
    print(f"Rare presentations: {cases} physical files, one good pad per size, zero replay fails.")


def check_grouped_traces():
    cases = accepted = 0
    for first, second, address, reply in product(range(2), repeat=4):
        chronological = [(0, 0, 0, first), (1, 1, 0, second), (address, 2, reply, reply)]
        for order, inverse in product(permutations(range(3)), repeat=2):
            records = [chronological[i] for i in order]
            checks = trace_checks(chronological, records, order, inverse, reply)
            expected = (reply == (first, second)[address] == 1
                        and records == sorted(chronological)
                        and all(inverse[order[i]] == i for i in range(3)))
            for stride in (1, 4, len(checks)):
                raw = guarded_file([all(checks[j:j + stride])
                                    for j in range(0, len(checks), stride)])
                assert satisfiable(parse(raw)[0]) == expected
                cases += 1
                accepted += expected
    print(f"Grouped native trace tests: {cases} physical files, {accepted} positives.")


if __name__ == "__main__":
    check_hash_bound()
    check_sparse()
    check_catalog()
    check_files()
    check_rare()
    check_grouped_traces()
