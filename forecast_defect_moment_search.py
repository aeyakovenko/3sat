"""Find a valid endpoint schedule from a positive first defect moment.

For schedule s let E(s) indicate the requested endpoint and d(s) count
failed local checks. A positive sum of E(s)*(1-d(s)) guarantees a leaf
with E=1 and d=0. The integer DP counts complete words, not distinct row
tuples; collisions add their path multiplicities. At a timestamp column
all the defect factors see the same symbol and all factors, including E,
see the same schedule letter. The endpoint sees its own fixed timestamp.

If the factor rows have W bits in total, h layers, L schedule letters, and
A timestamp symbols, each product count uses at most 2^W row tuples per
layer and L*A outgoing pairs per tuple. Counters have O(h log(2LA)) bits.
Recomputation for a concrete schedule takes at most 1+hL such counts per
test. Matrix generation, row operations and integer arithmetic must also
be charged. For an affine dependence of the next factor rows on l fresh
matrix entries, group letters by their row images instead. There are
at most 2^W images, each with a known multiplicity; a schedule can be
fixed one entry at a time in at most 1+hl prefix trials. This avoids
expanding the full 2^l-letter alphabet when l is quadratic in the width.

The small binary calibration uses z(t)=z(t-1)*z(t-2) with z(-1)=1 and
all earlier bits zero. All actual nonnegative bits are zero. It checks
the search on nontrivial scheduled predictions and exact bit subtraction.
It is independent of the choice of any SAT solver or forecast header.
"""

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Factor:
    """Binary linear prediction at time t-shift, optionally complemented."""

    mode: str
    shift: int
    complement: bool

    # Each of the two borrow states has six feature bits: constant, gate,
    # equality to the schedule, selected low bit, prediction, all digits one.
    initial = 1 | (1 << 5)
    width = 12

    def step(self, layer, letter, digit, row):
        result = 0
        for borrow in (0, 1):
            features = (row >> (6 * borrow)) & 63
            if not features:
                continue
            diff = digit - ((self.shift >> layer) & 1) - borrow
            bit = diff % 2
            unit, gate, equal, low, _, ones = (
                (features >> i) & 1 for i in range(6))
            if layer == 0:
                gate = unit if self.mode == "one" else unit * (1 - letter)
                equal = gate
                low = gate * (1 - bit if self.mode == "dense" else bit)
            target = int(layer == 0) if self.mode == "one" else letter
            equal *= int(bit == target)
            if self.mode == "one":
                prediction = equal
            elif self.mode == "dense":
                prediction = low
            else:
                prediction = low if letter else equal
            ones *= bit
            updated = unit | (gate << 1) | (equal << 2) | (low << 3)
            updated |= (prediction << 4) | (ones << 5)
            result ^= updated << (6 * int(diff < 0))
        return result

    def output(self, row):
        # At underflow the subtracted result represents -1 exactly when
        # every computed digit was one, the single nonzero negative seed.
        terminal = (1 << 4) | (1 << 11)
        if self.complement:
            terminal |= 1 | (1 << 6)
        return (terminal & row).bit_count() % 2


def affine_images(effect, widths, raw_bits, mask, value):
    """Count preimages under an affine tuple map on the permitted input cube."""
    def packed(letter):
        value = 0
        for part, width in zip(effect(letter), widths):
            value = (value << width) | part
        return value

    def unpack(value):
        result = []
        for width in reversed(widths):
            result.append(value & ((1 << width) - 1))
            value >>= width
        return tuple(reversed(result))

    base = packed(value)
    pivots = {}
    for bit in range(raw_bits):
        if mask >> bit & 1:
            continue
        delta = packed(value ^ (1 << bit)) ^ base
        while delta:
            pivot = delta.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = delta
                break
            delta ^= pivots[pivot]
    images = [base]
    for vector in pivots.values():
        images += [target ^ vector for target in images]
    mass = 1 << (raw_bits - mask.bit_count() - len(pivots))
    for target in images:
        yield unpack(target), mass


def count_product(h, prefix, letters, symbols, endpoint_digits, endpoint, factors,
                  *, raw_bits=None, restrictions=None):
    """Count (schedule,timestamp) for which every specified bit is one.
    With no defect factors, count endpoint schedules once each."""
    rows = (endpoint,) + factors
    widths = tuple(f.width for f in rows)
    counts = {tuple(f.initial for f in rows): 1}
    for layer in range(h):
        next_counts = {}
        choices = (prefix[layer],) if layer < len(prefix) else letters
        mask, value = (0, 0) if restrictions is None else restrictions[layer]
        if raw_bits is not None and layer < len(prefix):
            mask, value = (1 << raw_bits) - 1, prefix[layer]
        for state, multiplicity in counts.items():
            for digit in symbols if factors else (0,):
                def effect(letter):
                    end = endpoint.step(layer, letter, endpoint_digits[layer], state[0])
                    other = tuple(f.step(layer, letter, digit, r)
                                  for f, r in zip(factors, state[1:]))
                    return (end,) + other

                if raw_bits is None:
                    updates = ((effect(letter), 1) for letter in choices if letter & mask == value)
                else:
                    updates = affine_images(effect, widths, raw_bits, mask, value)
                for new, weight in updates:
                    if 0 in new:
                        continue
                    next_counts[new] = next_counts.get(new, 0) + multiplicity * weight
        counts = next_counts
    return sum(n for state, n in counts.items()
               if all(f.output(r) for f, r in zip(rows, state)))


def moments(h, prefix, mode):
    def f(shift=0, complement=False):
        return Factor(mode, shift, complement)

    # Mutually exclusive mismatches of y(t) against y(t-1) AND y(t-2).
    tests = ((f(0, True), f(1), f(2)), (f(), f(1, True)),
             (f(), f(1), f(2, True)))
    args = h, prefix, (0, 1), (0, 1), (1,) * h, f(0, True)
    endpoints = count_product(*args, ())
    defects_at_endpoints = sum(count_product(*args, test) for test in tests)
    return endpoints, defects_at_endpoints


def find_schedule(h, mode):
    def potential(prefix):
        hits, defects = moments(h, prefix, mode)
        return hits - defects

    prefix = ()
    if potential(prefix) <= 0:
        return None
    while len(prefix) < h:
        # The two child sums add to the strictly positive parent sum.
        prefix = next(child for bit in (0, 1)
                      if potential(child := prefix + (bit,)) > 0)
    return prefix


def direct_history(h, choices, mode):
    value = sum(bit << i for i, bit in enumerate(choices))
    bits = []
    for t in range(1 << h):
        if mode == "one":
            y = int(t == 1)
        elif mode == "dense":
            y = (1 - choices[0]) * int(t % 2 == 0)
        else:
            y = (1 - choices[0]) * (t % 2 if choices[-1] else int(t == value))
        bits.append(y)
    seeded = [0, 1] + bits
    defects = sum(bit != (seeded[i] & seeded[i + 1]) for i, bit in enumerate(bits))
    return bits, 1 - bits[-1], defects


def check_fixture(h, mode):
    histories = {}
    for s in product(range(2), repeat=h):
        bits, endpoint, defects = direct_history(h, s, mode)
        histories[s] = endpoint, defects
        for shift in (0, 1, 2):
            factor = Factor(mode, shift, False)
            for t in range(1 << h):
                row = factor.initial
                for i in range(h):
                    row = factor.step(i, s[i], (t >> i) & 1, row)
                earlier = t - shift
                expected = int(earlier == -1) if earlier < 0 else bits[earlier]
                assert factor.output(row) == expected

    for length in range(h + 1):
        for prefix in product(range(2), repeat=length):
            matching = [v for s, v in histories.items() if s[:length] == prefix]
            expected = sum(e for e, d in matching), sum(e * d for e, d in matching)
            assert moments(h, prefix, mode) == expected
    found = find_schedule(h, mode)
    hits, failures = moments(h, (), mode)
    good = sum(e == 1 and d == 0 for e, d in histories.values())
    if mode == "correlated":
        assert good == (1 << (h - 1)) and hits > failures
        assert sum(d for e, d in histories.values()) > len(histories)
        assert histories[found] == (1, 0)
    elif mode == "dense":
        assert good == (1 << (h - 1)) and hits < failures and found is None
    else:
        assert hits == failures and good == 0 and found is None
    print(f"h={h}, {mode}: endpoint schedules={hits}, endpoint defects={failures}, "
          f"valid schedules={good}, recovered={found}")


@dataclass(frozen=True)
class RawMatrixFactor:
    """Two factors may read different rows of the very same raw matrix."""

    initial: int
    terminal: int
    width = 3

    def step(self, layer, letter, digit, row):
        # Both digit-dependent permutations are linear in the incoming row.
        if digit:
            row = ((row << 1) & 7) | (row >> 2)
        result = 0
        for i in range(3):
            if row >> i & 1:
                result ^= (letter >> (3 * i)) & 7
        return result ^ (row if layer == 0 else 0)

    def output(self, row):
        return (row & self.terminal).bit_count() % 2


def check_matrix_alphabet():
    endpoint = RawMatrixFactor(1, 5)
    defects = (RawMatrixFactor(2, 3), RawMatrixFactor(1, 5))
    args = 2, (), range(512), (0, 1), (1, 0), endpoint, defects
    tests = (((0, 0), (0, 0)), ((0b101, 0b100), (0b110000, 0b010000)),
             ((511, 73), (511, 322)))
    for restrictions in tests:
        direct = count_product(*args, restrictions=restrictions)
        grouped = count_product(*args, restrictions=restrictions, raw_bits=9)
        assert direct == grouped
    print("full 3x3 matrix alphabet: all 512 letters agree with affine image counting "
          "under three entry restrictions")


def gf8_mul(a, b):
    """Carryless multiplication modulo the irreducible X^3 + X + 1."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 0b1011
    return result


def dense_fingerprint_count(h, prefix):
    """Count accepting (schedule, field point) pairs with a given schedule prefix.

    In the dense fixture an active prediction has defects at every even
    time and at time one. The two predicates are disjoint. A two-entry
    field row accumulates their timestamp monomial weights. After the
    low digit, only zero digits can extend the exact time-one monomial.
    Every schedule hits the endpoint.
    """
    counts = {(1, 0): 1}
    for layer in range(h):
        letters = prefix[layer:layer + 1] if layer < len(prefix) else (0, 1)
        next_counts = {}
        for (even, one), multiplicity in counts.items():
            for letter in letters:
                for x in range(8):
                    if layer == 0:
                        active = 1 - letter
                        state = (active, x if active else 0)
                    else:
                        state = (gf8_mul(even, 1 ^ x), one)
                    next_counts[state] = next_counts.get(state, 0) + multiplicity
        counts = next_counts
    return sum(count for (even, one), count in counts.items() if even == one)


def check_density_fingerprint():
    h = 3
    q = 8
    points_per_schedule = q ** h
    scores = {}
    for schedule in product((0, 1), repeat=h):
        bits, endpoint, _ = direct_history(h, schedule, "dense")
        seeded = [0, 1] + bits
        defects = [t for t, bit in enumerate(bits)
                   if bit != (seeded[t] & seeded[t + 1])]
        passes = 0
        for point in product(range(q), repeat=h):
            value = 0
            for t in defects:
                monomial = 1
                for j, x in enumerate(point):
                    if (t >> j) & 1:
                        monomial = gf8_mul(monomial, x)
                value ^= monomial
            passes += endpoint == 1 and value == 0
        scores[schedule] = passes
        # The active fingerprint is X_0 + product_{j>=1}(1 + X_j).
        # For each choice of its higher coordinates exactly one X_0 passes.
        assert passes == (q ** (h - 1) if schedule[0] == 0 else points_per_schedule)

    for length in range(h + 1):
        for prefix in product((0, 1), repeat=length):
            expected = sum(n for s, n in scores.items() if s[:length] == prefix)
            assert dense_fingerprint_count(h, prefix) == expected
    assert moments(h, (), "dense") == (8, 20) and find_schedule(h, "dense") is None
    assert dense_fingerprint_count(h, ()) == 2304
    assert [dense_fingerprint_count(h, (b,)) for b in (0, 1)] == [256, 2048]

    prefix = ()
    while len(prefix) < h:
        # The two children have equally many remaining schedule completions.
        parent_count = dense_fingerprint_count(h, prefix)
        prefix = max((prefix + (b,) for b in (0, 1)),
                     key=lambda s: dense_fingerprint_count(h, s))
        assert 2 * dense_fingerprint_count(h, prefix) >= parent_count
    _, endpoint, defects = direct_history(h, prefix, "dense")
    assert (endpoint, defects) == (1, 0) and prefix == (1, 0, 0)
    print(f"h=3, dense GF(8) fingerprint: 2304/4096 pairs pass; first-bit counts "
          f"256/2048 and 2048/2048; recovered={prefix} with no defects")


def main():
    for h in (3, 4):
        for mode in ("correlated", "dense", "one"):
            check_fixture(h, mode)
    check_matrix_alphabet()
    check_density_fingerprint()


if __name__ == "__main__":
    main()
