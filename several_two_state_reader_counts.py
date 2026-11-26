"""Count shared Boolean witnesses for fixed oblivious two-state readers.

Run the finite audit with: python several_two_state_reader_counts.py
Only the Python standard library is required. A row is (zero-based name,
four-bit table), with output in bit 2*input_bit + previous_state.
"""

from itertools import product
from random import Random


class Factors:
    """Feasible parities at each name's two possible values; None forbids it."""

    def __init__(self, variables, states):
        self.pairs = [(0, 0)] * variables
        self.free = variables
        self.missing = 0
        self.base = 0
        self.deltas = [0] * states
        self.deltas[0] = variables

    def replace(self, name, pair):
        for (a, b), change in ((self.pairs[name], -1), (pair, 1)):
            if a is None and b is None:
                self.missing += change
                continue
            self.base ^= a if a is not None else b
            if a is not None and b is not None:
                self.free += change
                self.deltas[a ^ b] += change
        self.pairs[name] = pair

    def record(self, offset, histograms):
        span = {0}
        for delta, count in enumerate(self.deltas):
            if count and delta not in span:
                span.update({value ^ delta for value in span})
        rank = len(span).bit_length() - 1
        for value in span:
            histograms[self.base ^ offset ^ value][self.free - rank] += 1


def pack_count(histogram):
    """Carry the small coefficients before constructing a single Python integer."""
    packed = bytearray((len(histogram) + 7) // 8)
    carry = 0
    for bit, coefficient in enumerate(histogram):
        carry += coefficient
        packed[bit // 8] |= (carry & 1) << (bit % 8)
        carry >>= 1
    assert carry == 0
    return int.from_bytes(packed, "little")


def count_final_states(variables, readers, starts):
    """Result[t] counts assignments whose reader j ends in bit j of t."""
    if variables < 0 or len(starts) != len(readers) or any(b not in (0, 1) for b in starts):
        raise ValueError("invalid number of variables or initial states")
    for rows in readers:
        if any(not (0 <= name < variables and 0 <= table < 16) for name, table in rows):
            raise ValueError("row needs a declared name and a four-bit transition")
    states = 1 << len(readers)
    factors = Factors(variables, states)
    histograms = [[0] * (variables + 1) for _ in range(states)]

    def visit(j, offset):
        if factors.missing:
            return
        if j == len(readers):
            factors.record(offset, histograms)
            return

        undo = []
        for name, table in reversed(readers[j]):
            old = factors.pairs[name]
            undo.append((name, old))
            resets = [None, None]
            permutations = [None, None]
            for bit, parity in enumerate(old):
                if parity is None:
                    continue
                lo = (table >> (2 * bit)) & 1
                hi = (table >> (2 * bit + 1)) & 1
                destinations = resets if lo == hi else permutations
                destinations[bit] = parity ^ (lo << j)
            if any(value is not None for value in resets):
                factors.replace(name, tuple(resets))
                visit(j + 1, offset)
            factors.replace(name, tuple(permutations))
            if factors.missing:
                break
        visit(j + 1, offset ^ (starts[j] << j))  # No reset in this reader.
        for name, old in reversed(undo):
            factors.replace(name, old)

    visit(0, 0)
    return tuple(pack_count(histogram) for histogram in histograms)


def brute(variables, readers, starts):
    counts = [0] * (1 << len(readers))
    for witness in range(1 << variables):
        final = 0
        for j, rows in enumerate(readers):
            state = starts[j]
            for name, table in rows:
                bit = (witness >> name) & 1
                state = (table >> (2 * bit + state)) & 1
            final |= state << j
        counts[final] += 1
    return tuple(counts)


def audit():
    trials = 0
    schedules = [()] + [((name, table),) for name in range(2) for table in range(16)]
    for readers in product(schedules, repeat=2):
        for starts in product(range(2), repeat=2):
            assert count_final_states(2, readers, starts) == brute(2, readers, starts)
            trials += 1
    print(f"{trials} exhaustive pairs of empty or single-row readers and initial states")

    # All named-position coincidences up to relabeling in the three one-row case.
    triples = 0
    for names in ((0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2)):
        for tables in product(range(16), repeat=3):
            readers = [((name, table),) for name, table in zip(names, tables)]
            starts = (1, 0, 1)
            assert count_final_states(3, readers, starts) == brute(3, readers, starts)
            triples += 1
    print(f"{triples} exhaustive triples of single-row tables across five name patterns")

    rng = Random(261126)
    for _ in range(900):
        v = rng.randrange(1, 8)
        r = rng.randrange(6)
        readers = [[(rng.randrange(v), rng.randrange(16)) for _ in range(rng.randrange(9))]
                   for _ in range(r)]
        starts = [rng.randrange(2) for _ in range(r)]
        assert count_final_states(v, readers, starts) == brute(v, readers, starts)

    # 0b0110 maps a state to itself on bit 0 and flips it on bit 1.
    readers = [[(i, 6) for i in group] for group in ((0, 1), (2, 1), (0, 2))]
    expected = tuple(0 if z.bit_count() % 2 else 1 << 998 for z in range(8))
    assert count_final_states(1000, readers, (0, 0, 0)) == expected
    assert count_final_states(0, [], ()) == (1,)
    assert count_final_states(0, [(), ()], (1, 0)) == (0, 1, 0, 0)
    print("900 repeated-name trials, rank-two shared parities on 1000 bits, and zero-bit cases")


if __name__ == "__main__":
    audit()
