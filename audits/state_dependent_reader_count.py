"""Count witnesses of a width-two layered Boolean reader.

A row (a,b) sets the next state to literal a from state 0 and to b from
state 1. Encode literal x_i XOR t by 2*i+t (1 <= i <= v), and constants
by 0 or 1. Rows can select different, arbitrarily repeated variable names.
The original reader executes every row. The counter returns an exact integer.
"""

from itertools import product
from random import Random


class ParitySystem:
    """Constraints X_i XOR X_j = d, together with one tracked affine phase.

    The physical input bit x_i is X_i XOR X_0. Complementing all X preserves
    every physical input, so there are two lifts of each physical assignment.
    A root indexes a free X-coordinate. offset[i] is X_i XOR X_root(i).
    The phase is the XOR of the roots flagged by coeff and the scalar phase.
    """

    def __init__(self, variables):
        vertices = variables + 1
        self.root = list(range(vertices))
        self.offset = [0] * vertices
        self.members = [[i] for i in range(vertices)]
        self.coeff = [0] * vertices
        self.active = 0
        self.phase = 0
        self.components = vertices

    def add_literal(self, literal):
        """XOR the physical literal into the current suffix phase."""
        self.phase ^= literal & 1
        for i in (literal >> 1, 0):
            root = self.root[i]
            self.phase ^= self.offset[i]
            self.active += 1 if self.coeff[root] == 0 else -1
            self.coeff[root] ^= 1

    @staticmethod
    def exponent(components, active, phase, target):
        """Return e for 2^e solutions in physical bits, or None for zero."""
        if not active and phase != target:
            return None
        # One dimension for the global complement gauge. If the phase has
        # a nonzero coefficient it removes one additional free dimension.
        return components - 1 - bool(active)

    def record(self, histogram, target):
        e = self.exponent(self.components, self.active, self.phase, target)
        if e is not None:
            histogram[e] += 1

    def split(self, a, b, target, histogram):
        """Record the reset branch A=B and permanently impose A!=B.

        Return False if the new all-permutation suffix is impossible.
        The reset branch uses only a temporary *logical* union, without
        relabeling any members. This avoids charging a large rollback at
        every row.
        """
        i, j = a >> 1, b >> 1
        left, right = self.root[i], self.root[j]
        difference = self.offset[i] ^ self.offset[j] ^ ((a ^ b) & 1)
        if left == right:
            if difference == 0:
                self.record(histogram, target)
                return False
            return True

        if len(self.members[left]) < len(self.members[right]):
            left, right = right, left

        # For A=B, X_right = X_left XOR difference, in either orientation.
        left_bit, right_bit = self.coeff[left], self.coeff[right]
        new_bit = left_bit ^ right_bit
        active = self.active - left_bit - right_bit + new_bit
        components = self.components - 1
        reset_phase = self.phase ^ (difference & right_bit)
        e = self.exponent(components, active, reset_phase, target)
        if e is not None:
            histogram[e] += 1

        # Switching to A!=B flips precisely the root-offset constraint.
        difference ^= 1
        self.phase ^= difference & right_bit
        self.coeff[left] = new_bit
        self.coeff[right] = 0
        self.active = active
        self.components = components
        for vertex in self.members[right]:
            self.root[vertex] = left
            self.offset[vertex] ^= difference
        self.members[left].extend(self.members[right])
        self.members[right].clear()
        return True


def count_histogram(rows, variables, start=0, target=1):
    """Histogram of disjoint last-reset cases by their power-of-two size.

    Time O(L + v log(v+2)) on a word RAM given the rows as a sequence.
    Every moved member joins a component of at least twice its previous size.
    """
    if variables < 0 or start not in (0, 1) or target not in (0, 1):
        raise ValueError("invalid variable count or state")
    if any(not (0 <= a < 2*(variables+1) and 0 <= b < 2*(variables+1))
           for a, b in rows):
        raise ValueError("literal code is outside the declared variable range")
    system = ParitySystem(variables)
    histogram = [0] * (variables + 1)
    for a, b in reversed(rows):
        # On a reset the next state is A. On a permutation the next state
        # is the old state XOR A. Both cases require the same phase update.
        system.add_literal(a)
        if not system.split(a, b, target, histogram):
            return histogram
    system.record(histogram, start ^ target)
    return histogram


def histogram_value(histogram):
    """Carry small counters and pack into bytes, in linear output size."""
    digits = bytearray((len(histogram) + 7) // 8)
    carry = 0
    for i, count in enumerate(histogram):
        carry, low = divmod(carry + count, 2)
        digits[i // 8] |= low << (i % 8)
    assert carry == 0  # Valid partitions have at most 2^v members in total.
    return int.from_bytes(digits, byteorder='little')


def exact_count(rows, variables, start=0, target=1):
    return histogram_value(count_histogram(rows, variables, start, target))


def brute_histograms(rows, variables):
    """Independently run both starting states on every physical assignment."""
    categories = {(s, t): {} for s in (0, 1) for t in (0, 1)}
    for x in range(1 << variables):
        def literal(code):
            i, sign = divmod(code, 2)
            return sign ^ ((x >> (i-1)) & 1 if i else 0)
        transitions = [(literal(a), literal(b)) for a, b in rows]
        last = max((i for i, (lo, hi) in enumerate(transitions) if lo == hi), default=-1)
        for start in (0, 1):
            state = start
            for row in transitions:
                state = row[state]
            cases = categories[start, state]
            cases[last] = cases.get(last, 0) + 1

    histograms = {}
    for states, cases in categories.items():
        histogram = [0] * (variables + 1)
        for count in cases.values():
            assert count & (count-1) == 0
            histogram[count.bit_length()-1] += 1
        histograms[states] = histogram
    return histograms


def check(rows, variables):
    histograms = brute_histograms(rows, variables)
    for start in (0, 1):
        totals = []
        for target in (0, 1):
            actual = count_histogram(rows, variables, start, target)
            expected = histograms[start, target]
            assert actual == expected, (rows, variables, start, target, actual, expected)
            value = sum(count * (1 << i) for i, count in enumerate(expected))
            assert histogram_value(actual) == value
            totals.append(value)
        assert sum(totals) == 1 << variables


def main():
    exhaustive = 0
    # All programs up to these respective lengths. Even a pair with no
    # variable reads includes arbitrary constant unconditional transitions.
    for variables, longest in ((0, 4), (1, 3), (2, 3), (3, 2)):
        literals = range(2 * (variables + 1))
        possible = list(product(literals, repeat=2))
        for length in range(longest + 1):
            for rows in product(possible, repeat=length):
                check(rows, variables)
                exhaustive += 1
    rng = Random(379)
    samples = 700
    for _ in range(samples):
        v = rng.randrange(3, 9)
        rows = [(rng.randrange(2*(v+1)), rng.randrange(2*(v+1)))
                for _ in range(rng.randrange(0, 33))]
        check(rows, v)

    # Many redundant permutation rows exercise repeated queries of the same
    # roots. A large dormant variable pool also checks full-size output.
    variables = 8192
    program = [(2,3)] * 8193
    assert exact_count(program, variables) == 1 << (variables-1)
    assert exact_count([], variables, start=1) == 1 << variables
    print(f"{exhaustive} exhaustive programs, {samples} seeded programs, "
          f"all four start/target pairs and complete last-reset histograms; "
          f"two {variables}-variable output checks.")


if __name__ == '__main__':
    main()
