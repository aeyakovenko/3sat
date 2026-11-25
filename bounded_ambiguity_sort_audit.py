"""Audit a single record sort for the one- and two-witness SAT contraction.

Both columns guess one truth bit at each literal occurrence. A diagonal pair
of satisfying assignments contributes +1, a strictly increasing pair -1.
The two coefficients coincide over F2. All variables in these fixtures occur.
"""

from itertools import product


def bitonic_schedule(slots):
    width = 1 << (slots - 1).bit_length()
    gates = []
    block = 2
    while block <= width:
        gap = block // 2
        while gap:
            for i in range(width):
                j = i ^ gap
                if i < j:
                    gates.append((i, j, i & block == 0))
            gap //= 2
        block *= 2
    return width, gates


class OccurrenceVerifier:
    def __init__(self, formula):
        assert formula
        assert all(len(c) == 3 and len({abs(x) for x in c}) == 3 for c in formula)
        self.literals = [x for clause in formula for x in clause]
        self.names = sorted({abs(x) for x in self.literals})
        assert self.names[0] > 0
        self.positions = {name: i for i, name in enumerate(self.names)}
        self.width, self.gates = bitonic_schedule(len(self.literals))

    def weight(self, guesses):
        """Check physical clauses, route both payloads, then check adjacent rows."""
        assert len(guesses) == len(self.literals)
        literal_values = [
            pair if literal > 0 else pair ^ 3
            for literal, pair in zip(self.literals, guesses)
        ]
        for i in range(0, len(literal_values), 3):
            if (literal_values[i] | literal_values[i + 1] | literal_values[i + 2]) != 3:
                return 0

        rows = [(abs(x), i, pair) for i, (x, pair) in enumerate(zip(self.literals, guesses))]
        slots = len(rows)
        rows.extend((self.names[-1] + 1, i, 0) for i in range(slots, self.width))
        for i, j, ascending in self.gates:
            # (name, original slot) is unique. The payload does not choose a route.
            if (rows[i][:2] > rows[j][:2]) == ascending:
                rows[i], rows[j] = rows[j], rows[i]

        previous_name = None
        previous_pair = None
        first_difference = None
        for name, _, pair in rows[:slots]:
            if name == previous_name and pair != previous_pair:
                return 0
            if first_difference is None and pair in (1, 2):
                # 01 is left=0, right=1. Name order orients each unordered pair.
                first_difference = pair
            previous_name, previous_pair = name, pair
        if first_difference is None:
            return 1
        return -1 if first_difference == 1 else 0

    def consistent_guesses(self):
        # Eliminate the adjacent equalities exactly. Each surviving per-name
        # value expands to one occurrence string, without a multiplicity.
        for values in product(range(4), repeat=len(self.names)):
            yield [values[self.positions[abs(x)]] for x in self.literals]


def contract(verifier, guesses):
    diagonal = increasing = signed = field_bit = 0
    for payload in guesses:
        weight = verifier.weight(payload)
        diagonal += weight == 1
        increasing += weight == -1
        signed += weight
        field_bit ^= weight & 1
    return diagonal, increasing, signed, field_bit


def satisfying_assignments(formula, names):
    answers = set()
    for bits in product((0, 1), repeat=len(names)):
        values = dict(zip(names, bits))
        if all(any(values[abs(x)] == (x > 0) for x in c) for c in formula):
            answers.add(bits)
    return answers


def check_formula(formula, *, enumerate_occurrences=False):
    verifier = OccurrenceVerifier(formula)
    solutions = satisfying_assignments(formula, verifier.names)
    pairs = {(a, b) for a in solutions for b in solutions if a < b}
    expected = len(solutions) - len(pairs)
    observed = contract(verifier, verifier.consistent_guesses())
    assert observed == (len(solutions), len(pairs), expected, expected % 2)
    if len(solutions) <= 2:
        assert observed[2:] == (int(bool(solutions)), int(bool(solutions)))
    if enumerate_occurrences:
        def checked_guesses():
            for raw in product(range(4), repeat=len(verifier.literals)):
                values = {abs(x): pair for x, pair in zip(verifier.literals, raw)}
                consistent = all(values[abs(x)] == pair for x, pair in zip(verifier.literals, raw))
                left = tuple(values[name] >> 1 for name in verifier.names)
                right = tuple(values[name] & 1 for name in verifier.names)
                weight = 0
                if consistent and left in solutions and right in solutions:
                    weight = int(left == right) - int(left < right)
                assert verifier.weight(raw) == weight
                yield raw

        assert contract(verifier, checked_guesses()) == observed
    return len(solutions), observed


def signed_clauses():
    clauses = []
    for i, signs in enumerate(product((1, -1), repeat=3)):
        terms = tuple(name * sign for name, sign in enumerate(signs, start=1))
        shift = i % 3
        clauses.append(terms[shift:] + terms[:shift])
    return clauses


def main():
    clauses = signed_clauses()
    histogram = [0] * 8
    for mask in range(1, 1 << len(clauses)):
        formula = [c for i, c in enumerate(clauses) if (mask >> i) & 1]
        count, _ = check_formula(formula)
        histogram[count] += 1
    assert histogram == [1, 8, 28, 56, 70, 56, 28, 8]

    # Distinct variable sets, a repeated variable across clauses, sparse names,
    # and both polarities. Enumerate all 4^6 raw occurrence guesses as well.
    check_formula([(-17, 5, 11), (11, -2, 17)], enumerate_occurrences=True)
    failure = check_formula(clauses[:5])
    assert failure == (3, (3, 3, 0, 0))
    print("Checked all 255 nonempty subsets of the eight proper three-variable clauses.")
    print("All 37 formulas with at most two solutions give the SAT bit over Z and F2.")
    print("A separate two-clause formula agrees on all 4,096 raw two-column guesses.")
    print("Three solutions give three diagonal terms and three increasing pairs: both sums vanish.")


if __name__ == "__main__":
    main()
