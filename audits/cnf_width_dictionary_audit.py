"""Check a parsimonious DIMACS CNF to proper 3-CNF reduction.

This executable instantiates only dictionary entries used by the input. The
model universe consists of the occurring names. No array is indexed by a
decimal name, and names are never converted to Python integers.
"""

from itertools import product


def decimal(token):
    if not token or not token.isdigit():
        raise ValueError("invalid decimal token")
    return token.lstrip(b"0") or b"0"


def name(lit):
    return lit.removeprefix(b"-")


def neg(lit):
    return name(lit) if lit.startswith(b"-") else b"-" + lit


def canonical(lit):
    digits = decimal(name(lit))
    return b"-" + digits if lit.startswith(b"-") else digits


def numeric_key(digits):
    return len(digits), digits


def read_dimacs(raw):
    """Keep raw literal spelling so that chunk budgets count its bytes."""
    lines = [line.split() for line in raw.splitlines()
             if line.strip() and not line.lstrip().startswith(b"c")]
    if not lines or len(lines[0]) != 4 or lines[0][:2] != [b"p", b"cnf"]:
        raise ValueError("invalid problem line")
    maximum, count = map(decimal, lines[0][2:])
    clauses = []
    clause = []
    for line in lines[1:]:
        for token in line:
            lit = canonical(token)
            if lit == b"0":
                clauses.append(tuple(clause))
                clause = []
            elif lit == b"-0" or numeric_key(name(lit)) > numeric_key(maximum):
                raise ValueError("literal outside declared range")
            else:
                clause.append(token)
    if clause or str(len(clauses)).encode() != count:
        raise ValueError("incorrect clause count or missing terminator")
    return clauses


def write_dimacs(clauses):
    maximum = max((name(canonical(lit)) for clause in clauses for lit in clause),
                  key=numeric_key, default=b"0")
    header = b"p cnf %s %d\n" % (maximum, len(clauses))
    return header + b"".join(b" ".join((*clause, b"0")) + b"\n" for clause in clauses)


def old_literal(token):
    # The last digit separates source names from all helper names.
    return canonical(token) + b"1"


def pieces(clause, budget):
    """Greedy whole-token chunks. An over-budget token forms its own piece."""
    chunk = []
    size = 0
    for token in clause:
        cost = len(token) + 1
        if chunk and size + cost > budget:
            yield tuple(chunk)
            chunk = []
            size = 0
        chunk.append(token)
        size += cost
    if chunk:
        yield tuple(chunk)


class ProperCNF:
    def __init__(self):
        self.clauses = {}
        self.helpers = 0
        self.anchors = tuple(self.fresh() for _ in range(3))
        # Each nonzero assignment falsifies its own clause; 000 survives.
        for signs in product((False, True), repeat=3):
            if any(signs):
                clause = tuple(neg(x) if bit else x for x, bit in zip(self.anchors, signs))
                self.add_proper(clause)

    def fresh(self):
        self.helpers += 1
        return str(self.helpers).encode() + b"2"

    def add_proper(self, clause):
        assert len(clause) == len({name(lit) for lit in clause}) == 3
        self.clauses[tuple(sorted(clause))] = None

    def emit(self, *literals):
        literals = list(dict.fromkeys(literals))
        if any(neg(lit) in literals for lit in literals):
            return
        used = {name(lit) for lit in literals}
        for anchor in self.anchors:
            if len(literals) == 3:
                break
            if anchor not in used:
                literals.append(anchor)
        self.add_proper(literals)

    def disjunction(self, literals):
        value, *rest = literals
        for term in rest:
            out = self.fresh()
            self.emit(neg(value), out)
            self.emit(neg(term), out)
            self.emit(value, term, neg(out))
            value = out
        return value


def reduce_width(raw, budget=None):
    source = read_dimacs(raw)
    # A 256-letter alphabet has at most O(N^(1/3)) keys at this width.
    if budget is None:
        budget = max(1, (max(len(raw), 1).bit_length() - 1) // 24)
    if budget < 1:
        raise ValueError("positive chunk size required")
    target = ProperCNF()
    dictionary = {}
    for clause in source:
        flags = []
        for part in pieces(clause, budget):
            if len(part) == 1:
                flags.append(old_literal(part[0]))
                continue
            if part not in dictionary:
                dictionary[part] = target.disjunction(tuple(map(old_literal, part)))
            flags.append(dictionary[part])
        if flags:
            target.emit(target.disjunction(flags))
        else:
            target.emit()

    # Preserve free source bits even if simplification removed every other use.
    used = {name(lit) for clause in target.clauses for lit in clause}
    old = {name(old_literal(token)) for clause in source for token in clause}
    a, b, _ = target.anchors
    for var in sorted(old - used):
        target.add_proper((var, neg(a), b))
    return write_dimacs(target.clauses)


def dpll_count(clauses, variables, assignment):
    """Count extensions, stopping at two. A residual free variable counts."""
    while True:
        active = []
        for clause in clauses:
            if any(assignment.get(name(lit)) == (lit == name(lit))
                   for lit in clause if name(lit) in assignment):
                continue
            rest = tuple(lit for lit in clause if name(lit) not in assignment)
            if not rest:
                return 0
            active.append(rest)
        if not active:
            return 1 if len(assignment) == len(variables) else 2
        shortest = min(active, key=len)
        branch = name(shortest[0])
        if len(shortest) == 1:
            assignment[branch] = shortest[0] == branch
            clauses = active
        else:
            total = 0
            for bit in (False, True):
                total += dpll_count(active, variables, {**assignment, branch: bit})
                if total >= 2:
                    return 2
            return total


def audit(raw, budget):
    source = [tuple(map(canonical, clause)) for clause in read_dimacs(raw)]
    original = sorted({name(lit) for clause in source for lit in clause})
    output = reduce_width(raw, budget)
    target = read_dimacs(output)
    assert all(len(clause) == len({name(lit) for lit in clause}) == 3 for clause in target)
    assert len(target) == len(set(target))
    variables = {name(lit) for clause in target for lit in clause}
    assert {old_literal(var) for var in original} <= variables
    for values in product((False, True), repeat=len(original)):
        assignment = dict(zip(original, values))
        expected = all(any(assignment[name(lit)] == (lit == name(lit)) for lit in clause)
                       for clause in source)
        pins = {old_literal(var): value for var, value in assignment.items()}
        actual = dpll_count(target, variables, pins)
        assert actual == int(expected), (source, assignment, budget, actual)
    return 1 << len(original)


def main():
    files = assignments = 0
    tokens = (b"1", b"-1", b"2", b"-2")
    small = [clause for width in range(3) for clause in product(tokens, repeat=width)]
    for left, right in product(small, repeat=2):
        raw = write_dimacs([left, right])
        for budget in (1, 4, 12):
            assignments += audit(raw, budget)
            files += 1

    huge = b"9" * 5000
    repeated = (b"1", b"-2", b"3", b"-4", b"5")
    cases = [
        b"p cnf 0 0\n",
        b"p cnf 78 0\n",                       # All declared names unused.
        b"p cnf 78 1\n0\n",                    # A single empty clause.
        b"c Only names 1 and 2 occur.\np cnf 78 2\n0001 -01 0\n2 -2 0\n",
        b"p cnf 3 2\n1 -2\n 3 0 000  \n",
        write_dimacs([repeated] * 18),
        write_dimacs([(*repeated, b"-1", *repeated), (b"1", b"-1"), (b"2", b"-2")]),
        write_dimacs([(b"-" + huge, b"2", b"0001"), (huge, b"-0002"),
                      (b"-" + b"0" * 65 + b"1", b"1")]),
        write_dimacs([tuple(b"1" for _ in range(45)), (b"-1",)]),
    ]
    for raw in cases:
        for budget in (None, 1, 4, 8, 15, 31):
            assignments += audit(raw, budget)
            files += 1
    # Assert that identical short clauses reuse the actual gates.
    assert reduce_width(write_dimacs([repeated]), 31) == reduce_width(
        write_dimacs([repeated] * 18), 31)
    # Long original identifiers and oversized singleton fragments keep their signs.
    split = list(pieces((b"1", b"-" + huge, b"2", b"3"), 5))
    assert split == [(b"1",), (b"-" + huge,), (b"2", b"3")]
    print(f"{files} proper 3-CNF outputs; {assignments} source assignments checked for unique extension")


if __name__ == "__main__":
    main()
