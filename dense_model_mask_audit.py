"""Audit the proper DIMACS mask family and its linear-measurement bound."""

from collections import Counter
from itertools import combinations_with_replacement, product


class MaskFamily:
    def __init__(self, groups, width):
        self.count = 0
        self.fixed = []
        self.anchors = self.allocate(3)
        for bits in range(1, 8):
            self.clause(*(v if not bits & (1 << j) else -v
                          for j, v in enumerate(self.anchors)))
        self.rows, self.row_prefixes = self.one_hot(groups)
        self.offsets, self.offset_prefixes = self.one_hot(width)
        self.library = self.allocate(1 << width)
        for pattern, v in enumerate(self.library):
            for j, selected in enumerate(self.offsets):
                self.clause(-selected, v if pattern & (1 << j) else -v)

    def allocate(self, amount):
        start = self.count + 1
        self.count += amount
        return list(range(start, self.count + 1))

    def clause(self, *literals):
        used = {abs(x) for x in literals}
        assert len(used) == len(literals)
        pads = [x for x in self.anchors if x not in used]
        self.fixed.append(tuple(literals) + tuple(pads[:3-len(literals)]))

    def one_hot(self, length):
        values = self.allocate(length)
        prefix = self.allocate(length + 1)
        self.clause(-prefix[0])
        self.clause(prefix[-1])
        for i, value in enumerate(values):
            old, new = prefix[i:i+2]
            self.clause(-old, new)
            self.clause(-value, new)
            self.clause(old, value, -new)
            self.clause(-old, -value)
        return values, prefix

    def serialize(self, mask):
        clauses = self.fixed.copy()
        width = len(self.offsets)
        for g, row in enumerate(self.rows):
            pattern = (mask >> (g * width)) & ((1 << width) - 1)
            clauses.append((-row, self.library[pattern], self.anchors[0]))
        fields = len(str(self.count)) + 1
        text = [f"p cnf {self.count} {len(clauses)}\n"]
        for clause in clauses:
            text.append(" ".join(f"{lit:>{fields}d}" for lit in clause) + " 0\n")
        return "".join(text).encode("ascii")

    def expected(self, group, offset):
        # Derive every variable from the selected pair, independently of DPLL.
        true = {self.rows[group], self.offsets[offset]}
        true.update(self.row_prefixes[group+1:])
        true.update(self.offset_prefixes[offset+1:])
        true.update(v for i, v in enumerate(self.library) if i & (1 << offset))
        return tuple(v in true for v in range(1, self.count + 1))


def parse_file(raw):
    header, *body = raw.splitlines()
    marker, kind, count_text, rows = header.split()
    assert (marker, kind) == (b"p", b"cnf") and len(body) == int(rows)
    count = int(count_text)
    clauses = []
    for row in body:
        a, b, c, zero = map(int, row.split())
        assert zero == 0 and len({abs(a), abs(b), abs(c)}) == 3
        clauses.append((a, b, c))
    assert {abs(v) for clause in clauses for v in clause} == set(range(1, count+1))
    return count, clauses


def full_models(count, clauses):
    def visit(assignment):
        while True:
            unresolved = Counter()
            unit = None
            for clause in clauses:
                if any(assignment.get(abs(lit)) == (lit > 0) for lit in clause):
                    continue
                open_literals = [lit for lit in clause if abs(lit) not in assignment]
                if not open_literals:
                    return
                if len(open_literals) == 1:
                    unit = open_literals[0]
                    break
                unresolved.update(abs(lit) for lit in open_literals)
            if unit is None:
                break
            assignment[abs(unit)] = unit > 0
        if unresolved:
            pivot = unresolved.most_common(1)[0][0]
            for value in (False, True):
                branch = assignment.copy()
                branch[pivot] = value
                yield from visit(branch)
        else:
            free = [v for v in range(1, count+1) if v not in assignment]
            for tail in product((False, True), repeat=len(free)):
                model = assignment.copy()
                model.update(zip(free, tail))
                yield tuple(model[v] for v in range(1, count+1))

    return set(visit({}))


def check_files(groups, width):
    family = MaskFamily(groups, width)
    expected = [family.expected(g, j) for g in range(groups) for j in range(width)]
    assert len(set(expected)) == groups * width
    proper_files = 1 << len(expected)
    lengths = set()
    total_models = 0
    for mask in range(proper_files):
        raw = family.serialize(mask)
        lengths.add(len(raw))
        actual = full_models(*parse_file(raw))
        assert actual == {model for i, model in enumerate(expected) if mask & (1 << i)}
        total_models += len(actual)
    assert len(lengths) == 1
    print(f"G={groups}, b={width}: {proper_files} equal-length proper files, "
          f"{total_models} full models, {lengths.pop()} bytes/file.")


def check_zero_sums(p, dimension):
    # Column permutations preserve the number of zero-sum subsets, so the
    # multisets cover all ordered measurement matrices up to this symmetry.
    vectors = list(product(range(p), repeat=dimension))
    index = {v: i for i, v in enumerate(vectors)}
    plus = [[index[tuple((x+y) % p for x, y in zip(a, b))] for b in vectors]
            for a in vectors]
    zero_free_limit = dimension * (p-1)
    cases = 0
    for q in range(1, zero_free_limit + 3):
        least = 1 << q
        for columns in combinations_with_replacement(range(len(vectors)), q):
            counts = [0] * len(vectors)
            counts[0] = 1
            for column in columns:
                updated = counts.copy()
                for i, amount in enumerate(counts):
                    updated[plus[i][column]] += amount
                counts = updated
            least = min(least, counts[0])
            assert counts[0] >= 1 << max(0, q - zero_free_limit)
            cases += 1
        assert least == 1 << max(0, q - zero_free_limit)
    return cases


def grouped_answers(mask, q, p, degree):
    # A field answer is given in its additive prime-field basis.
    width = degree * (p-1)
    for start in range(0, q, width):
        value = [0] * degree
        for offset in range(min(q-start, width)):
            coordinate = offset // (p-1)
            value[coordinate] += (mask >> (start+offset)) & 1
        assert all(0 <= entry < p for entry in value)
        yield tuple(value)


def check_grouping():
    cases = 0
    for p, degree, q in product((2, 3, 5), (1, 2, 3), range(1, 13)):
        width = degree * (p-1)
        for mask in range(1 << q):
            answers = list(grouped_answers(mask, q, p, degree))
            assert len(answers) == (q+width-1) // width
            assert any(any(value) for value in answers) == bool(mask)
            cases += 1
    return cases


if __name__ == "__main__":
    for shape in ((2, 2), (2, 3), (3, 2)):
        check_files(*shape)
    cases = sum(check_zero_sums(p, d)
                for p, d in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (5, 1)))
    print(f"{cases:,} coefficient-column multisets satisfy the multiplicity bound, "
          "with equality attained at every tested width.")
    print(f"{check_grouping():,} fixed-group measurement tests passed.")
