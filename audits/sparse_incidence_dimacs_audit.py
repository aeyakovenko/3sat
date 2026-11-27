"""Audit the sparse incidence-to-proper-DIMACS serialization using only the stdlib."""

from itertools import permutations, product


def label_literal(literal, renaming):
    name = renaming[abs(literal)]
    return name if literal > 0 else -name


def relabel(rows, renaming):
    """Rows are indexed by all domain points. None denotes a variable point."""
    result = [None] * len(rows)
    for name, row in enumerate(rows, 1):
        if row is not None:
            result[renaming[name] - 1] = tuple(label_literal(x, renaming) for x in row)
    return tuple(result)


def row_clause(row, anchors):
    a, b, c = anchors
    if row is None or any(-x in row for x in row):
        return -a, b, c
    distinct = tuple(dict.fromkeys(row))
    return distinct + anchors[:3 - len(distinct)]


def serialize(rows):
    """Return ordinary ASCII bytes and the determining input names for each byte."""
    d = len(rows)
    anchors = (d + 1, d + 2, d + 3)
    a, b, _ = anchors
    width = len(str(d + 3)) + 1
    header = f"p cnf {d + 3} {2 * d + 7}\n".encode("ascii")
    parts = [header]
    determining_names = [frozenset()] * len(header)

    def emit(clause, support=()):
        assert len(clause) == len({abs(x) for x in clause}) == 3
        line = (" ".join(f"{x:{width}d}" for x in clause) + " 0\n").encode("ascii")
        parts.append(line)
        determining_names.extend([frozenset(support)] * len(line))

    for excluded in product((0, 1), repeat=3):
        if any(excluded):
            emit(tuple(-x if bit else x for x, bit in zip(anchors, excluded)))
    for name in range(1, d + 1):
        emit((name, -a, b))
    for name, row in enumerate(rows, 1):
        if row is not None:
            assert len(row) <= 3
            assert all(1 <= abs(x) <= d and rows[abs(x) - 1] is None for x in row)
        support = {name} | {abs(x) for x in row or ()}
        emit(row_clause(row, anchors), support)
    return b"".join(parts), determining_names


def parse(text):
    header, *body = text.splitlines()
    kind, cnf, names, count = header.split()
    assert (kind, cnf) == (b"p", b"cnf") and int(count) == len(body)
    clauses = []
    for line in body:
        x, y, z, end = map(int, line.split())
        assert end == 0 and all(1 <= abs(i) <= int(names) for i in (x, y, z))
        assert len({abs(x), abs(y), abs(z)}) == 3
        clauses.append((x, y, z))
    assert {abs(x) for row in clauses for x in row} == set(range(1, int(names) + 1))
    return int(names), tuple(clauses)


def evaluate(clauses, true_names):
    return all(any((abs(x) in true_names) == (x > 0) for x in clause) for clause in clauses)


def check_clause_normalization():
    checked = 0
    for length in range(4):
        for clause in product((1, -1, 2, -2, 3, -3), repeat=length):
            rows = (None, None, None, clause)
            names, compiled = parse(serialize(rows)[0])
            assert names == 7
            for values in product((False, True), repeat=3):
                true_names = {i for i, value in enumerate(values, 1) if value}
                assert evaluate(compiled, true_names) == evaluate([clause], true_names)
            for bits in product((False, True), repeat=3):
                anchors = {i for i, value in enumerate(bits, 5) if value}
                assert evaluate(compiled[:7], anchors) == (not any(bits))
            checked += 1
    return checked


def word_value(text, bit_start, bit_end):
    first, end = bit_start // 8, (bit_end + 7) // 8
    value = int.from_bytes(text[first:end], 'little')
    return (value >> (bit_start % 8)) & ((1 << (bit_end - bit_start)) - 1)


def check_renamings(rows, expected, exhaustive=True):
    text, supports = serialize(rows)
    d = len(rows)
    widths = (11, 19, 37, 64)
    probes = []
    for width in widths:
        for start in range(0, 8 * len(text), width):
            end = min(start + width, 8 * len(text))
            names = frozenset().union(*supports[start // 8:(end + 7) // 8])
            probes.append((start, end, names, word_value(text, start, end)))

    def source_assignment_values(instance):
        variables = [i for i, row in enumerate(instance, 1) if row is None]
        for bits in product((False, True), repeat=len(variables)):
            yield {v for v, b in zip(variables, bits) if b}

    source = tuple(row for row in rows if row is not None)
    assert any(evaluate(source, a) for a in source_assignment_values(rows)) == expected
    orders = permutations(range(1, d + 1)) if exhaustive else (
        tuple(range(1, d + 1)), tuple(range(d, 0, -1)), tuple(range(2, d + 1)) + (1,))
    checks = 0
    count = 0
    for order in orders:
        renaming = (0,) + order
        moved = relabel(rows, renaming)
        new_text, _ = serialize(moved)
        assert len(new_text) == len(text)
        _, compiled = parse(new_text)
        for assignment in source_assignment_values(rows):
            mapped = {renaming[name] for name in assignment}
            assert evaluate(compiled, mapped) == evaluate(source, assignment)
        fixed = {i for i in range(1, d + 1) if renaming[i] == i}
        for start, end, names, old in probes:
            if names <= fixed:
                assert word_value(new_text, start, end) == old
                checks += 1
        count += 1
    return count, checks


def main():
    normalized = check_clause_normalization()
    yes = (None, None, None, (1, -2, 3), (-1, 2, -3))
    no = (None, None, None, (1,), (-1,))
    proper_no = (None, None, None) + tuple(
        tuple(-i if bit else i for i, bit in enumerate(bits, 1))
        for bits in product((0, 1), repeat=3))
    results = [check_renamings(yes, True), check_renamings(no, False),
               check_renamings(proper_no, False, exhaustive=False)]
    print(f"{normalized} clause forms, {sum(r[0] for r in results)} labeled files, "
          f"{sum(r[1] for r in results)} fixed-support packed-word checks passed")


if __name__ == "__main__":
    main()
