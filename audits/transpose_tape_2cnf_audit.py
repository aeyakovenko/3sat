"""Audit a fixed-slot decimal DIMACS reduction of word-matrix transpose to UNSAT.

Run with Python 3. The solver uses implication-graph reachability for arbitrary
2-CNF files, including files with sparse decimal variable identifiers.
"""

from itertools import product

def digits(value, width):
    assert 0 <= value < 1 << width
    return f"{value:0{width}b}".translate(str.maketrans("01", "12"))


def serialize(side, width, row_records, column_records):
    """Both inputs are in the incoming physical order of their own matrix."""
    coord_bits = max(1, (side - 1).bit_length())
    cells = side * side
    assert len(row_records) == len(column_records) == cells

    def anchor(rank):
        return "1" + digits(rank, 2 * coord_bits + 1) + "1" * width

    def key(row, column, value):
        return ("2" + digits(row, coord_bits) + digits(column, coord_bits)
                + "1" + digits(value, width))

    largest = "3" + "1" * (2 * coord_bits + 1 + width)
    setup = (f"p cnf {largest} {2 * cells + 3}\n"
             f"{largest} 0\n{anchor(0)} 0\n-{anchor(cells)} 0\n")
    left, right = [], []
    for rank, value in enumerate(row_records):
        row, column = divmod(rank, side)
        left.append(f"-{anchor(rank)} {key(row, column, value)} 0\n")
    for position, value in enumerate(column_records):
        column, row = divmod(position, side)
        rank = row * side + column
        right.append(f"-{key(row, column, value)} {anchor(rank + 1)} 0\n")

    slots = [line.encode("ascii") for line in left + right]
    slot_size = len(slots[0])
    assert all(len(line) == slot_size for line in slots)
    return setup.encode("ascii") + b"".join(slots), len(setup), slot_size


def is_satisfiable(raw):
    lines = raw.splitlines()
    prefix, kind, largest, clause_count = lines[0].split()
    assert (prefix, kind) == (b"p", b"cnf")
    assert len(lines) - 1 == int(clause_count)
    graph = {}
    for line in lines[1:]:
        *literals, end = map(int, line.split())
        assert end == 0 and 1 <= len(literals) <= 2
        for literal in literals:
            assert literal and abs(literal) <= int(largest)
            graph.setdefault(literal, set())
            graph.setdefault(-literal, set())
        left, right = literals[0], literals[-1]
        graph[-left].add(right)
        graph[-right].add(left)
    assert max(graph) == int(largest)

    def reachable(start, target):
        visited, pending = {start}, [start]
        while pending:
            literal = pending.pop()
            if literal == target:
                return True
            for successor in graph[literal] - visited:
                visited.add(successor)
                pending.append(successor)
        return False

    return all(not (reachable(v, -v) and reachable(-v, v)) for v in graph if v > 0)


def transpose(records, side):
    return tuple(records[row * side + column]
                 for column in range(side) for row in range(side))


def check_pair(side, width, rows, columns):
    raw, start, slot = serialize(side, width, rows, columns)
    assert is_satisfiable(raw) == (transpose(rows, side) != columns)
    return raw, start, slot


def edit_checks(side, width):
    """Flip every bit of every physical record in each matrix independently."""
    cells = side * side
    rows = tuple((i * (i + 3) + i // side) % (1 << width) for i in range(cells))
    columns = transpose(rows, side)
    base, start, slot = check_pair(side, width, rows, columns)
    checks = 0
    for half, records in enumerate((rows, columns)):
        for position, old in enumerate(records):
            for bit in range(width):
                changed = list(records)
                changed[position] = old ^ (1 << bit)
                pair = (changed, columns) if half == 0 else (rows, changed)
                raw, new_start, new_slot = check_pair(side, width, *pair)
                assert (new_start, new_slot, len(raw)) == (start, slot, len(base))
                changed_indices = [j for j, (x, y) in enumerate(zip(base, raw)) if x != y]
                assert len(changed_indices) == 1
                index = changed_indices[0]
                assert (index - start) // slot == half * cells + position
                assert (index - start) // (side * slot) == half * side + position // side
                checks += 1
    return checks


def main():
    count = 0
    for side, width in ((1, 1), (1, 2), (1, 3), (2, 1)):
        arrays = list(product(range(1 << width), repeat=side * side))
        for rows in arrays:
            for columns in arrays:
                check_pair(side, width, rows, columns)
                count += 1
    edits = sum(edit_checks(side, width) for side, width in ((2, 2), (3, 3), (5, 6)))
    print(f"{count} exhaustive pairs and {edits} single-bit edits passed")


if __name__ == "__main__":
    main()
