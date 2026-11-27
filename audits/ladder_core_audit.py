"""Probe an unsatisfiable 73-clause subformula in the canonical one-point ladder."""

import re
from itertools import pairwise, product

from constant_point_lift_audit import lift
from simple_permutation_successor import coloring_dimacs


def core_rows(size):
    """Map zero-based body rows to clauses without generating the long permutation."""
    if size < 8:
        raise ValueError("the uniform ladder starts at eight vertices")
    a, c, d = 4, size - 2, size - 1
    pin = 3 * size + 1
    width = len(str(pin)) + 1
    rows = {}

    def line(index, names):
        rows[index] = (" ".join(str(x).rjust(width) for x in names) + " 0\n").encode()

    vertices = [0, 1, 2, 3, a, c, d]
    for vertex in vertices:
        line(vertex, [3 * vertex + color for color in (1, 2, 3)])

    def add_edge(index, u, v):
        for color in (1, 2, 3):
            for sign_index, z in enumerate((pin, -pin)):
                row = size + 6 * index + 2 * (color - 1) + sign_index
                line(row, [-3 * u - color, -3 * v - color, z])

    for u in (0, 1, 2, 3, c):
        add_edge(u, u, u + 1)
    block = (1, c, a, d, 3, 0, 2)
    padding = size - 7
    start = (padding + 1) // 2
    for i, (u, v) in enumerate(pairwise(block)):
        add_edge(size - 1 + start + i, u, v)
    return rows


# A numeric line containing a zero closes any open clause. Reading a complete
# line also distinguishes a delimiter from a zero inside a line comment.
NUMERIC_LINE = re.compile(rb"(?: *-?[1-9][0-9]* +){3}0\n")
HEADER = re.compile(rb"p cnf ([1-9][0-9]*) ([1-9][0-9]*)\n")


def has_ladder_contradiction(data):
    """True certifies NO under the whole-file DIMACS grammar. False is inconclusive."""
    byte_length = len(data)
    header = HEADER.match(data, 0, min(byte_length, 16 + 2 * byte_length.bit_length()))
    if header is None:
        return False
    variables, clauses = map(int, header.groups())
    size, remainder = divmod(variables - 1, 3)
    if remainder or size < 8 or clauses != 13 * size - 12:
        return False
    line_length = 3 * (1 + len(str(variables))) + 5
    if header.end() + clauses * line_length != byte_length:
        return False
    for index, expected in core_rows(size).items():
        start = header.end() + line_length * index
        if data[start : start + line_length] != expected:
            return False
        if index:
            prev = start - line_length
            if (
                data[prev - 1 : prev] != b"\n"
                or NUMERIC_LINE.fullmatch(data[prev:start]) is None
            ):
                return False
    return True


def audit():
    for k in (1, 2, 3, 4, 7, 16, 25, 26, 27, 128, 326, 1024):
        size = 7 + k
        image = coloring_dimacs(lift((1, 3, 0, 2), k))
        assert has_ladder_contradiction(image)
        rows = core_rows(size)
        assert len(rows) == 73
        if k == 1:
            # Check the projected clauses directly under both pin values.
            # Positive vertex clauses let us restrict to one flag per vertex,
            # since all other occurrences of those flags are negative.
            extracted = [list(map(int, row.split()[:-1])) for row in rows.values()]
            vertices = [0, 1, 2, 3, 4, size - 2, size - 1]
            pin = 3 * size + 1
            single_fail = set()
            for choices in product((1, 2, 3), repeat=len(vertices)):
                flags = {3 * v + col for v, col in zip(vertices, choices)}
                for z in (False, True):
                    flags.discard(pin)
                    if z:
                        flags.add(pin)
                    bad = [
                        i
                        for i, clause in enumerate(extracted)
                        if not any((abs(x) in flags) == (x > 0) for x in clause)
                    ]
                    assert bad
                    if len(bad) == 1:
                        single_fail.add(bad[0])
            # Removing a vertex's at-least-one clause allows no flag at that
            # vertex. Check all other rows are then simultaneously satisfiable.
            for missing, v in enumerate(vertices):
                rest = [u for u in vertices if u != v]
                for choices in product((1, 2, 3), repeat=len(rest)):
                    flags = {3 * u + col for u, col in zip(rest, choices)}
                    if all(
                        any((abs(x) in flags) == (x > 0) for x in clause)
                        for i, clause in enumerate(extracted)
                        if i != missing
                    ):
                        single_fail.add(missing)
                        break
            assert single_fail == set(range(73))

        lines = image.splitlines(keepends=True)
        target = next(i for i in sorted(rows) if i > 0 and i - 1 not in rows)
        # Corrupt just the synchronizer before a verified row
        # in a way that preserves a trailing ' 0' but puts it in a comment.
        lines[target] = b"c" + lines[target][1:]
        assert not has_ladder_contradiction(b"".join(lines))
        # A change to an uninspected row can leave the NO certificate intact.
        free = next(
            i for i in range(len(lines) - 1) if i not in rows and i + 1 not in rows
        )
        lines = image.splitlines(keepends=True)
        lines[free + 1] = lines[1]
        assert has_ladder_contradiction(b"".join(lines))
    assert not has_ladder_contradiction(coloring_dimacs(tuple(range(8))))
    print("73 physical clauses certify all 12 tested rungs, up to 1,031 vertices.")


if __name__ == "__main__":
    audit()
