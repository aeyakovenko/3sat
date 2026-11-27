"""Independent checks of both orientations of iterated four-point lifts."""

import itertools

from constant_point_lift_audit import lift
from simple_permutation_successor import coloring_dimacs, simple


def graph_edges(order):
    return {tuple(sorted(e)) for e in itertools.pairwise(order)} | {
        (j, j + 1) for j in range(len(order) - 1)
    }


def violations(row, edges):
    return {e for e in edges if row[e[0]] == row[e[1]]}


def extend(row, first, defective=False):
    # Color the new vertices (a,b,c,d) in their red order.
    old_max = row[-1]
    if defective:
        assert row[first] != old_max
        c = (old_max + 1) % 3
        a = d = (old_max + 2) % 3
        b = old_max
    else:
        c = old_max
        b = next(col for col in range(3) if col not in (c, row[first]))
        a = next(col for col in range(3) if col not in (c, b))
        d = next(col for col in range(3) if col not in (c, a))
    return row + (a, b, c, d)


def dimacs_check(order, edge, row):
    original = coloring_dimacs(order).splitlines(keepends=True)
    n = len(order)
    u, c = edge
    edge_position = order.index(u)
    assert order[edge_position + 1] == c
    start = 1 + n + 6 * (n - 1 + edge_position)
    width = 1 + len(str(3 * n + 1))
    lines = original.copy()
    for j in range(6):
        line = lines[start + j]
        offset = width + 1
        field = line[offset : offset + width]
        assert int(field) == -(3 * c + 1 + j // 2)
        lines[start + j] = (
            line[:offset] + field.replace(b"-", b" ") + line[offset + width :]
        )
    assert sum(a != b for a, b in zip(b"".join(lines), b"".join(original))) == 6
    positive = {3 * v + col + 1 for v, col in enumerate(row)}
    for line in lines[1:]:
        clause = [int(lit) for lit in line.split()]
        assert clause[-1] == 0
        assert any((abs(lit) in positive) == (lit > 0) for lit in clause[:-1])


def audit():
    # The fixed certificate on orientation 2413 uses only ranks 1 through 7.
    constant = (1, 3, 0, 2)
    triangles = ((1, 2, 3), (1, 3, 4), (5, 6, 7), (2, 6, 7))
    fixed = {(3, 4)}
    for x, y, z in triangles:
        fixed.update((a - 1, b - 1) for a, b in ((x, y), (y, z), (x, z)))
    assert len(fixed) == 11

    order = (2, 0, 3, 1)
    deficient = (0, 1, 2, 0)
    prior_missing = (0, 3)
    colorings = {}
    switched_checks = 0
    for stage in range(1, 81):
        assert violations(deficient, graph_edges(order)) == {prior_missing}
        top = len(order) - 1
        pos = order.index(top)
        u = order[pos - 1]
        # The three central choices in a one-site interpolation give the same
        # permutation, because no other fresh vertex has yet been inserted.
        central = order[:pos] + (top + 1,) + order[pos:]
        assert not violations(
            deficient + ((deficient[u] + 1) % 3,), graph_edges(central)
        )
        assert not simple((top + 1,) + order)

        c = len(order) + 2
        edge = (u, c)
        assert edge == (4 * stage - 4, 4 * stage + 2)
        colorings = {e: extend(row, order[0]) for e, row in colorings.items()}
        colorings[edge] = extend(deficient, order[0])
        deficient = extend(deficient, order[0], defective=True)
        order = lift(order, 1)
        actual = graph_edges(order)
        prior_missing = (len(order) - 4, len(order) - 1)
        assert violations(deficient, actual) == {prior_missing}
        for i, (e, row) in enumerate(colorings.items(), 1):
            assert violations(row, actual) == {e}
            idx = order.index(e[1])
            switched = list(order)
            switched[idx], switched[idx + 1] = switched[idx + 1], switched[idx]
            assert not violations(row, graph_edges(switched))
            if stage <= 12:
                assert simple(switched) == (i < stage)
                dimacs_check(order, e, row)
            switched_checks += 1
        constant = lift(constant, 1)
        assert fixed <= graph_edges(constant)
    print(
        "Both orientation invariants and every one-site intermediate verified through 80 lifts."
    )
    print(
        f"Checked {switched_checks:,} edge-deleted colorings and native positive swaps."
    )
    print(
        "Checked switch simplicity and six sign flips in every corresponding DIMACS file through 12 lifts."
    )


if __name__ == "__main__":
    audit()
