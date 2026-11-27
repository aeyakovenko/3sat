"""Exact hidden edge-word sizes for a binary parity-check kernel on a tree.

Run with Python 3.10+; no dependencies. Columns are nonnegative integer masks.
An interior vertex has degree three and an arbitrary local acceptance table.
The default charges even a leaf edge with its minimal syndrome dimension.
The second convention feeds each leaf bit directly into its adjacent table.
"""

from functools import lru_cache
from itertools import combinations
from random import Random


def extend_basis(basis, column):
    for vector in basis:
        column = min(column, column ^ vector)
    if not column:
        return basis
    return tuple(sorted((*basis, column), reverse=True))


def cut_widths(columns):
    if len(columns) < 2 or min(columns) < 0:
        raise ValueError("supply at least two nonnegative columns")
    full = (1 << len(columns)) - 1
    bases = [()] * (full + 1)
    for side in range(1, full + 1):
        low = side & -side
        bases[side] = extend_basis(bases[side ^ low], columns[low.bit_length() - 1])
    rank = [len(basis) for basis in bases]
    return [rank[side] + rank[full ^ side] - rank[full] for side in range(full + 1)]


def bipartitions(side):
    """Unordered nonempty bipartitions, visiting the side omitting the lowest bit."""
    remaining = side ^ (side & -side)
    part = remaining
    while part:
        yield part, side ^ part
        part = (part - 1) & remaining


def edge_prices(widths, charge_leaf_edges):
    if charge_leaf_edges:
        return widths
    full = len(widths) - 1
    return [
        0 if min(side.bit_count(), (full ^ side).bit_count()) <= 1 else w
        for side, w in enumerate(widths)
    ]


def optimum_tree(widths, charge_leaf_edges=True):
    """Returns minimum maximum width, plus a witnessing nested tree of leaf indices."""
    full = len(widths) - 1
    root_leaf = full.bit_length() - 1
    others = full >> 1
    price = edge_prices(widths, charge_leaf_edges)
    cost = [0] * (others + 1)
    split = [None] * (others + 1)
    for side in range(1, others + 1):
        if side & (side - 1) == 0:
            cost[side] = price[side]
            continue
        best = full.bit_length() + 1
        for left, right in bipartitions(side):
            candidate = max(price[side], cost[left], cost[right])
            if candidate < best:
                best = candidate
                split[side] = left, right
                if best == price[side]:
                    break
        cost[side] = best

    def reconstruct(side):
        if split[side] is None:
            return side.bit_length() - 1
        left, right = split[side]
        return reconstruct(left), reconstruct(right)

    # The displayed root just subdivides the edge at the distinguished leaf.
    return cost[others], (root_leaf, reconstruct(others))


def syndrome_table(columns):
    values = [0] * (1 << len(columns))
    for assignment in range(1, len(values)):
        low = assignment & -assignment
        values[assignment] = values[assignment ^ low] ^ columns[low.bit_length() - 1]
    return values


def glue_tree(columns, tree, widths, charge_leaf_edges):
    """Build actual syndrome domains; evaluate all inputs through local constraints."""
    full = len(widths) - 1
    syndromes = syndrome_table(columns)
    prices = edge_prices(widths, charge_leaf_edges)

    @lru_cache(None)
    def span(side):
        return {syndromes[x & side] for x in range(full + 1)}

    def compile_node(node):
        if isinstance(node, int):
            side = 1 << node
            column = columns[node]

            def value(assignment):
                return column if assignment & side else 0
        else:
            left_side, left_eval = compile_node(node[0])
            right_side, right_eval = compile_node(node[1])
            assert not left_side & right_side
            side = left_side | right_side

            def value(assignment):
                left = left_eval(assignment)
                right = right_eval(assignment)
                if left is None or right is None:
                    return None
                return left ^ right

        domain = span(side) & span(full ^ side)
        assert len(domain) == 1 << widths[side]
        # When leaf edges are free, the physical bit is used in its neighbor's
        # table. A root placed on that edge may use the same raw bit directly.
        use_domain = charge_leaf_edges or min(side.bit_count(), (full ^ side).bit_count()) > 1
        if use_domain:
            assert len(domain) <= 1 << prices[side]

        def evaluate(assignment):
            label = value(assignment)
            if use_domain and label not in domain:
                return None
            return label

        return side, evaluate

    all_leaves, evaluate = compile_node(tree)
    assert all_leaves == full
    for assignment, syndrome in enumerate(syndromes):
        assert (evaluate(assignment) == 0) == (syndrome == 0)


def rectangle_audit(columns, widths):
    """Use raw truth tables to test rectangle covers, allowing arbitrary local tables.

    The nonzero row neighborhoods yield an exact cover. One marked cell in each
    gives a fooling set: no all-one rectangle covers two, even when its row
    and column sets are arbitrary nonlinear Boolean predicates.
    """
    full = len(widths) - 1
    syndromes = syndrome_table(columns)
    # Choose the side omitting the distinguished leaf; the other orientation
    # merely transposes the acceptance matrix.
    for side in range(1, (full >> 1) + 1):
        other = full ^ side
        rows = {}
        for assignment, syndrome in enumerate(syndromes):
            if syndrome == 0:
                row, col = assignment & side, assignment & other
                rows.setdefault(row, set()).add(col)
        neighborhoods = {}
        for row, cols in rows.items():
            neighborhoods.setdefault(frozenset(cols), row)
        assert len(neighborhoods) == 1 << widths[side]
        marked = [(row, min(cols)) for cols, row in neighborhoods.items()]
        for (row1, col1), (row2, col2) in combinations(marked, 2):
            assert rows[row1].isdisjoint(rows[row2])
            assert col2 not in rows[row1] and col1 not in rows[row2]


def enumerate_tree_costs(side, prices):
    """Independent exhaustive topologies, intended for at most seven leaves."""
    if side & (side - 1) == 0:
        yield prices[side]
        return
    for left, right in bipartitions(side):
        for left_cost in enumerate_tree_costs(left, prices):
            for right_cost in enumerate_tree_costs(right, prices):
                yield max(prices[side], left_cost, right_cost)


def audit(columns, name, expected=None):
    widths = cut_widths(columns)
    results = []
    for charge_leaves in (True, False):
        width, tree = optimum_tree(widths, charge_leaves)
        glue_tree(columns, tree, widths, charge_leaves)
        if len(columns) <= 7:
            all_costs = list(enumerate_tree_costs((len(widths) - 1) >> 1,
                                                  edge_prices(widths, charge_leaves)))
            number = 1
            for factor in range(3, 2 * len(columns) - 4, 2):
                number *= factor
            assert len(all_costs) == number and min(all_costs) == width
        results.append(width)
    if len(columns) <= 7:
        rectangle_audit(columns, widths)
    if expected is not None:
        assert tuple(results) == expected, (columns, results, expected)
    print(f"{name}: all edges {results[0]}, internal edges {results[1]}; tree {tree}")


def exhaust_nine():
    """All nine-column binary matroids have lambda-width at most two.

    Duality replaces a rank above four by a rank at most four and preserves
    lambda. Delete loops and all but one column from each parallel class. The
    remaining distinct nonzero vectors embed into F_2^4 and extend to nine
    distinct vectors spanning this space. An invertible row operation maps one
    basis of that extension to the unit basis, leaving only C(11,5) choices.
    Deletion can only reduce a cut's intersection dimension after restricting
    its tree. A deleted parallel copy can be restored as a sibling using one
    bit; a zero column can be restored using no bits.
    """
    units = (1, 2, 4, 8)
    nonunits = [column for column in range(1, 16) if column not in units]
    counts = {}
    for extras in combinations(nonunits, 5):
        width, _ = optimum_tree(cut_widths((*units, *extras)))
        counts[width] = counts.get(width, 0) + 1
    assert sum(counts.values()) == 462 and max(counts) == 2
    print(f"Nine terminals, all normalized simple rank-four cases: {counts}")


if __name__ == "__main__":
    audit([0, 0, 0], "free bits", (0, 0))
    audit([1, 1, 0], "one equality", (1, 0))
    audit([1, 2, 4, 8], "zero code on four bits", (0, 0))
    audit([7, 5, 3, 1, 4, 2], "six terminals", (2, 2))
    audit([1, 2, 3, 4, 5, 6, 7], "Hamming [7,4,3]", (2, 2))
    audit([15, 14, 6, 8, 9, 11, 5, 1, 7], "nine terminals", (2, 2))
    # The binary reduced incidence matrix of K5 is a ten-terminal witness.
    k5 = [u ^ v for u, v in combinations((0, 1, 2, 4, 8), 2)]
    audit(k5, "K5 cycle code, ten terminals", (3, 3))
    audit([30, 38, 1, 59, 26, 54, 19, 27, 17, 4, 25, 32], "twelve terminals", (3, 3))

    exhaust_nine()

    rng = Random(2903)
    for n in (6, 9, 12):
        widths_found = []
        for _ in range(12):
            columns = rng.sample(range(1, 1 << (n // 2)), n)
            widths_found.append(optimum_tree(cut_widths(columns))[0])
        print(f"{n} terminals, 12 seeded samples: {sorted(set(widths_found))}; "
              f"balanced-tree ceiling {(n + 2) // 3}")
