"""Exhaust literal-port permutations before optimizing over all sheet assignments."""

from functools import cache
from itertools import combinations, permutations, product


def transposition_cost(p):
    unseen = set(range(len(p)))
    cycles = 0
    while unseen:
        i = next(iter(unseen))
        cycles += 1
        while i in unseen:
            unseen.remove(i)
            i = p[i]
    return len(p) - cycles


@cache
def or_repair_table(d):
    """Minimum permutation cost to satisfy all rows for three truth columns."""
    full = (1 << d) - 1
    choices = []
    for mask in range(full + 1):
        best = {}
        for p in permutations(range(d)):
            reordered = sum(((mask >> p[j]) & 1) << j for j in range(d))
            cost = transposition_cost(p)
            best[reordered] = min(best.get(reordered, 3 * d + 1), cost)
        choices.append(tuple(best.items()))
    return {
        cols: min(
            (sum(opt[1] for opt in options)
             for options in product(*(choices[col] for col in cols))
             if options[0][0] | options[1][0] | options[2][0] == full),
            default=3 * d + 1,
        )
        for cols in product(range(full + 1), repeat=3)
    }


def base_minimum(formula, variables):
    scores = [
        sum(len({((a >> var) & 1) ^ sign for var, sign in clause}) == 1
            for clause in formula)
        for a in range(1 << variables)
    ]
    return min(scores), scores.index(min(scores))


def minimum_cover_distance(formula, variables, d):
    full = (1 << d) - 1
    table = or_repair_table(d)
    best = d * len(formula) + 1
    for xs in product(range(full + 1), repeat=variables):
        cost = 0
        for clause in formula:
            cols = tuple(xs[v] ^ (full if sign else 0) for v, sign in clause)
            first = table[cols]
            second = table[tuple(c ^ full for c in cols)]
            if max(first, second) > 3 * d:
                break
            cost += first + second
        else:
            best = min(best, cost)
    return best


def paired_formula(sign_vectors):
    return [tuple(enumerate(signs)) for signs in sign_vectors]


def block_switches(formula, assignment, d):
    """Return explicit raw sheet-to-variable rows and pairwise disjoint switches."""
    base = [tuple((v, s ^ polarity) for v, s in clause)
            for clause in formula for polarity in range(2)]
    rows = [[(3 * sheet + v, s) for v, s in clause]
            for clause in base for sheet in range(d)]
    switches = []
    blocks = ([3] if d % 2 else []) + [2] * ((d - 3 * (d % 2)) // 2)
    start = 0
    for size in blocks:
        for i, clause in enumerate(base):
            truth = [((assignment >> v) & 1) ^ sign for v, sign in clause]
            if any(truth) and not all(truth):
                continue
            first = i * d + start
            if all(truth):
                switches.append((first, first + 1, 0))
            else:
                switches.append((first + 1, first, 0))
            if size == 3 and not any(truth):
                switches.append((first + 1, first + 2, 1))
        start += size
    endpoints = [(r, k) for a, b, k in switches for r in (a, b)]
    assert len(set(endpoints)) == len(endpoints)
    return rows, switches


def raw_minimum(rows, d):
    # Pair/triple groups are independent formula components even after switches.
    groups = []
    sizes = ([3] if d % 2 else []) + [2] * ((d - 3 * (d % 2)) // 2)
    start = 0
    for size in sizes:
        lo, hi = 3 * start, 3 * (start + size)
        groups.append([
            [(v - lo, s) for v, s in row] for row in rows if lo <= row[0][0] < hi
        ])
        assert all(0 <= v < 3 * size for row in groups[-1] for v, _ in row)
        start += size
    return sum(group_minimum(tuple(map(tuple, rows_in_group)), size)
               for rows_in_group, size in zip(groups, sizes))


@cache
def group_minimum(group, size):
    return min(
        sum(not any(((a >> v) & 1) ^ s for v, s in row) for row in group)
        for a in range(1 << (3 * size))
    )


def complete_bipartite_face():
    """Test all quotient assignments of the expanding construction on K4,4."""
    all_assignments = (1 << 256) - 1
    allowed = []
    edges = set()
    for layer in range(4):
        sign = layer % 2
        for i in range(4):
            j = 4 + (i + layer) % 4
            edges.add((i, j))
            off = on = 0
            for a in range(256):
                left, right = ((a >> i) & 1) ^ sign, ((a >> j) & 1) ^ sign
                if left and right:
                    off |= 1 << a
                if left or right:
                    on |= 1 << a
            allowed.append((off, on))
    assert len(edges) == 16
    states = [all_assignments]
    for off, on in allowed:
        states = [previous & condition for previous in states for condition in (off, on)]
    assert not any(states[:-1]) and states[-1]
    return len(states)


def main():
    signs = [(0, *tail) for tail in product(range(2), repeat=2)]
    base_cases = [paired_formula(subset) for i in range(5) for subset in combinations(signs, i)]
    for selected in (base_cases[-1], [*base_cases[-1], *base_cases[-1]]):
        base_cases.append([*selected, ((0, 0), (0, 0), (1, 1))])
    more = [
        tuple(zip(variables, sign_tuple))
        for variables in combinations(range(4), 3) for sign_tuple in signs
    ]
    cases = [(formula, 3) for formula in base_cases] + [(more, 4), (more[::3], 4)]
    for d in (2, 3):
        for formula, variables in cases:
            u, _ = base_minimum(formula, variables)
            assert minimum_cover_distance(formula, variables, d) == d * u
    formula = paired_formula(signs)
    u, a = base_minimum(formula, 3)
    assert u == 1
    subcubes = 0
    for d in range(2, 9):
        initial, switches = block_switches(formula, a, d)
        assert len(switches) == d
        for subset in range(1 << d):
            rows = [row.copy() for row in initial]
            for i, (p, q, k) in enumerate(switches):
                if (subset >> i) & 1:
                    rows[p][k], rows[q][k] = rows[q][k], rows[p][k]
            assert raw_minimum(rows, d) == d - subset.bit_count()
            subcubes += 1
    print(f"{2 * len(cases)} exact minima over unrestricted cover permutations and sheet assignments")
    print(f"{subcubes} actual lifted formulas checked for optimal residual defect")
    print(f"{complete_bipartite_face()} selector verdicts checked for K4,4")


if __name__ == "__main__":
    main()
