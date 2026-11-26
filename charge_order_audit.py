"""Check distributed charge switches, physical projections and the integer coefficient."""

from itertools import product
from math import comb

from simple_permutation_successor import coloring_dimacs, predecessor, successor
from two_hamilton_paths_sat_audit import encode, switched_order

F, T, X = 0, 1, 2
channels = 6
vertices = 3 + 2 * channels
edges = [(F, T), (F, X), (T, X)]
pins = []
for k in range(channels):
    q, l = 3 + 2 * k, 4 + 2 * k
    edges.append((q, X))
    pins.append((len(edges), len(edges) + 1))
    edges.extend(((q, T), (l, F)))
enc = encode(vertices, edges)
old = enc.permutation()
positions = {v: i for i, v in enumerate(enc.blue)}
owners = {d: k for k, u, v, d, _ in enc.splitters}
switch = []
for k, (q_e, l_e) in enumerate(pins):
    (t_id,) = [i for i in enc.matching[q_e] if owners[i] == T]
    (f_id,) = [i for i in enc.matching[l_e] if owners[i] == F]
    switch.append((positions[t_id], positions[f_id]))
assert len({i for pair in switch for i in pair}) == 2 * channels
base = successor(old)
fields = []
b = (len(base) - 2) // 7
for a, z in switch:
    fields.append(
        {4 * pos + j for pos in (a, z) for j in (0, 1)}
        | {4 * ((pos - 1) % b) + j for pos in (a, z) for j in (2, 3)}
    )
assert sum(map(len, fields)) == len(set.union(*fields)) == 8 * channels
for mask in range(1 << channels):
    active = [i for i in range(channels) if mask >> i & 1]
    new = switched_order(old, switch, active)
    # Obtain new owner directly by the original blue-slot chain, then derive all red pair constraints.
    new_owner = {enc.red[new[positions[d]]]: k for d, k in owners.items()}
    actual = [frozenset((new_owner[x], new_owner[y])) for x, y in enc.matching]
    expected = list(map(frozenset, edges))
    for k in active:
        i, j = pins[k]
        expected[i] = frozenset((3 + 2 * k, F))
        expected[j] = frozenset((4 + 2 * k, T))
    assert actual == expected
    target = successor(new)
    assert predecessor(target) == tuple(new)
    assert {i for i, (x, y) in enumerate(zip(base, target)) if x != y} == set().union(
        *(fields[i] for i in active)
    )
    if mask == 0:
        baseline_dimacs = coloring_dimacs(target)
        physical = []
    if len(active) == 1:
        physical.append(
            {
                j
                for j, (x, y) in enumerate(
                    zip(baseline_dimacs, coloring_dimacs(target))
                )
                if x != y
            }
        )
assert (
    len(physical) == channels
    and all(physical)
    and sum(map(len, physical)) == len(set.union(*physical))
)
checks = 0
for row in product(range(6), repeat=3):
    B = sum(row) % 6
    verdict = B not in (1, 5)
    sums = {
        i: sum(1 for q in range(6) if ((B - a + q) % 6 not in (1, 5)) != verdict)
        for i, a in enumerate(row)
    }
    assert all(v == (2 if verdict else 4) for v in sums.values())
    for p in (2, 3):
        if verdict:
            continue
        lam = B % p
        # shift arithmetic on a connected test graph with 7 vertices, total prescribed via first three charges
        diffs = [(c - lam) % p for c in (*row, 0, 0, 0, 0)]
        assert sum(diffs) % p == 0 and lam
        shifts = [sum(diffs[: i + 1]) % p for i in range(6)]
        assert [(b - a) % p for a, b in zip([0] + shifts, shifts + [0])] == diffs
        for c, d in zip((*row, 0, 0, 0, 0), diffs):
            assert (6 // p) * (lam + d) % 6 == ((6 // p) * c) % 6
        checks += 1
print(
    len(switch),
    "switches;",
    1 << channels,
    "renderings;",
    len(base),
    "permutation entries;",
    sum(map(len, physical)),
    "disjoint edited byte positions;",
    checks,
    "field-branch charge shifts",
)

# The top coefficient calculated by direct Boolean Mobius inversion.


def finite_diff(values, j):
    return tuple(values[(i + j) % 6] - v for i, v in enumerate(values))


def accept(r):
    return int(r % 6 not in (1, 5))


start = finite_diff(finite_diff(tuple(map(accept, range(6))), 3), 2)
second = finite_diff(start, 1)
third = finite_diff(second, 1)
assert (
    start == (-1, -1, 0, 1, 1, 0)
    and second == (0, 1, 1, 0, -1, -1)
    and third == (1, 0, -1, -1, 0, 1)
)
assert finite_diff(third, 1) == start
for t in (4, 7, 13, 325):
    total = sum(
        (-1) ** (t - i - a - b) * comb(t - 2, i) * accept(i + 3 * a + 2 * b)
        for i in range(t - 1)
        for a, b in product(range(2), repeat=2)
    )
    assert total == 1
for t in (4, 7, 13):
    rows = product(range(2), repeat=t)
    total = sum(
        (-1) ** (t - sum(row)) * accept(3 * row[0] + 2 * row[1] + sum(row[2:]))
        for row in rows
    )
    assert total == 1
print(
    "Integer top coefficient +1 by exact Mobius inversion through 13 bits and binomial sums at t=325."
)
