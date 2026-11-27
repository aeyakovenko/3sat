"""Check the singleton cut algorithm and the four-sheet relay reduction on ordinary CNFs."""

import argparse
from collections import Counter
from itertools import combinations, permutations, product
from random import Random

from sheet_guard_deletions_audit import (
    brute_sat,
    compile_two_layers,
    selector_renaming,
    serialize_dimacs,
    solve_dimacs,
)


def inverse(permutation):
    result = [0] * len(permutation)
    for i, target in enumerate(permutation):
        result[target] = i
    return result


def singleton_cut(positive, negative):
    pin = positive[0]
    zeros = {pin, inverse(negative)[pin]}
    ones = {0, negative[0]}
    if ones & zeros:
        return False
    start = negative[0]
    vertex = start
    gap = []
    while vertex not in zeros:
        gap.append(vertex)
        vertex = negative[vertex]
        if vertex == start:
            return True
    back = inverse(positive)
    for candidate in gap:
        other = back[negative[candidate]]
        tails = {candidate, other}
        heads = {negative[candidate], negative[other]}
        if not (tails & heads or tails & zeros or heads & ones):
            return True
    return False


def projected_truth_mask(positive, negative, bits, all_states):
    """Intersect raw I/P constraints at the two physical ends of each port."""
    n = len(positive)
    pos_inverse = inverse(positive)
    neg_inverse = inverse(negative)
    pin = positive[0]
    states = all_states
    for i in range(n):
        # Physical left bit = x_i, physical right bit = NOT x_i.
        x, b = bits[i], all_states ^ bits[negative[i]]
        if i == 0:
            states &= x & (all_states ^ b)
        else:
            a = all_states ^ bits[positive[i]]
            states &= (all_states ^ x) | a | (all_states ^ b)
        x, b = all_states ^ bits[i], bits[neg_inverse[i]]
        if i == pin:
            states &= x & (all_states ^ b)
        else:
            a = bits[pos_inverse[i]]
            states &= (all_states ^ x) | a | (all_states ^ b)
    return states


def census(size):
    layouts = list(permutations(range(size)))
    involutions = [p for p in layouts if all(p[p[i]] == i for i in range(size))]
    bits = [sum(1 << state for state in range(1 << size) if state >> i & 1) for i in range(size)]
    universe = (1 << (1 << size)) - 1
    yes = 0
    for positive in layouts:
        for relative in involutions:
            negative = [positive[i] for i in relative]
            expected = bool(projected_truth_mask(positive, negative, bits, universe))
            assert singleton_cut(positive, negative) == expected
            yes += expected
    total = len(layouts) * len(involutions)
    return yes, total - yes


def check_layout(sheets, rows, selectors):
    ports = [[{}, {}], [{}, {}]]
    for x, y, z in rows:
        if (x > 0) == (y > 0) == (z > 0):
            layer, index = divmod((abs(y) - sheets - 1) // 2, sheets)
            ports[layer][x < 0][index + 1] = abs(x)
    h, r = [name for _, name in selectors]
    assert ports[1][0][h] == h and ports[1][0][r] == r
    ports[1][0][h], ports[1][0][r] = r, h
    half = sheets // 2
    for pos, neg in ports:
        for matching in (pos, neg):
            assert len(matching) == sheets
            assert all(matching[partner] == x and (x <= half) != (partner <= half)
                       for x, partner in matching.items())
        relative = {x: pos[neg[x]] for x in range(1, half + 1)}
        assert all(relative[y] == x for x, y in relative.items())
        assert all(x != y for x, y in relative.items())


def verify_compiler(solver):
    signed_clauses = list(product((-1, 1), (-2, 2), (-3, 3)))
    counts = Counter()
    sources = []
    for size in range(9):
        for source in combinations(signed_clauses, size):
            sources.append((3, source))
    # Forbid every leaf of a depth-three decision tree on seven different
    # variables. Deleting any one leaf gives its missing satisfying branch.
    tree = []
    for branch in product((0, 1), repeat=3):
        node = 1
        row = []
        for value in branch:
            row.append(-node if value else node)
            node = 2 * node + value
        tree.append(tuple(row))
    assert not brute_sat(7, tree)
    sources.append((7, tree))
    for i in range(8):
        changed = tree[:i] + tree[i + 1:]
        assert brute_sat(7, changed)
        sources.append((7, changed))
    rng = Random(381269)
    for _ in range(31):
        n = rng.randrange(4, 9)
        random_rows = [tuple(v if rng.randrange(2) else -v for v in rng.sample(range(1, n + 1), 3))
                       for _ in range(rng.randrange(3 * n, 8 * n))]
        sources.append((n, random_rows))
    for n, source in sources:
        expected = brute_sat(n, source)
        sheets, fresh, rows, selectors = compile_two_layers(n, source, double_relays=True)
        check_layout(sheets, rows, selectors)
        signed = selector_renaming(fresh, selectors)
        base = b''
        for mask in range(4):
            actual = rows.copy()
            for j, (index, _) in enumerate(selectors):
                if mask >> j & 1:
                    actual[index] = (selectors[1 - j][1], *actual[index][1:])
            data = serialize_dimacs(fresh, [tuple(signed[lit] for lit in row) for row in actual])
            if mask == 0:
                base = data
            assert len(data) == len(base)
            assert sum((x ^ y).bit_count() for x, y in zip(base, data)) == mask.bit_count()
            verdict = solve_dimacs(solver, data)
            assert verdict == (expected or mask != 0)
            counts[verdict] += 1
    return len(sources), counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='also verify the doubled-relay compiler with a DIMACS solver')
    args = parser.parse_args()
    for n in range(1, 7):
        print(f'{n} singleton relays per side: {census(n)} (SAT, UNSAT)', flush=True)
    if args.solver:
        num_sources, counts = verify_compiler(args.solver)
        print(f'CaDiCaL on the four doubled-relay corners of {num_sources} sources: {counts}')
