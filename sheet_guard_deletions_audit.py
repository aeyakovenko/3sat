"""Compile signed 3-SAT into sheet layers, and solve the emitted proper 3-CNFs."""

import argparse
import subprocess
from collections import Counter, defaultdict
from itertools import combinations, product
from random import Random

MIXED = tuple(range(1, 7))
INTACT = frozenset()
CLAUSE_DELETIONS = frozenset((0b001, 0b100))
FREE_DELETIONS = frozenset((0b001, 0b101))
DUAL_DELETIONS = frozenset((0b011, 0b101))


def forbid(values, pattern):
    """The OR-row that vanishes only on the three-bit pattern."""
    return tuple(-name if pattern & (1 << (2 - port)) else name for port, name in enumerate(values))


def local_clauses(center, plus, minus, y, z, deletions):
    clauses = [forbid((center, y, z), mask) for mask in MIXED if mask not in deletions]
    clauses.extend(((plus, y, z), (-minus, -y, -z)))
    return clauses


def rail(literal):
    return 2 * (abs(literal) - 1) + 1 + (literal < 0)


def layer_jobs(variables, clauses):
    jobs = [(rail(x), rail(-x), rail(-x), INTACT) for x in range(1, variables + 1)]
    for a, b, c in clauses:
        assert all(1 <= abs(x) <= variables for x in (a, b, c))
        assert len({abs(a), abs(b), abs(c)}) == 3
        jobs.append((rail(-a), rail(b), rail(-c), CLAUSE_DELETIONS))
    return schedule(jobs)


def schedule(jobs):
    layers = []
    for job in jobs:
        used = set(job[:3])
        for occupied, jobs_in_layer in layers:
            if used.isdisjoint(occupied):
                break
        else:
            occupied, jobs_in_layer = set(), []
            layers.append((occupied, jobs_in_layer))
        occupied.update(used)
        jobs_in_layer.append(job)
    return [jobs_in_layer for _, jobs_in_layer in layers]


def compile_sheets(variables, clauses):
    sheets = 2 * variables
    layers = layer_jobs(variables, clauses)
    degree = max(Counter(abs(x) for clause in clauses for x in clause).values(), default=0)
    assert len(layers) <= 3 * degree + 1
    return emit(sheets, layers)


def compile_bipartite(variables, clauses):
    # Logical X and its negation proxy have distinct left and right rails.
    side_size = 4 * variables

    def left(lit):
        return rail(lit)

    def right(lit):
        return side_size + rail(lit)

    jobs = []
    for x in range(1, variables + 1):
        for symbol in (x, -x):
            jobs.append((left(symbol), right(symbol), right(symbol), INTACT))
        anchor = 2 * variables + 2 * x - 1
        one, zero = side_size + anchor, side_size + anchor + 1
        jobs.extend([
            (anchor, anchor, one, INTACT),
            (anchor + 1, zero, anchor + 1, INTACT),
            (left(x), one, right(-x), DUAL_DELETIONS),
            (left(x), right(-x), zero, CLAUSE_DELETIONS),
        ])
    for a, b, c in clauses:
        assert all(1 <= abs(x) <= variables for x in (a, b, c))
        assert len({abs(a), abs(b), abs(c)}) == 3
        jobs.append((left(-a), right(-b), right(c), CLAUSE_DELETIONS))
    for center, a, b, _ in jobs:
        assert center <= side_size
        assert all(endpoint == center or endpoint > side_size for endpoint in (a, b))
    layers = schedule(jobs)
    degree = max(Counter(abs(x) for clause in clauses for x in clause).values(), default=0)
    assert len(layers) <= 3 * degree + 7
    return emit(2 * side_size, layers, side_size)


def compile_two_fixed(variables, clauses):
    """Only two positive remote entries are fixed, at opposite-side anchor centers."""
    side_size = 4 * variables

    def right(literal):
        return side_size + rail(literal)

    def constant(symbol, selector):
        return side_size + 2 * variables + 2 * (symbol - 1) + 1 + selector

    left_pin = 2 * variables + 1
    right_pin = constant(1, 1)
    pin_layer = [
        (left_pin, left_pin, constant(1, 0), INTACT),
        (right_pin, right_pin, left_pin + 1, INTACT),
    ]
    jobs = []
    for x in range(1, variables + 1):
        for symbol in (x, -x):
            jobs.append((rail(symbol), right(symbol), right(symbol), INTACT))
        jobs.extend([
            (rail(x), constant(x, 0), right(-x), DUAL_DELETIONS),
            (rail(x), right(-x), constant(x, 1), CLAUSE_DELETIONS),
        ])
        if x < variables:
            for selector in (0, 1):
                relay = 2 * variables + 2 * x + 1 + selector
                for neighbor in (x, x + 1):
                    endpoint = constant(neighbor, selector)
                    jobs.append((relay, endpoint, endpoint, INTACT))
    for a, b, c in clauses:
        assert all(1 <= abs(x) <= variables for x in (a, b, c))
        assert len({abs(a), abs(b), abs(c)}) == 3
        jobs.append((rail(-a), right(-b), right(c), CLAUSE_DELETIONS))
    layers = [pin_layer, *schedule(jobs)]
    degree = max(Counter(abs(x) for clause in clauses for x in clause).values(), default=0)
    assert len(layers) <= 3 * degree + 8
    sheets = 2 * side_size
    fresh, result = emit(sheets, layers, side_size, complete=True)

    inspect_anchors(sheets, len(layers), 0, left_pin, right_pin, fresh, result)
    return fresh, result


def inspect_anchors(sheets, num_layers, pin_layer_index, left_pin, right_pin, fresh, result):
    side_size = sheets // 2
    # Recover the two remote entries per guard directly from the actual emitted
    # clauses. The six local guards have mixed signs and never enter this census.
    remote = Counter()
    fixed = Counter()
    anchor_rows = {}
    for x, y, z in result:
        if (x > 0) == (y > 0) == (z > 0):
            cell = (abs(y) - sheets - 1) // 2
            layer, index = divmod(cell, sheets)
            center = index + 1
            positive = x > 0
            remote[layer, positive] += 1
            if abs(x) == center:
                fixed[layer, positive, center] += 1
                anchor_rows[center] = (x, y, z)
            else:
                assert (abs(x) <= side_size) != (center <= side_size)
    assert len(remote) == 2 * num_layers and set(remote.values()) == {sheets}
    assert fixed == Counter({(pin_layer_index, True, left_pin): 1, (pin_layer_index, True, right_pin): 1})
    coloring = 0
    for variable in range(1, fresh + 1):
        sheet = variable if variable <= sheets else 1 + ((variable - sheets - 1) // 2) % sheets
        if sheet <= side_size:
            coloring |= 1 << (variable - 1)
    complement = ((1 << fresh) - 1) ^ coloring
    for bits, failed_at in ((coloring, right_pin), (complement, left_pin)):
        defects = [row for row in result if not satisfied([row], bits)]
        assert defects == [anchor_rows[failed_at]]
        switched = [
            (other, *anchor_rows[center][1:])
            for center, other in ((left_pin, right_pin), (right_pin, left_pin))
        ]
        assert satisfied(switched, bits)
    return anchor_rows


def compile_two_layers(variables, clauses):
    """One equality cycle per logical symbol, then disjoint four-sheet clause boxes."""
    groups = defaultdict(lambda: ([], []))
    next_occurrence = 0

    def occurrence(symbol, side):
        nonlocal next_occurrence
        token = next_occurrence
        next_occurrence += 1
        groups[symbol][side].append(token)
        return token

    left, right = 0, 1
    one, zero = 2 * variables + 1, 2 * variables + 2
    boxes = []

    def box(center, a, b, side):
        # A new private logical symbol has one used occurrence and one
        # complementary dummy in the equality layer.
        private = zero + len(boxes) + 1
        boxes.append((
            occurrence(center, side), occurrence(a, 1 - side), occurrence(b, 1 - side),
            occurrence(private, side),
        ))

    for x in range(1, variables + 1):
        box(rail(x), rail(-x), one, right)
        box(rail(x), rail(-x), zero, left)
    for a, b, c in clauses:
        assert all(1 <= abs(x) <= variables for x in (a, b, c))
        assert len({abs(a), abs(b), abs(c)}) == 3
        box(rail(-a), rail(-b), rail(c), left)

    pins = (
        occurrence(one, left), occurrence(zero, left),
        occurrence(one, right), occurrence(zero, right),
    )
    side_size = sum(max(len(l), len(r)) for l, r in groups.values())
    sheets = 2 * side_size
    names = range(1, sheets + 1)
    assert sheets <= 2 * (4 * (2 * variables + len(clauses)) + 4)
    first_plus, first_minus = {}, {}
    label = {}
    offset = 0
    for left_uses, right_uses in groups.values():
        count = max(len(left_uses), len(right_uses))
        for j in range(count):
            l = offset + j + 1
            r = side_size + l
            next_r = side_size + offset + ((j + 1) % count) + 1
            first_plus[l], first_plus[r] = r, l
            first_minus[l], first_minus[next_r] = next_r, l
            if j < len(left_uses):
                label[left_uses[j]] = l
            if j < len(right_uses):
                label[right_uses[j]] = r
        offset += count
    assert offset == side_size and len(label) == next_occurrence

    second_plus, second_minus = {}, {}

    def match(perm, a, b):
        assert a not in perm and b not in perm
        perm[a], perm[b] = b, a

    for tokens in boxes:
        c, a, b, d = (label[token] for token in tokens)
        match(second_plus, c, a)
        match(second_plus, d, b)
        match(second_minus, c, b)
        match(second_minus, d, a)
    h, other_h, r_one, r_zero = (label[token] for token in pins)
    match(second_plus, h, h)
    match(second_plus, r_zero, r_zero)
    match(second_plus, other_h, r_one)
    match(second_minus, h, r_one)
    match(second_minus, r_zero, other_h)
    free_left = [x for x in names if x <= side_size and x not in second_plus]
    free_right = [x for x in names if x > side_size and x not in second_plus]
    assert set(second_plus) == set(second_minus) and len(free_left) == len(free_right)
    for a, b in zip(free_left, free_right):
        match(second_plus, a, b)
        match(second_minus, a, b)

    result = []
    fresh = sheets
    for layer, (plus, minus) in enumerate(((first_plus, first_minus), (second_plus, second_minus))):
        for perm in (plus, minus):
            assert set(perm) == set(names) == set(perm.values())
            assert all(perm[perm[x]] == x for x in names)
        for x in names:
            guard = INTACT if layer == 0 or x in (h, r_zero) else CLAUSE_DELETIONS
            result.extend(local_clauses(x, plus[x], minus[x], fresh + 1, fresh + 2, guard))
            fresh += 2
    assert fresh == 5 * sheets and len(result) == 14 * sheets + 4
    assert all(len({abs(x) for x in row}) == 3 for row in result)
    # Recover the actual local guard masks, independently of which mask emit
    # was instructed to use.
    present = defaultdict(set)
    for a, y, z in result:
        pattern = (int(a < 0) << 2) | (int(y < 0) << 1) | int(z < 0)
        if pattern in MIXED:
            cell = (abs(y) - sheets - 1) // 2
            assert abs(a) == 1 + (cell % sheets)
            present[cell].add(pattern)
    assert len(present) == 2 * sheets
    for cell, actual in present.items():
        full = cell < sheets or 1 + cell % sheets in (h, r_zero)
        assert set(MIXED) - actual == (INTACT if full else CLAUSE_DELETIONS)
    anchors = inspect_anchors(sheets, 2, 1, h, r_zero, fresh, result)
    selectors = [(i, x) for i, row in enumerate(result) for x in (h, r_zero) if row == anchors[x]]
    assert len(selectors) == 2
    return sheets, fresh, result, selectors


def check_selector_cube(sheets, variables, emitted, selectors, original_sat, executable):
    # Give the two anchors dense decimal names 10 and 11; each identifier
    # switch then changes one actual ASCII bit. Other names are permuted.
    left, right = (x for _, x in selectors)
    remap = {left: 10, right: 11}
    ordinary = (v for v in range(1, variables + 1) if v not in (10, 11))
    for v in range(1, variables + 1):
        if v not in remap:
            remap[v] = next(ordinary)
    signed = {**remap, **{-k: -v for k, v in remap.items()}}
    files = []
    for a, b in product(range(2), repeat=2):
        clauses = list(emitted)
        for (index, _), switched, other in zip(selectors, (a, b), (right, left)):
            if switched:
                clauses[index] = (other, *clauses[index][1:])
        assert solve_emitted(sheets, clauses) == bool(original_sat or a or b)
        actual = [tuple(signed[lit] for lit in row) for row in clauses]
        data = serialize_dimacs(variables, actual)
        if executable:
            assert solve_dimacs(executable, data) == bool(original_sat or a or b)
        files.append(data)
    base = files[0]
    for corner, expected in zip(files, (0, 1, 1, 2)):
        assert len(corner) == len(base)
        assert sum((left ^ right).bit_count() for left, right in zip(corner, base)) == expected


def emit(sheets, layers, side_size=None, complete=False):
    names = list(range(1, sheets + 1))
    fresh = sheets
    result = []
    for jobs in layers:
        plus = {x: x for x in names}
        minus = plus.copy()
        guards = {x: FREE_DELETIONS for x in names}
        for center, a, b, deletions in jobs:
            assert plus[center] == center and plus[a] == a
            assert minus[center] == center and minus[b] == b
            plus[center], plus[a] = a, center
            minus[center], minus[b] = b, center
            guards[center] = deletions
        for port, perm in enumerate((plus, minus), 1):
            if complete:
                assert side_size is not None
                prescribed_fixed = {job[0] for job in jobs if job[port] == job[0]}
                available = [x for x in names if x not in prescribed_fixed and perm[x] == x]
                left = [x for x in available if x <= side_size]
                right = [x for x in available if x > side_size]
                assert len(left) == len(right)
                for a, b in zip(left, right):
                    perm[a], perm[b] = b, a
                assert {x for x in names if perm[x] == x} == prescribed_fixed
                assert all(perm[job[0]] == job[port] for job in jobs)
            assert set(perm.values()) == set(names)
            assert all(perm[perm[x]] == x for x in names)
            if side_size is not None:
                assert all(perm[x] == x or (x <= side_size) != (perm[x] <= side_size) for x in names)
        for sheet in names:
            result.extend(local_clauses(sheet, plus[sheet], minus[sheet], fresh + 1, fresh + 2, guards[sheet]))
            fresh += 2
    assert all(len({abs(x) for x in clause}) == 3 for clause in result)
    return fresh, result


def satisfied(clauses, bits):
    return all(any(bool(bits & (1 << (abs(lit) - 1))) == (lit > 0) for lit in row) for row in clauses)


def brute_sat(variables, clauses):
    return any(satisfied(clauses, bits) for bits in range(1 << variables))


def eliminate(clauses, variable):
    """Exact Davis-Putnam elimination on a set of ordinary clauses."""
    positive = [c - {variable} for c in clauses if variable in c]
    negative = [c - {-variable} for c in clauses if -variable in c]
    retained = {c for c in clauses if variable not in c and -variable not in c}
    for p, n in product(positive, negative):
        merged = p | n
        if not any(-lit in merged for lit in merged):
            retained.add(merged)
    return retained


def solve_residual(clauses):
    """DPLL with unit propagation on the rail CNF produced by resolution."""
    def restrict(rows, true_literal):
        return {row - {-true_literal} for row in rows if true_literal not in row}

    while clauses:
        shortest = min(clauses, key=len)
        if not shortest:
            return False
        lit = next(iter(shortest))
        if len(shortest) > 1:
            return solve_residual(restrict(clauses, lit)) or solve_residual(restrict(clauses, -lit))
        clauses = restrict(clauses, lit)
    return True


def solve_emitted(rail_count, clauses):
    groups = defaultdict(set)
    for clause in clauses:
        private = tuple(sorted(abs(lit) for lit in clause if abs(lit) > rail_count))
        assert len(private) == 2
        groups[private].add(frozenset(clause))
    assert sum(len(pair) for pair in groups) == len({var for pair in groups for var in pair})
    residual = set()
    for pair, group in groups.items():
        residual.update(eliminate(eliminate(group, pair[0]), pair[1]))
    assert all(abs(lit) <= rail_count for row in residual for lit in row)
    return solve_residual(residual)


def check_signatures():
    failed = []
    all_relations = set()
    for flags in product((False, True), repeat=len(MIXED)):
        deletions = frozenset(k for k, erased in zip(MIXED, flags) if erased)
        clauses = local_clauses(1, 2, 3, 4, 5, deletions)
        relation = set()
        for c, a, b in product(range(2), repeat=3):
            public = c | (a << 1) | (b << 2)
            accept = any(satisfied(clauses, public | (private << 3)) for private in range(4))
            mismatched_pair = bool(deletions & ({5, 6} if c else {1, 2}))
            alternate = 4 in deletions if c else 3 in deletions
            expected = mismatched_pair or (not b if c else bool(a)) or (alternate and (a or not b))
            assert accept == expected
            if deletions == INTACT:
                assert accept == (not b if c else bool(a))
            if deletions == CLAUSE_DELETIONS:
                assert accept == (not c or a or not b)
            if deletions == DUAL_DELETIONS:
                assert accept == (c or a or not b)
            if deletions == FREE_DELETIONS:
                assert accept
            if accept:
                relation.add(public)
        if any(((x & y) | (y & z) | (x & z)) not in relation for x, y, z in combinations(relation, 3)):
            failed.append(tuple(sorted(deletions)))
        all_relations.add(frozenset(relation))
    assert len(all_relations) == 9 and len(failed) == 12
    assert tuple(sorted(CLAUSE_DELETIONS)) in failed
    assert tuple(sorted(DUAL_DELETIONS)) in failed
    print(f"64 deletion masks, {len(all_relations)} projected relations, {len(failed)} majority failures")
    return failed


def serialize_dimacs(variables, clauses):
    body = [f"p cnf {variables} {len(clauses)}"]
    body.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    return ("\n".join(body) + "\n").encode("ascii")


def solve_dimacs(executable, data):
    run = subprocess.run([executable], input=data, capture_output=True, check=False)
    assert run.returncode in (10, 20), (run.returncode, run.stderr)
    return run.returncode == 10


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", help="also cross-check every compiled CNF with a DIMACS solver reading stdin")
    args = parser.parse_args()
    check_signatures()
    triple = list(product((-1, 1), (-2, 2), (-3, 3)))
    collection = [(3, list(rows)) for count in range(9) for rows in combinations(triple, count)]
    rng = Random(246197)
    for _ in range(32):
        n = rng.randrange(4, 7)
        rows = [
            tuple(v if rng.randrange(2) else -v for v in rng.sample(range(1, n + 1), 3))
            for _ in range(2 * n)
        ]
        if rng.randrange(2):
            rows.extend(triple)
        collection.append((n, rows))
    counts = Counter()
    for n, rows in collection:
        expected = brute_sat(n, rows)
        for compiler, rail_count in (
            (compile_sheets, 2 * n),
            (compile_bipartite, 8 * n),
            (compile_two_fixed, 8 * n),
        ):
            variables, emitted = compiler(n, rows)
            assert solve_emitted(rail_count, emitted) == expected
            if args.solver:
                assert solve_dimacs(args.solver, serialize_dimacs(variables, emitted)) == expected
        sheets, variables, emitted, selectors = compile_two_layers(n, rows)
        check_selector_cube(sheets, variables, emitted, selectors, expected, args.solver)
        counts[expected] += 1
    assert counts == {False: 15, True: 273}
    print(f"three sheet compilers on {len(collection)} formulas each, {counts[True]} SAT and {counts[False]} UNSAT")
    print("two positive fixed entries and a different one-clause defect on each complementary assignment")
    print(f"fourth compiler: {len(collection)} two-layer CNFs, only I/P guards, four real one-bit cube corners each")


if __name__ == "__main__":
    main()
