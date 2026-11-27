"""Parsimoniously extend proper DIMACS 3-CNF to avoid DFAO model weights.

Run without arguments for the audit. With --states S read a source file on
stdin and write its extended formula on stdout. Source models assign only
occurring names. Target variables are consecutive and all occur. Every
target model has the same weight, absent from the truth tables of all DFAOs
with at most S states on the full cube and from all affine truth tables.
The weight is consequently forbidden under every ordering of the names.
"""

import argparse
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, permutations, product
from math import factorial
from random import Random
import sys

from cnf_width_dictionary_audit import canonical, dpll_count, name, read_dimacs


def canonical_transitions(states):
    """Label reachable states by first discovery in a 0-before-1 BFS."""
    entries = [0] * (2 * states)

    def fill(position, reached):
        if position == len(entries):
            if reached == states:
                yield tuple(entries)
            return
        if position // 2 >= reached or states - reached > len(entries) - position:
            return
        for dest in range(min(reached + 1, states)):
            entries[position] = dest
            yield from fill(position + 1, max(reached, dest + 1))

    yield from fill(0, 1)


@lru_cache(None)
def automaton_weights(state_bound, digits):
    """Count all length-digits paths to each state, then all output subsets."""
    weights = set()
    for states in range(1, state_bound + 1):
        for transitions in canonical_transitions(states):
            population = [1] + [0] * (states - 1)
            for _ in range(digits):
                following = [0] * states
                for src, count in enumerate(population):
                    following[transitions[2 * src]] += count
                    following[transitions[2 * src + 1]] += count
                population = following
            possible = {0}
            for count in population:
                possible |= {total + count for total in possible}
            weights.update(possible)
    return frozenset(weights)


def farthest_weight(total, low, high, forbidden):
    """Return the smallest maximizer and its distance to the full spectrum."""
    marked = bytearray(total + 1)
    for weight in forbidden:
        marked[weight] = 1
    if not (0 <= low <= high <= total and marked[0] and marked[total]):
        raise ValueError("require a feasible interval and forbidden endpoints")
    best, margin = low, -1
    left = 0
    for right in range(1, total + 1):
        if not marked[right]:
            continue
        start, stop = max(left, low), min(right, high)
        if start <= stop:
            middle = min(stop, max(start, (left + right) // 2))
            distance = min(middle - left, right - middle)
            if distance > margin:
                best, margin = middle, distance
        left = right
    return best, margin


def choose_weight(variables, state_bound, min_variables=0):
    if state_bound < 1:
        raise ValueError("the state bound must be positive")
    if min_variables < 0:
        raise ValueError("the minimum variable count must be nonnegative")
    # Leave a constant fraction of all positions available to vary the weight.
    digits = (max(3 * variables + 3, min_variables) - 1).bit_length()
    # If K = sum(2^q q^(2q), q=1..state_bound), there are at most K+3
    # forbidden weights. Every V >= 2*variables+K+6 leaves K+4 candidates.
    while True:
        total = 1 << digits
        free = total - 2 * variables - 3
        forbidden = automaton_weights(state_bound, digits) | {0, total // 2, total}
        weight, margin = farthest_weight(total, variables, variables + free, forbidden)
        if margin:
            return total, weight, margin
        digits += 1


@dataclass(frozen=True)
class Extension:
    data: bytes
    original_names: tuple
    total: int
    weight: int
    margin: int


def ordered_names(clauses):
    # For normalized decimals, breadth-first depth gives numeric length.
    # Sorted children of the ten-symbol alphabet give lexicographic ties.
    edges = [{}]
    terminal = {}
    for clause in clauses:
        for lit in clause:
            key = name(lit)
            node = 0
            for digit in key:
                if digit not in edges[node]:
                    edges[node][digit] = len(edges)
                    edges.append({})
                node = edges[node][digit]
            terminal[node] = key
    queue = [0]
    names = []
    for node in queue:
        if node in terminal:
            names.append(terminal[node])
        queue.extend(edges[node][digit] for digit in sorted(edges[node]))
    return tuple(names)


def extend(source, state_bound, min_variables=0):
    original = [tuple(map(canonical, clause)) for clause in read_dimacs(source)]
    if any(len(clause) != 3 or len({name(lit) for lit in clause}) != 3
           for clause in original):
        raise ValueError("each source clause must contain three distinct variables")
    names = ordered_names(original)
    v = len(names)
    total, weight, margin = choose_weight(v, state_bound, min_variables)
    ranks = {key: i for i, key in enumerate(names, 1)}
    clauses = [tuple(-ranks[name(lit)] if lit.startswith(b"-") else ranks[lit]
                     for lit in clause) for clause in original]
    a, b, c = range(2 * v + 1, 2 * v + 4)
    for pattern in range(1, 8):
        clauses.append(tuple(-var if pattern >> j & 1 else var
                             for j, var in enumerate((a, b, c))))
    for x in range(1, v + 1):
        clauses.extend(((x, v + x, a), (-x, -(v + x), a)))
    for z in range(c + 1, total + 1):
        clauses.append((z if z <= c + weight - v else -z, a, b))
    body = [f"p cnf {total} {len(clauses)}"]
    body.extend(f"{x} {y} {z} 0" for x, y, z in clauses)
    return Extension(("\n".join(body) + "\n").encode(), names, total, weight, margin)


@lru_cache(None)
def direct_weights(state_bound, digits):
    """Independent oracle: all labelled tables, outputs, and actual words."""
    weights = set()
    words = tuple(product((0, 1), repeat=digits))
    for states in range(1, state_bound + 1):
        for table in product(range(states), repeat=2 * states):
            endpoints = []
            for word in words:
                state = 0
                for bit in word:
                    state = table[2 * state + bit]
                endpoints.append(state)
            for flags in product((0, 1), repeat=states):
                weights.add(sum(flags[state] for state in endpoints))
    return weights


def unit_propagate(clauses, pins):
    assigned = dict(pins)
    while True:
        before = len(assigned)
        for clause in clauses:
            if any(assigned[abs(x)] == (x > 0) for x in clause if abs(x) in assigned):
                continue
            remaining = [x for x in clause if abs(x) not in assigned]
            if not remaining:
                return None
            if len(remaining) == 1:
                lit = remaining[0]
                assigned[abs(lit)] = lit > 0
        if len(assigned) == before:
            return assigned


def audit_source(source, states, min_variables=0):
    ext = extend(source, states, min_variables)
    source_clauses = [tuple(map(canonical, row)) for row in read_dimacs(source)]
    target = read_dimacs(ext.data)
    integers = [tuple(map(int, row)) for row in target]
    named_vars = {name(lit) for row in target for lit in row}
    assert all(len(row) == len({abs(x) for x in row}) == 3 for row in integers)
    assert {int(v) for v in named_vars} == set(range(1, ext.total + 1))
    v = len(ext.original_names)
    assert ext.total >= max(3 * v + 3, min_variables)
    forbidden = direct_weights(states, ext.total.bit_length() - 1) | {0, ext.total // 2, ext.total}
    distances = [min(abs(x - f) for f in forbidden)
                 for x in range(v, ext.total - v - 2)]
    assert ext.margin == max(distances) > 0 and ext.weight == v + distances.index(ext.margin)
    assert len(target) == len(source_clauses) + 2 * v + 7 + ext.total - 2 * v - 3
    anchors = list(range(2 * v + 1, 2 * v + 4))
    for bits in product((False, True), repeat=3):
        if any(bits):
            assert unit_propagate(integers, dict(zip(anchors, bits))) is None
    assert unit_propagate(integers, {}) == {}
    fixed_anchors = dict.fromkeys(anchors, False)
    models = 0
    for row in product((False, True), repeat=v):
        assignment = dict(zip(ext.original_names, row))
        is_model = all(any(assignment[name(lit)] != lit.startswith(b"-") for lit in clause)
                       for clause in source_clauses)
        pins = dict(enumerate(row, 1))
        numeric_bytes = {str(i).encode(): bit for i, bit in pins.items()}
        assert dpll_count(target, named_vars, numeric_bytes) == int(is_model)
        closure = unit_propagate(integers, pins | fixed_anchors)
        if is_model:
            assert len(closure) == ext.total and sum(closure.values()) == ext.weight
            assert all(closure[v + i] != bit for i, bit in pins.items())
            models += 1
        else:
            assert closure is None
    return 1 << v, models


def audit():
    weight_cases = 0
    for states in range(1, 4):
        for digits in range(1, 8):
            assert automaton_weights(states, digits) == direct_weights(states, digits)
            weight_cases += 1
    # Test every choice of interior forbidden points and every nonempty
    # feasible interval. Its nearest forbidden points can lie outside it.
    gap_cases = 0
    for total in range(1, 9):
        for mask in range(1 << (total - 1)):
            marks = {0, total} | {x for x in range(1, total) if mask >> (x - 1) & 1}
            for lo in range(total + 1):
                for hi in range(lo, total + 1):
                    distances = [min(abs(x - f) for f in marks) for x in range(lo, hi + 1)]
                    margin = max(distances)
                    assert farthest_weight(total, lo, hi, marks) == (lo + distances.index(margin), margin)
                    gap_cases += 1
    files = projections = models = 0

    def check(raw, states, min_variables=0):
        nonlocal files, projections, models
        new_projections, new_models = audit_source(raw, states, min_variables)
        files += 1
        projections += new_projections
        models += new_models

    triples = [tuple(x if sign else -x for x, sign in zip((29, 3, 105), signs))
               for signs in product((False, True), repeat=3)]
    for selection in range(256):
        clauses = [c for i, c in enumerate(triples) if selection >> i & 1]
        lines = [f"p cnf 1500 {len(clauses)}"]
        lines.extend(f"{x} {y} {z} 0" for x, y, z in clauses)
        check("\n".join(lines).encode(), 2)

    huge = b"9" * 4500
    sparse = (b"c sparse, unused declaration, repeated clause and aliases\np cnf 1" +
              b"0" * 4500 + b" 2\n" + huge + b" -0002 030 0\n" + huge + b" -2 30 0\n")
    assert extend(sparse, 3).original_names == (b"2", b"30", huge)
    check(sparse, 3)
    requested = b"p cnf 90 1\n90 -3 5 0\n"
    assert extend(requested, 2, min_variables=70).total == 128
    check(requested, 2, min_variables=70)
    rng = Random(20261126)
    for v in range(3, 8):
        for size in (1, 5, 17):
            rows = [rng.sample(range(1, v + 1), 3) for _ in range(size)]
            lines = [f"p cnf {100 * v} {size}"]
            for row in rows:
                signed = [x if rng.randrange(2) else -x for x in row]
                lines.append(" ".join(map(str, signed)) + " 0")
            check("\n".join(lines).encode(), 3)

    # Exhaust literal permutations on four positions. On sixteen positions
    # enumerate the distinct supports in the permutation orbit instead.
    from automatic_assignment_front_audit import affine_word, reference_automaton_words
    empty = extend(b"p cnf 999 0\n", 1)
    assert (empty.total, empty.weight) == (4, 1)
    target = [tuple(map(int, row)) for row in read_dimacs(empty.data)]
    model = unit_propagate(target, {1: False, 2: False, 3: False})
    forbidden_words = reference_automaton_words(4, 1) | {
        affine_word(4, bias, mask) for bias in (0, 1) for mask in range(4)}
    orders = 0
    for order in permutations(range(1, empty.total + 1)):
        word = sum(int(model[var]) << i for i, var in enumerate(order))
        assert word not in forbidden_words
        orders += 1
    print(f"{weight_cases} DP spectra matched exhaustive labelled-table evaluation")
    print(f"{gap_cases} complete-spectrum/interval choices matched a direct max-min search")
    print(f"{files} files, {projections} projections, {models} uniquely extended models")
    two_state = extend(b"p cnf 999 0\n", 2)
    assert (two_state.total, two_state.weight, two_state.margin) == (16, 3, 2)
    forbidden_words = reference_automaton_words(16, 2) | {
        affine_word(16, bias, mask) for bias in (0, 1) for mask in range(16)}
    supports = 0
    nearest = two_state.total
    for indices in combinations(range(two_state.total), two_state.weight):
        word = sum(1 << i for i in indices)
        distance = min((word ^ witness).bit_count() for witness in forbidden_words)
        assert distance >= two_state.margin
        nearest = min(nearest, distance)
        supports += 1
    assert nearest == two_state.margin
    represented = supports * factorial(two_state.weight) * factorial(two_state.total - two_state.weight)
    assert represented == factorial(two_state.total)
    print(f"{orders} explicit permutations at V=4, {supports} supports covering all {represented} orders at V=16")
    four_state = extend(b"p cnf 999 0\n", 4)
    assert four_state.total == 512 and four_state.margin > 0
    print(f"Four states, empty source: V={four_state.total}, weight={four_state.weight}, margin={four_state.margin}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--states", type=int, help="extend standard input for this DFAO bound")
    parser.add_argument("--min-variables", type=int, default=0,
                        help="minimum number of occurring target variables")
    parser.add_argument("--report", action="store_true", help="report size, weight and margin on stderr")
    options = parser.parse_args()
    if options.states is None:
        if options.min_variables or options.report:
            parser.error("--min-variables and --report require --states")
        audit()
    else:
        output = extend(sys.stdin.buffer.read(), options.states, options.min_variables)
        sys.stdout.buffer.write(output.data)
        if options.report:
            print(f"variables={output.total} weight={output.weight} margin={output.margin}", file=sys.stderr)
