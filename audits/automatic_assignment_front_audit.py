"""Compare two satisfying-assignment searches with small exhaustive oracles.

Names take zero-based ranks in order of first occurrence. Every rank is read
most-significant bit first in the same number of bits, including leading zeros.
The automaton start state is zero. A failed search leaves SAT undecided.
"""

from functools import lru_cache
from itertools import islice, product
from random import Random

from cnf_width_dictionary_audit import canonical, name, read_dimacs, write_dimacs
from hidden_read_correlation_audit import walsh


def rank_bits(variable_count):
    return max(1, (variable_count - 1).bit_length())


def number_variables(source):
    ranks = {}
    clauses = []
    for row in source:
        converted = []
        for token in row:
            lit = canonical(token)
            # Signed rank plus one lets rank zero have either polarity.
            code = ranks.setdefault(name(lit), len(ranks) + 1)
            converted.append(-code if lit.startswith(b"-") else code)
        clauses.append(tuple(converted))
    return tuple(ranks), tuple(clauses)


def accessible_in_breadth_first_order(table, states):
    reached = [0]
    for state in reached:
        for dest in table[2 * state:2 * state + 2]:
            if dest not in reached:
                if dest != len(reached):
                    return False
                reached.append(dest)
    return len(reached) == states


def machines(states):
    for table in product(range(states), repeat=2 * states):
        if accessible_in_breadth_first_order(table, states):
            for output in range(1 << states):
                yield table, output


def trie_assignment_slices(batch, states, variables):
    """One bit per machine. Each trie node has a lane mask per DFAO state."""
    lanes = (1 << len(batch)) - 1
    delta = [[[0] * states for _ in range(states)] for _ in range(2)]
    accepting = [0] * states
    for lane, (table, output) in enumerate(batch):
        for state in range(states):
            if output >> state & 1:
                accepting[state] |= 1 << lane
            for bit in range(2):
                delta[bit][state][table[2 * state + bit]] |= 1 << lane
    level = [[lanes] + [0] * (states - 1)]
    for _ in range(rank_bits(variables)):
        children = []
        for node in level:
            for bit in range(2):
                child = [0] * states
                for origin in range(states):
                    for dest in range(states):
                        child[dest] |= node[origin] & delta[bit][origin][dest]
                children.append(child)
        level = children
    slices = []
    for node in level[:variables]:
        true_lanes = 0
        for current, marked in zip(node, accepting):
            true_lanes |= current & marked
        slices.append(true_lanes)
    return lanes, slices


@lru_cache(None)
def automaton_batches(variables, state_bound, batch_size):
    result = []
    for states in range(1, state_bound + 1):
        definitions = machines(states)
        while batch := tuple(islice(definitions, batch_size)):
            result.append(trie_assignment_slices(batch, states, variables))
    return result


def dfao_front(clauses, variables, state_bound, batch_size=64):
    models = set()
    for lanes, slices in automaton_batches(variables, state_bound, batch_size):
        passing = lanes
        for clause in clauses:
            satisfied = 0
            for lit in clause:
                column = slices[abs(lit) - 1]
                satisfied |= column if lit > 0 else lanes ^ column
            passing &= satisfied
            if not passing:
                break
        while passing:
            lane_bit = passing & -passing
            assignment = sum(1 << i for i, column in enumerate(slices) if lane_bit & column)
            models.add(assignment)
            passing ^= lane_bit
    return models


def falsifying_equations(clause, bias):
    """A basis of mask equations for falsifying every literal, or None."""
    basis = {}
    for literal in clause:
        row = abs(literal) - 1
        rhs = bias ^ int(literal < 0)
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row, rhs
                break
            other, target = basis[pivot]
            row ^= other
            rhs ^= target
        if row == 0 and rhs:
            return None
    return tuple(basis.values())


def affine_violations(clauses, variables, bias):
    """One integer Walsh transform yields all masks' counts for this bias."""
    size = 1 << rank_bits(variables)
    coefficients = [0] * size
    for clause in clauses:
        basis = falsifying_equations(clause, bias)
        if basis is None:
            continue
        terms = [(0, 1)]
        for row, rhs in basis:
            sign = -1 if rhs else 1
            terms += [(total ^ row, weight * sign) for total, weight in terms]
        scale = size >> len(basis)
        for index, weight in terms:
            coefficients[index] += scale * weight
    totals = walsh(coefficients)
    assert all(0 <= x <= size * len(clauses) and x % size == 0 for x in totals)
    return tuple(x // size for x in totals)


def affine_word(variables, bias, mask):
    return sum((bias ^ ((rank & mask).bit_count() % 2)) << rank for rank in range(variables))


def affine_front(clauses, variables):
    counts = tuple(affine_violations(clauses, variables, bias) for bias in (0, 1))
    models = {affine_word(variables, bias, mask)
              for bias, row in enumerate(counts)
              for mask, violated in enumerate(row) if violated == 0}
    return models, counts


@lru_cache(None)
def reference_automaton_words(variables, state_bound):
    """All labelled tables, also those with unused states; one rank at a time."""
    words = set()
    digits = [format(i, f"0{rank_bits(variables)}b") for i in range(variables)]
    for states in range(1, state_bound + 1):
        for table in product(range(states), repeat=2 * states):
            endpoints = []
            for spelling in digits:
                state = 0
                for char in spelling:
                    state = table[2 * state + int(char)]
                endpoints.append(state)
            for markings in product((0, 1), repeat=states):
                words.add(sum(markings[state] << i for i, state in enumerate(endpoints)))
    return words


def named_violations(source, names, word):
    values = {key: bool(word >> i & 1) for i, key in enumerate(names)}
    return sum(not any(values[name(lit)] != lit.startswith(b"-") for lit in clause)
               for clause in source)


def check_file(data, bound, batch_size=64):
    source = [tuple(map(canonical, clause)) for clause in read_dimacs(data)]
    names, clauses = number_variables(source)
    variables = len(names)
    counts = [named_violations(source, names, word) for word in range(1 << variables)]
    models = {word for word, violations in enumerate(counts) if violations == 0}
    automatic = dfao_front(clauses, variables, bound, batch_size)
    assert automatic == models & reference_automaton_words(variables, bound)
    affine, by_bias = affine_front(clauses, variables)
    size = 1 << rank_bits(variables)
    for bias, actual in enumerate(by_bias):
        candidates = [affine_word(variables, bias, mask) for mask in range(size)]
        assert actual == tuple(counts[word] for word in candidates)
    return models, automatic, affine, 2 * size


def main():
    files = satisfiable = affine_counts = 0
    # This machine counts zero digits modulo two. Dropping the leading zero
    # of rank 1 would give it the wrong output in this three-variable case.
    assert trie_assignment_slices([((1, 0, 0, 1), 2)], 2, 3) == (1, [0, 1, 1])

    def audit(raw, bound=2, batch_size=64):
        nonlocal files, satisfiable, affine_counts
        models, automatic, affine, checked = check_file(raw, bound, batch_size)
        files += 1
        satisfiable += bool(models)
        affine_counts += checked
        return models, automatic, affine

    # Exhaust ordered clauses, including repetitions, complementary signs,
    # empty clauses, empty conjunctions and both orders of first occurrence.
    literals = (b"9", b"-9", b"101", b"-101")
    pool = [c for width in range(4) for c in product(literals, repeat=width)]
    for count in range(3):
        for clauses in product(pool, repeat=count):
            audit(write_dimacs(clauses))

    # Dense rank 0..3 receives 0001, an AND of the two rank bits.
    # It is generated by a two-state DFAO and by no affine mask plus bias.
    huge = b"9" * 4500
    unique_and = (b"c sparse names and a leading-zero alias\np cnf " + huge +
                  b" 5\n-" + huge + b" 0\n-00017 0 -003 0\n2 0\n17 -17 0\n")
    assert audit(unique_and, bound=2, batch_size=3) == ({8}, {8}, set())
    assert audit(b"p cnf 99 2\n099 0\n-99 0\n") == (set(), set(), set())

    # Force a unique SAT model that the two-state family actually misses.
    missing = next(w for w in range(256) if w not in reference_automaton_words(8, 2))
    units = [(str(i + 1 if missing >> i & 1 else -(i + 1)).encode(),) for i in range(8)]
    found, automatic, _ = audit(write_dimacs(units))
    assert found == {missing} and not automatic

    rng = Random(42017)
    for variables in range(3, 9):
        for case in range(12):
            names = [str(1009 * (i + 3) ** 3).encode() for i in range(variables)]
            rng.shuffle(names)
            choices = names + [b"-" + x for x in names]
            clauses = [(x, b"-" + x) for x in names]
            for _ in range(8):
                width = rng.randrange(0 if case % 4 == 0 else 1, 7)
                clauses.append(tuple(rng.choice(choices) for _ in range(width)))
            audit(write_dimacs(clauses), bound=3, batch_size=(1, 7, 64)[case % 3])

    print(f"{files} DIMACS formulas, {satisfiable} SAT and {files - satisfiable} UNSAT")
    print(f"{affine_counts} bias/mask violation counts matched direct clause evaluation")
    print("DFAO batches of 1, 3, 7, 64 lanes matched full labelled-table enumeration")
    print("The unique four-variable AND model passed the DFAO search and missed every affine mask")


if __name__ == "__main__":
    main()
