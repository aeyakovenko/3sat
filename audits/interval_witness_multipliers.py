"""Extend an explicit tip permutation with prescribed integer count factors."""

from simple_permutation_successor import valid_order

INCREMENT = (1, 2, 0, 4, 5, 3)
DOUBLE_PLUS_ONE = (1, 5, 3, 4, 2, 0)
RESET = (1, 2, 0, 3)
ABSOLUTE_RESET = (1, 2, 0, 5, 3, 6, 4)
LOW_DEGREE = (0, 2, 1, 3, 5, 4)


def integer_blocks(value):
    """Read blocks from the left until the suffix parameter is one."""
    if value < 1:
        raise ValueError("expected a positive multiplier")
    while value > 1:
        if value % 2 == 0:
            yield INCREMENT
            value -= 1
        if value > 1:
            yield DOUBLE_PLUS_ONE
            value = (value - 1) // 2


def maximal_prime_powers(limit):
    """One largest power at most limit for each prime at most limit."""
    marked = bytearray(limit + 1)
    for prime in range(2, limit + 1):
        if marked[prime]:
            continue
        for multiple in range(prime + prime, limit + 1, prime):
            marked[multiple] = 1
        power = prime
        while power <= limit // prime:
            power *= prime
        yield power


def append_block(order, block):
    offset = len(order)
    order.extend(offset + i for i in block)


def protect_counts(source, modulus_limit, observed_variables):
    """Render the entire permutation. The input is any nonempty tip permutation."""
    if not source or not valid_order(source):
        raise ValueError("expected a nonempty permutation")
    if modulus_limit < 2 or observed_variables < 0:
        raise ValueError("invalid modulus or restriction budget")
    result = list(source)
    for power in maximal_prime_powers(modulus_limit):
        digits = tuple(integer_blocks(power))
        for _ in range(observed_variables + 1):
            for block in (ABSOLUTE_RESET, *digits, ABSOLUTE_RESET):
                append_block(result, block)
    return tuple(result)


def proper_count_clauses(order):
    """A parsimonious proper 3-CNF, including one Boolean sign bit per triangle.

    A satisfying sign vector determines every base color, tip color and sign
    flag. The initial base has color zero. Colors use exactly-one triples.
    """
    if not order or not valid_order(order):
        raise ValueError("expected a nonempty permutation")
    t = len(order)
    false_a, false_b, false_c = (7 * t + 4 + i for i in range(3))
    clauses = []
    for mask in range(1, 8):
        clauses.append(
            tuple(
                -x if mask >> i & 1 else x
                for i, x in enumerate((false_a, false_b, false_c))
            )
        )

    def color_var(v, c):
        return 1 + 3 * v + c

    def forbid_same(u, v):
        for c in range(3):
            clauses.append((-color_var(u, c), -color_var(v, c), false_a))

    for v in range(2 * t + 1):
        flags = tuple(color_var(v, c) for c in range(3))
        clauses.append(flags)
        for c in range(3):
            clauses.append((-flags[c], -flags[(c + 1) % 3], false_a))
    clauses.append((color_var(0, 0), false_a, false_b))
    for i in range(t):
        left, tip, right = 2 * i, 2 * i + 1, 2 * i + 2
        forbid_same(left, tip)
        forbid_same(tip, right)
        forbid_same(left, right)
        sign_flag = 6 * t + 4 + i
        for c in range(3):
            for step, lit in ((1, sign_flag), (2, -sign_flag)):
                clauses.append(
                    (-color_var(left, c), -color_var(right, (c + step) % 3), lit)
                )
    for i in range(t - 1):
        forbid_same(2 * order[i] + 1, 2 * order[i + 1] + 1)
    return clauses


def proper_count_dimacs(order):
    """Fixed-width decimal literal slots preserve the positions of local edits."""
    clauses = proper_count_clauses(order)
    variables = 7 * len(order) + 6
    width = len(str(variables)) + 1
    positive = [str(i).rjust(width) for i in range(variables + 1)]
    negative = [str(-i).rjust(width) for i in range(variables + 1)]
    lines = [f"p cnf {variables} {len(clauses)}"]
    for clause in clauses:
        tokens = [negative[-v] if v < 0 else positive[v] for v in clause]
        lines.append(" ".join(tokens) + " 0")
    return ("\n".join(lines) + "\n").encode("ascii")
