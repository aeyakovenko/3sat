"""Check actual width-three clauses with a DPLL search independent of the generator."""

from itertools import product


def pin(variable, bit, dummy_one, dummy_two):
    literal = variable if bit else -variable
    return [(literal, first * dummy_one, second * dummy_two)
            for first, second in product((-1, 1), repeat=2)]


def xor_gate(left, right, out):
    return [tuple(-var if bit else var for var, bit in zip((left, right, out), bits))
            for bits in product((0, 1), repeat=3) if bits[2] != bits[0] ^ bits[1]]


def formula(rows, h):
    alphabet = 1 << h
    table_size = alphabet ** 3
    initial_parity = table_size + 1
    dummies = (initial_parity + len(rows) + 1, initial_parity + len(rows) + 2)
    clauses = []
    for a, b, z in product(range(alphabet), repeat=3):
        position = 1 + (a * alphabet + b) * alphabet + z
        clauses.extend(pin(position, (a & b & z).bit_count() % 2, *dummies))
    clauses.extend(pin(initial_parity, 0, *dummies))
    clauses.extend(pin(initial_parity + len(rows), 1, *dummies))
    for i, (a, b, z) in enumerate(rows):
        position = 1 + (a * alphabet + b) * alphabet + z
        clauses.extend(xor_gate(initial_parity + i, position, initial_parity + i + 1))
    assert all(len(set(map(abs, clause))) == 3 for clause in clauses)
    return clauses


def satisfiable(clauses):
    if not clauses:
        return True
    if () in clauses:
        return False
    shortest = min(clauses, key=len)
    branches = shortest if len(shortest) == 1 else (shortest[0], -shortest[0])
    for literal in branches:
        residual = [tuple(x for x in c if x != -literal) for c in clauses if literal not in c]
        if satisfiable(residual):
            return True
    return False


def main():
    from random import Random
    rng = Random(419)
    cases = 0
    for h, row_count, exhaustive in ((1, 2, True), (1, 8, False), (2, 5, False)):
        rows = list(product(range(1 << h), repeat=3))
        matrices = (product(rows, repeat=row_count) if exhaustive else
                    (rng.choices(rows, k=row_count) for _ in range(32)))
        for selected in matrices:
            expected = sum((a & b & z).bit_count() for a, b, z in selected) % 2
            assert satisfiable(formula(selected, h)) == bool(expected)
            cases += 1
    print(f"{cases} packed three-CNF verdicts passed")


if __name__ == "__main__":
    main()
