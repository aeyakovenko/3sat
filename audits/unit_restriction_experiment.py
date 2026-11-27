"""Exhaustive small checks of the fixed unit-propagation candidate on restrictions."""

from fractions import Fraction
from itertools import product


def restrict(cnf, pins):
    residual = []
    for clause in cnf:
        if any(pins.get(abs(lit)) == (lit > 0) for lit in clause):
            continue
        remaining = tuple(lit for lit in clause if abs(lit) not in pins)
        if not remaining:
            return ((),)
        residual.append(remaining)
    return tuple(residual)


def unit_verdict(cnf):
    """Simple reference implementation; the paper gives the linear-time version."""
    while cnf:
        if () in cnf:
            return False
        unit = next((clause[0] for clause in cnf if len(clause) == 1), None)
        if unit is None:
            return False
        cnf = restrict(cnf, {abs(unit): unit > 0})
    return True


def circuit_cnf(bits):
    # An OR of the selected minterms. Every AND/OR has its own output variable.
    clauses = []
    next_name = 4

    def gate(a, b, is_and):
        nonlocal next_name
        z = next_name
        next_name += 1
        if is_and:
            clauses.extend(((-z, a), (-z, b), (z, -a, -b)))
        else:
            clauses.extend(((z, -a), (z, -b), (-z, a, b)))
        return z

    output = None
    for index, values in enumerate(product((False, True), repeat=3)):
        if not bits & (1 << index):
            continue
        a, b, c = (i if v else -i for i, v in enumerate(values, start=1))
        term = gate(gate(a, b, True), c, True)
        output = term if output is None else gate(output, term, False)
    if output is None:
        clauses.append(())
    else:
        clauses.append((output,))
    z, w = next_name, next_name + 1
    clauses.extend(((-z, w), (z, -w)))
    return tuple(clauses), z


def check_layers():
    layer_cases = 0
    for table in range(256):
        cnf, z = circuit_cnf(table)
        assert not unit_verdict(cnf)
        for index, values in enumerate(product((False, True), repeat=3)):
            for guard in (False, True):
                pins = dict(enumerate(values, start=1))
                pins[z] = guard
                assert unit_verdict(restrict(cnf, pins)) == bool(table & (1 << index))
                layer_cases += 1
    print(f"circuit layers: 256 roots, {layer_cases} correct pinned verdicts")


def check_sparse_defects(m):
    variable_count = 2 * m + 1
    cnf = tuple((1, 2 + 2 * i, 3 + 2 * i) for i in range(m))
    assert not unit_verdict(cnf)
    defect_mass = 0
    for values in product((None, False, True), repeat=variable_count):
        pins = {v: b for v, b in enumerate(values, start=1) if b is not None}
        residual = restrict(cnf, pins)
        answer = unit_verdict(residual)
        present = {abs(lit) for clause in residual for lit in clause}
        defect = any(answer != any(unit_verdict(restrict(residual, {v: b}))
                                   for b in (False, True)) for v in present)
        fixed_false_pair = any(values[1 + 2 * i] is False and values[2 + 2 * i] is False
                               for i in range(m))
        assert not (fixed_false_pair and defect)
        if defect:
            defect_mass += 2 ** (variable_count - len(pins))
    probability = Fraction(defect_mass, 4 ** variable_count)
    bound = Fraction(15, 16) ** m
    a, b, d = Fraction(7, 16), Fraction(1, 16), Fraction(1, 4)
    exact = ((1 - b) ** m - a ** m) / 2 + m * d * (1 - b - d) ** (m - 1) / 4
    assert probability == exact <= bound
    print(f"shared-literal family m={m}: defect probability {probability}, bound {bound}")


if __name__ == "__main__":
    check_layers()
    for pairs in range(1, 5):
        check_sparse_defects(pairs)
