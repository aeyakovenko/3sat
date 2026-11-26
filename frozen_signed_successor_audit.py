"""Check small proper DIMACS extensions, including every toggle edit on both branches."""

from itertools import product


def reserve(first):
    bits = (first, first + 1, first + 2)
    return [
        tuple(-wire if value else wire for wire, value in zip(bits, forbidden))
        for forbidden in product((0, 1), repeat=3)
        if any(forbidden)
    ]


def xor_gate(left, right, out):
    clauses = []
    for x, y in product((0, 1), repeat=2):
        wrong = 1 ^ x ^ y
        clauses.append(tuple(-w if b else w for w, b in zip((left, right, out), (x, y, wrong))))
    return clauses


def signed_block(old_variables, hidden, toggles, pin):
    first = old_variables + 1
    clauses = reserve(first)
    # The toy deterministic core fixes one output. Its role is semantic only.
    wire = first + 3
    clauses.append((wire if hidden else -wire, first, first + 1))
    for toggle in toggles:
        new, output = wire + 1, wire + 2
        clauses.append((new if toggle else -new, first, first + 1))
        clauses.extend(xor_gate(wire, new, output))
        wire = output
    clauses.append((wire if pin else -wire, first, first + 1))
    return wire, clauses


def record(clause, field):
    assert len(set(map(abs, clause))) == 3
    return (" ".join(f"{literal:>{field}d}" for literal in clause) + " 0\n").encode("ascii")


def model_count(clauses, num_vars):
    def visit(values):
        while True:
            need = None
            for clause in clauses:
                if any(values.get(abs(lit)) == (lit > 0) for lit in clause):
                    continue
                open_lits = [lit for lit in clause if abs(lit) not in values]
                if not open_lits:
                    return 0, None
                if len(open_lits) == 1:
                    need = open_lits[0]
                    break
            if need is None:
                break
            values[abs(need)] = need > 0
        if len(values) == num_vars:
            return 1, values
        var = next(v for v in range(1, num_vars + 1) if v not in values)
        total = 0
        sample = None
        for bit in (False, True):
            new_values = values.copy()
            new_values[var] = bit
            count, example = visit(new_values)
            total += count
            if example is not None:
                sample = example
        return total, sample

    return visit({})


def physical_file(num_vars, records):
    return f"p cnf {num_vars} {len(records)}\n".encode("ascii") + b"".join(records)


def parse(data):
    header, *rows = data.splitlines()
    label, cnf, variables, count = header.split()
    assert (label, cnf) == (b'p', b'cnf') and len(rows) == int(count)
    result = []
    for row in rows:
        a, b, c, end = map(int, row.split())
        assert end == 0 and all(0 < abs(v) <= int(variables) for v in (a, b, c))
        assert len({abs(a), abs(b), abs(c)}) == 3
        result.append((a, b, c))
    return int(variables), result


def audit_chain(sequence):
    old_vars = 3
    old_records = [record(clause, 3) for clause in reserve(1)]
    old_model = dict.fromkeys(range(1, 4), False)
    trials = 0
    for stage, hidden in enumerate(sequence, 1):
        length = stage + 1
        field = stage + 3
        for toggles in product((False, True), repeat=length):
            files = []
            for pin in (False, True):
                variables, clauses = signed_block(old_vars, hidden, toggles, pin)
                records = old_records + [record(clause, field) for clause in clauses]
                data = physical_file(variables, records)
                files.append(data)
                assert data.split(b'\n', 1)[1].startswith(b''.join(old_records))
                parsed_vars, parsed = parse(data)
                count, unique = model_count(parsed, parsed_vars)
                expected = pin == (hidden ^ (sum(toggles) % 2))
                assert count == int(expected)
                if expected:
                    assert all(unique[v] == val for v, val in old_model.items())
                    if not any(toggles):
                        next_vars, next_records, next_model = variables, records, unique
                trials += 1
            assert len(files[0]) == len(files[1])
            diffs = [(a, b) for a, b in zip(*files) if a != b]
            assert diffs == [(ord('-'), ord(' '))]
        old_vars, old_records, old_model = next_vars, next_records, next_model
    return trials


def audit_elimination():
    # Sixteen two-probe predictors, all Boolean functions on two mask pins.
    # Each sees real signed pin bytes. The circuit outcome is checked independently
    # by counting the models of its DIMACS encoding. This tests the filtering
    # step; the native instruction interpreter is outside this small fixture.
    codes = range(16)
    total = 0
    survivors = 0
    for initial in (0xFFFF, 0x5555, 0x3C3C, 0x0181, 0):
        active = initial
        while True:
            pins = []
            for i in codes:
                lit = 4 + i if active & (1 << i) else -(4 + i)
                pins.append((lit, 1, 2))
            mask_records = [record(c, 4) for c in pins]
            def candidate(i):
                a = int(b'-' not in mask_records[(i + 1) % 16])
                b = int(b'-' not in mask_records[(i + 5) % 16])
                return (i >> (2 * a + b)) & 1

            yes = [i for i in codes if active & (1 << i) and candidate(i)]
            chosen = yes[0] if yes else None
            # The fixture embeds each truth table as a gate on two actual mask
            # bits, then forbids an active candidate with a true output.
            clauses = reserve(1) + pins
            for i in codes:
                a, b, output = 4 + ((i + 1) % 16), 4 + ((i + 5) % 16), 20 + i
                for x, y in product((0, 1), repeat=2):
                    bit = (i >> (2 * x + y)) & 1
                    clauses.append((-a if x else a, -b if y else b, output if bit else -output))
                clauses.append((-(4 + i), -output, 1))
            data = physical_file(35, [record(c, 4) for c in clauses])
            variables, parsed = parse(data)
            count, _ = model_count(parsed, variables)
            assert count == int(chosen is None)
            total += 1
            if chosen is None:
                survivors += active.bit_count()
                break
            active ^= 1 << chosen
    return total, survivors


if __name__ == "__main__":
    trials = sum(audit_chain(s) for s in product((False, True), repeat=3))
    eliminated_trials, survivors = audit_elimination()
    print(f"{trials} signed DIMACS files with checked model counts and old-model restrictions")
    print(f"{eliminated_trials} within-scale DIMACS trials, {survivors} active programs on terminal files in total")
