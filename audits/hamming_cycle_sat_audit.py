"""Audit the proper 3-CNF compiler and its model counts on actual DIMACS files."""

from argparse import ArgumentParser
from itertools import product
from subprocess import run


def forbidden(names, pattern):
    return tuple(-v if bit else v for v, bit in zip(names, pattern, strict=True))


def even_parity(a, b, c):
    names = (a, b, c)
    return [forbidden(names, p) for p in product((0, 1), repeat=3) if sum(p) % 2]


def block(start, source):
    data = list(range(start, start + 7))
    fresh = start + 7
    clauses = []
    for row in range(3):
        a, b, c, d = [v for position, v in enumerate(data, start=1) if position & (1 << row)]
        r = fresh
        fresh += 1
        clauses.extend(even_parity(a, b, r))
        if row == 0 and source is not None:
            t = fresh
            fresh += 1
            clauses.extend(even_parity(c, d, t))
            clauses.extend(even_parity(r, t, source))
        else:
            clauses.extend(even_parity(r, c, d))
    return clauses, fresh


def encode(clauses, largest):
    body = ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)
    return (f'p cnf {largest} {len(clauses)}\n' + body).encode('ascii')


def decode(raw):
    lines = raw.splitlines()
    tag, kind, largest, count = lines[0].split()
    assert (tag, kind) == (b'p', b'cnf')
    assert len(lines) - 1 == int(count)
    clauses = []
    for line in lines[1:]:
        a, b, c, end = map(int, line.split())
        names = {abs(a), abs(b), abs(c)}
        assert end == 0 and len(names) == 3 and min(names) >= 1 and max(names) <= int(largest)
        clauses.append((a, b, c))
    return clauses


def satisfies(clauses, assignment):
    return all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses)


def syndrome(word):
    value = 0
    for index, bit in enumerate(word, start=1):
        if bit:
            value ^= index
    return value


def audit_fibers(source):
    start = 4
    clauses, end = block(start, source)
    tested = decode(encode(clauses, end - 1))
    cosets = {}
    for pin in (0, 1) if source is not None else (0,):
        words = []
        for data in product((0, 1), repeat=7):
            assignment = dict(enumerate(data, start=start))
            if source is not None:
                assignment[source] = pin
            count = 0
            for aux in product((0, 1), repeat=end - start - 7):
                assignment.update(enumerate(aux, start=start + 7))
                count += satisfies(tested, assignment)
            assert count == int(syndrome(data) == pin)
            if count:
                words.append(data)
        assert len(words) == 16
        assert min(sum(x != y for x, y in zip(a, b, strict=True))
                   for i, a in enumerate(words) for b in words[i + 1:]) == 3
        assert (pin, 0, 0, 0, 0, 0, 0) in words
        cosets[pin] = len(words)
    return cosets


def audit_pinned_encoder(solver):
    """Solve physical proper 3-CNF for all inputs to the graph of a [7,4,3] encoder."""
    guards = (1, 2, 3)
    fixed_false = [forbidden(guards, p) for p in product((0, 1), repeat=3) if any(p)]
    names = tuple(10 * i + 2 for i in range(1, 12))
    a, b, c, d = names[:4]
    # Fresh XOR gates 4..9 give the parity coordinates at positions 1, 2, 4.
    gates = ((a, b, 4), (4, d, 5), (a, c, 6), (6, d, 7),
             (b, c, 8), (8, d, 9))
    actual_outputs = (5, 7, a, 9, b, c, d)
    fixed = []
    for yes in names:
        no = yes + 1
        fixed.extend(((yes, no, 1), (-yes, -no, 1)))
    for gate in gates:
        fixed.extend(even_parity(*gate))
    for actual, proposed in zip(actual_outputs, names[4:], strict=True):
        fixed.extend(((-actual, proposed, 1), (actual, -proposed, 1)))

    largest = names[-1] + 1
    used = {abs(lit) for row in fixed_false + fixed for lit in row}
    fixed.extend((-1, v, 3) for v in range(1, largest + 1) if v not in used)

    def file_for(bits):
        units = [(name if bit else name + 1, 1, 2) for name, bit in zip(names, bits, strict=True)]
        return encode(fixed_false + units + fixed, largest)

    def satisfiable(parsed):
        # Enumerate all guard assignments and apply ordinary unit propagation.
        # At a fixed point every surviving clause in these files is satisfied.
        for guard_values in product((0, 1), repeat=3):
            values = dict(zip(guards, guard_values, strict=True))
            while True:
                previous = len(values)
                complete = True
                for row in parsed:
                    if any(values.get(abs(lit)) == (lit > 0) for lit in row):
                        continue
                    unknown = [lit for lit in row if abs(lit) not in values]
                    if not unknown:
                        break
                    if len(unknown) == 1:
                        lit = unknown[0]
                        values[abs(lit)] = lit > 0
                    else:
                        complete = False
                else:
                    if complete:
                        return True
                    assert len(values) > previous, 'unresolved clauses after unit propagation'
                    continue
                break
        return False

    base = file_for([0] * 11)
    base_mask = int.from_bytes(base, 'little')
    changes = []
    for index in range(11):
        single = [int(j == index) for j in range(11)]
        delta = base_mask ^ int.from_bytes(file_for(single), 'little')
        assert delta.bit_count() == 1 and delta not in changes
        changes.append(delta)

    accepted = []
    for bits in product((0, 1), repeat=11):
        message, word = bits[:4], bits[4:]
        # Independent specification: systematic positions and Hamming syndrome.
        expected = tuple(word[i] for i in (2, 4, 5, 6)) == message and syndrome(word) == 0
        raw = file_for(bits)
        edited_mask = sum(delta for delta, bit in zip(changes, bits, strict=True) if bit)
        assert len(raw) == len(base) and int.from_bytes(raw, 'little') ^ base_mask == edited_mask
        assert satisfiable(decode(raw)) == expected
        if solver:
            check = run([solver, '-q'], input=raw, capture_output=True, check=False)
            assert check.returncode == (10 if expected else 20), (bits, check.stderr)
        if expected:
            accepted.append(bits)
    assert len(accepted) == 16
    distance = min(sum(u != v for u, v in zip(x, y, strict=True))
                   for i, x in enumerate(accepted) for y in accepted[i + 1:])
    assert distance == 4
    print('2048 physical encoder graph formulas checked (16 messages x 128 outputs); '
          '16 accepted, 2032 rejected, 11 independent one-bit edits, graph distance 4.')


def main(solver):
    pin_count = audit_fibers(1)
    assert audit_fibers(None) == {0: 16}
    source_rows = [forbidden((1, 2, 3), p) for p in product((0, 1), repeat=3)]
    append1, next_var = block(4, 1)
    append2, end = block(next_var, 2)
    positive = 0
    for mask in range(256):
        source = [row for k, row in enumerate(source_rows) if mask & (1 << k)]
        raw = encode(source + append1 + append2, end - 1)
        parsed = decode(raw)
        assert parsed == source + append1 + append2
        models = sum(pin_count[a] * pin_count[b] for a, b, c in product((0, 1), repeat=3)
                     if satisfies(source, {1: a, 2: b, 3: c}))
        assert models == (8 - mask.bit_count()) * 16**2
        positive += models > 0
        if solver:
            check = run([solver, '-q'], input=raw, capture_output=True, check=False)
            assert check.returncode == (10 if models else 20), (mask, check.returncode, check.stderr)
    assert positive == 255
    print('Three one-block fibers checked by exhaustive auxiliary enumeration; each has 16 words and distance 3.')
    print(f'256 physical two-block formulas, {positive} positive and one negative; exact per-source multiplier 256.')
    if solver:
        print('All 256 DIMACS verdicts agree with the supplied SAT solver.')
    audit_pinned_encoder(solver)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='optional CaDiCaL executable')
    main(parser.parse_args().solver)
