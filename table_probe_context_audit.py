"""Check proper, packed DIMACS encodings of the table-indexing predicate."""

from collections import Counter
from itertools import product


def mux_tree(address_bits):
    entries = 1 << address_bits
    # Heap node 1 is the root; left and right append a 0 or a 1 to the prefix.
    node = lambda index: address_bits + index
    false1, false2, pad1, pad2 = range(address_bits + 2 * entries,
                                      address_bits + 2 * entries + 4)
    fixed = [(-forced, a * pad1, b * pad2) for forced in (false1, false2)
             for a, b in product((-1, 1), repeat=2)]
    fixed.append((node(1), false1, false2))
    for i in range(1, entries):
        address = i.bit_length()
        z, low, high = node(i), node(2 * i), node(2 * i + 1)
        fixed.extend(((address, -low, z), (address, low, -z),
                      (-address, -high, z), (-address, high, -z)))
    pins = list(range(1, address_bits + 1)) + [node(i) for i in range(entries, 2 * entries)]
    return pad2, fixed, pins, false1, false2


def template(address_bits):
    count, fixed, pins, false1, false2 = mux_tree(address_bits)
    width = 16
    while True:
        word_bytes = width // 8
        file = bytearray(f'p cnf {count} {len(fixed) + len(pins)}\n', 'ascii')
        for clause in fixed:
            file.extend((' '.join(map(str, clause)) + ' 0\n').encode('ascii'))
        sign_addresses = []
        for v in pins:
            file.extend(b' ' * (-len(file) % word_bytes))
            sign_addresses.append(len(file) // word_bytes)
            file.extend(b' ' * word_bytes)
            file.extend(f'{v} {false1} {false2} 0\n'.encode('ascii'))
        file.extend(b' ' * (-len(file) % word_bytes))
        desired = 16 * (((len(file) * 8 + 1).bit_length() + 15) // 16)
        if width == desired:
            return bytes(file), sign_addresses, word_bytes
        assert width < desired
        width = desired


def parse(file):
    header, body = file.split(b'\n', maxsplit=1)
    fmt, kind, variables, count = header.split()
    assert (fmt, kind) == (b'p', b'cnf')
    words = list(map(int, body.split()))
    assert len(words) == 4 * int(count) and all(v == 0 for v in words[3::4])
    clauses = [tuple(words[i:i + 3]) for i in range(0, len(words), 4)]
    assert all(len({abs(v) for v in c}) == 3 for c in clauses)
    assert {abs(v) for c in clauses for v in c} == set(range(1, int(variables) + 1))
    return clauses, int(variables)


def satisfiable(clauses):
    """DPLL on the parsed clauses, with no knowledge of the intended circuit."""
    while clauses:
        if any(not c for c in clauses):
            return False
        unit = next((c[0] for c in clauses if len(c) == 1), None)
        if unit is None:
            occurrences = Counter(abs(v) for c in clauses for v in c)
            variable = max(occurrences, key=occurrences.get)
            return any(satisfiable(clauses + [(literal,)]) for literal in (variable, -variable))
        clauses = [tuple(v for v in c if v != -unit) for c in clauses if unit not in c]
    return True


def truth_table_sat(clauses, variables):
    return any(all(any(bits[abs(v) - 1] == (v > 0) for v in c) for c in clauses)
               for bits in product((False, True), repeat=variables))


def audit(t):
    blob, slots, word_bytes = template(t)
    assert len(set(slots)) == t + (1 << t)
    rows = 0
    for table in product((False, True), repeat=1 << t):
        outputs = []
        for address in range(1 << t):
            bits = [bool(address & (1 << j)) for j in reversed(range(t))]
            bits.extend(table)
            file = bytearray(blob)
            for slot, value in zip(slots, bits):
                start = slot * word_bytes
                end = start + word_bytes
                assert file[start:end] == b' ' * word_bytes
                assert ord('0') <= file[end] <= ord('9')
                if not value:
                    file[end - 1] = ord('-')
            changed = {i for i, (a, b) in enumerate(zip(blob, file)) if a != b}
            assert changed == {(s + 1) * word_bytes - 1 for s, v in zip(slots, bits) if not v}
            clauses, variables = parse(file)
            result = satisfiable(clauses)
            assert result == table[address]
            if t <= 1:
                assert truth_table_sat(clauses, variables) == result
            outputs.append(result)
            rows += 1
        assert tuple(outputs) == table
    return rows, len(blob) * 8, word_bytes * 8


def audit_two_query_states():
    # States 0 and 1 each probe one fixed address bit. Edges may return to
    # either state. Labels 2 and 3 halt with 0 and 1; label 4 diverges.
    partial = set()
    systems = 0
    for root, a0, a1, b0, b1 in product(range(5), repeat=5):
        edges = ((a0, a1), (b0, b1))
        truth = []
        for bits in product((0, 1), repeat=2):
            state = root
            visited = set()
            while state < 2 and state not in visited:
                visited.add(state)
                state = edges[state][bits[state]]
            truth.append(state - 2 if state in (2, 3) else None)
        partial.add(tuple(truth))
        systems += 1
    total = {f for f in partial if None not in f}
    missing = set(product((0, 1), repeat=4)) - total
    assert missing == {(0, 1, 1, 0), (1, 0, 0, 1)}
    return systems, len(partial), len(total)


def audit_eight_clause_obstruction():
    fixed = [(x, 2 * y, 3 * z) for x, y, z in product((1, -1), repeat=3)
             if (y, z) != (1, 1)]
    header = b'p cnf 3 8\n'
    prefix = header + b''.join((' '.join(map(str, c)) + ' 0\n').encode('ascii') for c in fixed)
    records = [prefix + s + b'1 2 3 0\n' + t + b'1 2 3 0\n'
               for s, t in product((b' ', b'-'), repeat=2)]
    assert len({len(raw) for raw in records}) == 1
    first, second = len(prefix), len(prefix) + len(b' 1 2 3 0\n')
    assert {i for i, column in enumerate(zip(*records)) if len(set(column)) > 1} == {first, second}
    length = len(records[0])
    width = 16 * (((length * 8 + 1).bit_length() + 15) // 16)
    locations = (first // (width // 8), second // (width // 8))
    assert locations[0] != locations[1]
    truth = []
    for raw in records:
        clauses, variables = parse(raw)
        models = [assignment for assignment in product((False, True), repeat=variables)
                  if all(any(assignment[abs(v) - 1] == (v > 0) for v in c) for c in clauses[:-2])]
        assert models == [(False, False, False), (True, False, False)]
        truth.append(truth_table_sat(clauses, variables))
        assert satisfiable(clauses) == truth[-1]
    assert truth == [True, False, False, True]
    return length, (first, second), width, locations


if __name__ == '__main__':
    for width in range(4):
        count, length, word_width = audit(width)
        print(f'{width} address bits: {count} proper formulas, {length} encoded bits, '
              f'{word_width}-bit RAM words')
    systems, partial, total = audit_two_query_states()
    print(f'{systems} cyclic two-query systems, {partial} partial functions including '
          f'{total} total functions; only XOR and its complement missing among total functions')
    length, offsets, width, locations = audit_eight_clause_obstruction()
    print(f'Four eight-clause XNOR files: {length} bytes each, sign offsets {offsets}, '
          f'{width}-bit word addresses {locations}, zero-based')
