"""Check proper DIMACS coordinate faces with independent PicoSAT verdicts.

Run with pycosat installed. The queue implements the generic fast path.
Python's dictionaries and integers are for testing; the manuscript gives the
deterministic radix/trie RAM implementation and its physical length bounds.
"""

from collections import defaultdict, deque
from itertools import product
from random import Random

import pycosat


def circuit_value(inputs, gates):
    values = list(inputs)
    for left, right, table in gates:
        values.append((table >> (2 * values[left] + values[right])) & 1)
    return bool(values[-1])


def formula(inputs, gates):
    """Wires are numbered from zero; one four-bit table describes each binary gate."""
    n = len(inputs)
    rails = [(10 * (i + 1) + 2, 10 * (i + 1) + 3) for i in range(n)]
    fresh = 10 * n + 4
    for _ in gates:
        rails.append((fresh, fresh + 1))
        fresh += 2
    anchors = (fresh, fresh + 1, fresh + 2)
    clauses = [tuple(-v if bit else v for v, bit in zip(anchors, bits))
               for bits in product((0, 1), repeat=3) if any(bits)]

    def padded(literals):
        terms = tuple(dict.fromkeys(literals))
        assert len({abs(v) for v in terms}) == len(terms)
        clauses.append(terms + anchors[:3 - len(terms)])

    for bit, pair in zip(inputs, rails):
        padded((pair[bit],))
    for zero, one in rails:
        padded((-zero, -one))
    for j, (left, right, table) in enumerate(gates, n):
        for a, b in product((0, 1), repeat=2):
            value = (table >> (2 * a + b)) & 1
            padded((-rails[left][a], -rails[right][b], rails[j][value]))
    padded((-rails[-1][0],))
    used = {v for pair in rails for v in pair} | set(anchors)
    for v in range(1, anchors[-1] + 1):
        if v not in used:
            padded((-v,))
    return clauses


def dumps(clauses, messy=False):
    highest = max(abs(lit) for clause in clauses for lit in clause)
    lines = [f'p cnf {highest} {len(clauses)}']
    for i, clause in enumerate(clauses):
        if messy and i % 13 == 0:
            lines.append('c shuffled literals and clauses')
        tokens = list(map(str, clause)) + ['0']
        lines.append((' \n\t' if messy and i % 5 == 0 else ' ').join(tokens))
    return ('\n'.join(lines) + '\n').encode('ascii')


def parse(data):
    """Intern long decimal names by their tokens, not by the declared maximum."""
    lines = [line.split() for line in data.splitlines() if line.strip()
             and not line.lstrip().startswith(b'c')]
    p, cnf, maximum, size = lines[0]
    assert (p, cnf) == (b'p', b'cnf')
    intern = {}
    clauses, clause = [], []
    for line in lines[1:]:
        for token in line:
            if token == b'0':
                assert len(clause) == 3 and len({abs(v) for v in clause}) == 3
                clauses.append(tuple(clause))
                clause = []
                continue
            digits = token.removeprefix(b'-')
            assert digits.isdigit() and not digits.startswith(b'0')
            assert (len(digits), digits) <= (len(maximum), maximum)
            v = intern.setdefault(digits, len(intern) + 1)
            clause.append(-v if token.startswith(b'-') else v)
    assert not clause and len(clauses) == int(size)
    return clauses, len(intern)


def propagate(data):
    """Return verdict, or None when exhaustive fallback would be needed."""
    clauses, count = parse(data)
    allowed = {}
    occurrences = defaultdict(list)
    for index, clause in enumerate(clauses):
        ordered = sorted(clause, key=abs)
        names = tuple(map(abs, ordered))
        forbidden = sum((lit < 0) << i for i, lit in enumerate(ordered))
        allowed[names] = allowed.get(names, 255) & ~(1 << forbidden)
        for literal in clause:
            occurrences[abs(literal)].append(index)

    queue = deque()
    for names, choices in allowed.items():
        if not choices:
            return False
        if choices.bit_count() == 1:
            setting = choices.bit_length() - 1
            for j, name in enumerate(names):
                queue.append(name if setting >> j & 1 else -name)

    assignment = [0] * (count + 1)
    while queue:
        lit = queue.popleft()
        name = abs(lit)
        if assignment[name]:
            if assignment[name] != lit:
                return False
            continue
        assignment[name] = lit
        for index in occurrences[name]:
            clause = clauses[index]
            if any(assignment[abs(v)] == v for v in clause):
                continue
            open_lits = [v for v in clause if not assignment[abs(v)]]
            if not open_lits:
                return False
            if len(open_lits) == 1:
                queue.append(open_lits[0])
    if all(any(assignment[abs(v)] == v for v in clause) for clause in clauses):
        return True
    return None


def check_file(data, expected):
    clauses, _ = parse(data)
    picosat = pycosat.solve(clauses)
    assert picosat != 'UNKNOWN'
    assert (picosat != 'UNSAT') == expected
    if expected:
        assert pycosat.solve(clauses + [tuple(-v for v in picosat)]) == 'UNSAT'
    assert propagate(data) == expected


def changed_bytes(a, b):
    assert len(a) == len(b)
    return [j for j in range(len(a)) if a[j] != b[j]]


def face_check(n, gates):
    zero = (0,) * n
    original = dumps(formula(zero, gates))
    offsets = []
    for i in range(n):
        single = tuple(int(i == j) for j in range(n))
        file = dumps(formula(single, gates))
        offset, = changed_bytes(original, file)
        assert (original[offset], file[offset]) == (ord('2'), ord('3'))
        offsets.append(offset)
    assert len(set(offsets)) == n
    for bits in product((0, 1), repeat=n):
        expected = circuit_value(bits, gates)
        data = dumps(formula(bits, gates))
        assembled = bytearray(original)
        for bit, offset in zip(bits, offsets):
            assembled[offset] ^= bit
        assert data == assembled
        check_file(data, expected)
    return 1 << n


def relabel(clauses, rng):
    names = sorted({abs(v) for clause in clauses for v in clause})
    permutation = names.copy()
    rng.shuffle(permutation)
    # Sparse identifiers wider than a conventional machine word.
    mapping = {i: (10**40 + p) * rng.choice((-1, 1))
               for i, p in zip(names, permutation)}
    result = []
    for clause in clauses:
        row = [mapping[abs(v)] if v > 0 else -mapping[abs(v)] for v in clause]
        rng.shuffle(row)
        result.append(tuple(row))
    rng.shuffle(result)
    return result


def extension_checks():
    rng = Random(84291)
    counts = 0
    gates = [(0, 1, 6), (2, 2, 8), (3, 4, 14), (0, 5, 6)]
    for bits in product((0, 1), repeat=3):
        base = formula(bits, gates)
        model = pycosat.solve(base)
        is_sat = model != 'UNSAT'
        names = sorted({abs(v) for row in base for v in row})
        variants = [base, base + base, base + [tuple(-v for v in base[0])]]
        if is_sat:
            truth = set(model)
            block = rng.sample(names, 3)
            falsified = tuple(-v if v in truth else v for v in block)
            variants.append(base + [falsified])
            variants.append(base + [(-falsified[0], *falsified[1:])])
        for _ in range(4):
            extra = [tuple(v * rng.choice((-1, 1)) for v in rng.sample(names, 3))
                     for _ in range(10)]
            variants.append(base + extra)
        for original in variants:
            expected = pycosat.solve(original) != 'UNSAT'
            check_file(dumps(relabel(original, rng), messy=True), expected)
            counts += 1
    # A single proper clause admits models but no pinned support or starting
    # unit. The fast path must leave this case to the general fallback.
    assert propagate(dumps([(1, 2, 3)])) is None
    positive = formula((1,), [])
    assert propagate(dumps(positive + [positive[0]])) is True
    # All-positive on the anchor triple forbids the remaining all-zero tuple.
    missing = tuple(abs(v) for v in positive[0])
    check_file(dumps(positive + [missing]), False)
    return counts


def cycle_circuit(n):
    gates = [(i, (i + 1) % n, 14) for i in range(n)]
    output = n
    for i in range(1, n):
        gates.append((output, n + i, 8))
        output = n + len(gates) - 1
    return gates


def consecutive_lengths():
    sizes = list(range(3, 8))
    circuits = [cycle_circuit(n) for n in sizes]
    minimum = max(len(dumps(formula([0] * n, c))) for n, c in zip(sizes, circuits))
    lengths = []
    for step, (n, circuit) in enumerate(zip(sizes, circuits)):
        length = minimum + step
        for bits in product((0, 1), repeat=n):
            ordinary = dumps(formula(bits, circuit))
            assert len(ordinary) <= length
            padded = ordinary + b' ' * (length - len(ordinary))
            assert len(padded) == length
            check_file(padded, circuit_value(bits, circuit))
        lengths.append(length)
    return lengths


def large_parity_checks():
    rng = Random(27183)
    statistics = []
    for n in (16, 64, 256):
        gates = []
        acc = 0
        for i in range(1, n):
            gates.append((acc, i, 6))
            acc = n + len(gates) - 1
        bits = [rng.randrange(2) for _ in range(n)]
        data = dumps(formula(bits, gates))
        check_file(data, bool(sum(bits) % 2))
        changed = [1 - bit for bit in bits]
        flipped = dumps(formula(changed, gates))
        positions = changed_bytes(data, flipped)
        assert len(positions) == n and all(data[j] ^ flipped[j] == 1 for j in positions)
        gap = min(b - a for a, b in zip(positions, positions[1:]))
        statistics.append((n, len(data) * 8, gap))
    return statistics


def parity_name_blocks(widths, bits):
    """Each selected identifier is printed once; it chooses an entire block."""
    false_one, false_two = 1, 2
    out = [tuple(-v if b else v for v, b in zip((1, 2, 3), row))
           for row in product((0, 1), repeat=3) if any(row)]
    block_vars = []
    cursor = 0
    for i, width in enumerate(widths):
        block_vars.append(4 + i)
        local = bits[cursor:cursor + width]
        cursor += width
        for u in product((0, 1), repeat=width):
            name = int(str(11 + i) + ''.join('3' if b else '2' for b in u))
            z = block_vars[-1] if sum(u) % 2 else -block_vars[-1]
            out.extend([(-name, z, false_one), (name, -z, false_one)])
            if u == local:
                selected = name
        out.append((selected, false_one, false_two))
    acc = block_vars[0]
    fresh = 4 + len(widths)
    for z in block_vars[1:]:
        for a, b in product((0, 1), repeat=2):
            out.append((-acc if a else acc, -z if b else z,
                        fresh if a ^ b else -fresh))
        acc = fresh
        fresh += 1
    out.append((acc, false_one, false_two))
    return dumps(out)


def check_parity_name_blocks():
    cases = 0
    for widths in ((1, 1), (2, 1, 2), (3, 2, 1), (1, 2, 1, 2)):
        count = sum(widths)
        origin = parity_name_blocks(widths, (0,) * count)
        positions = []
        for i in range(count):
            choice = tuple(int(j == i) for j in range(count))
            data = parity_name_blocks(widths, choice)
            pos, = changed_bytes(origin, data)
            assert (origin[pos] ^ data[pos]) == 1
            positions.append(pos)
        assert len(set(positions)) == count
        for bits in product((0, 1), repeat=count):
            data = parity_name_blocks(widths, bits)
            assert set(changed_bytes(origin, data)) == {positions[i] for i, b in enumerate(bits) if b}
            # PicoSAT checks the actual printed file, including every pin.
            decoded_clauses, _ = parse(data)
            assert (pycosat.solve(decoded_clauses) != 'UNSAT') == bool(sum(bits) % 2)
            cases += 1
    return cases


if __name__ == '__main__':
    truth_table_checks = sum(face_check(2, [(0, 1, t)]) for t in range(16))
    repeated_checks = sum(face_check(1, [(0, 0, t)]) for t in range(16))
    cycles = sum(face_check(n, cycle_circuit(n)) for n in range(3, 8))
    print(f'all binary tables: {truth_table_checks}; repeated gate inputs: {repeated_checks}')
    print(f'cycle faces: {cycles}; shuffled/renamed/extended files: {extension_checks()}')
    print('parity (independent bits, encoded bits, minimum selector spacing in bytes):',
          large_parity_checks())
    print('cycle coordinate faces at consecutive physical byte lengths:', consecutive_lengths())
    print('complete multibit-name parity faces:', check_parity_name_blocks())
