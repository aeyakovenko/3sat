"""Check the indexed block templates and the reversed threshold on small native histories."""

from argparse import ArgumentParser
from bisect import bisect_right
from itertools import permutations, product
from subprocess import run

from free_presentation_audit import guarded_dimacs, models, trace_checks


def truth(literal, assignment):
    return assignment[abs(literal)] == (literal > 0)


def gate_clauses(output, gate):
    conjunction, left, right = gate
    names = list(dict.fromkeys([output, abs(left), abs(right), 1, 2, 3]))[:3]
    for values in product((False, True), repeat=3):
        table = dict(zip(names, values, strict=True))
        value = ((truth(left, table) and truth(right, table)) if conjunction
                 else (truth(left, table) or truth(right, table)))
        if table[output] != value:
            yield tuple(-name if bit else name for name, bit in zip(names, values, strict=True))
        else:
            yield (-1, 2, 3)


class BlockTemplate:
    """Gate ordinals depend only on port count. The callable supplies table replies."""

    def __init__(self, ports, first, reply):
        self.ports = ports
        self.first = first
        self.reply = reply
        self.low_bits = max(0, len(ports).bit_length() - 2)
        self.high_bits = len(ports) - self.low_bits
        self.low_rows = 1 << self.low_bits
        self.high_rows = 1 << self.high_bits
        self.high_tree = 2 * self.low_rows - 2
        self.library = self.high_tree + 2 * self.high_rows - 2
        self.row_tests = self.library + self.low_rows * (1 << self.low_rows)
        self.selection = self.row_tests + self.high_rows
        self.size = self.selection + self.high_rows

    def prefix(self, base, depth, index):
        return self.first + base + (1 << depth) - 2 + index if depth else -1

    def gate(self, ordinal):
        if ordinal < self.library:
            high = ordinal >= self.high_tree
            base = self.high_tree if high else 0
            bits = self.high_bits if high else self.low_bits
            offset = ordinal - base
            depth = (offset + 2).bit_length() - 1
            index = offset + 2 - (1 << depth)
            port = self.ports[(len(self.ports) if high else bits) - depth]
            return True, self.prefix(base, depth - 1, index // 2), port if index % 2 else -port
        if ordinal < self.row_tests:
            mask, low = divmod(ordinal - self.library, self.low_rows)
            previous = self.first + ordinal - 1 if low else 1
            indicator = self.prefix(0, self.low_bits, low) if mask >> low & 1 else 1
            return False, previous, indicator
        if ordinal < self.selection:
            high = ordinal - self.row_tests
            mask = sum(int(self.reply(high * self.low_rows + low)) << low for low in range(self.low_rows))
            selected = self.first + self.library + (mask + 1) * self.low_rows - 1
            return True, self.prefix(self.high_tree, self.high_bits, high), selected
        high = ordinal - self.selection
        previous = self.first + ordinal - 1 if high else 1
        return False, previous, self.first + self.row_tests + high


class IndexedFile:
    def __init__(self, inputs, templates):
        self.inputs = inputs
        self.templates = templates
        self.offsets = []
        block_clauses = 0
        for table in templates:
            self.offsets.append(block_clauses)
            block_clauses += 8 * table.size + 1
        self.variables = 3 + inputs + sum(table.size for table in templates)
        self.clause_count = 7 + inputs + block_clauses
        self.header = f'p cnf {self.variables} {self.clause_count}\n'.encode()
        self.field = 1 + len(str(self.variables))
        self.line = 3 * self.field + 5

    def clause(self, number):
        if number < 7:
            return tuple(-name if (number + 1) >> (name - 1) & 1 else name for name in (1, 2, 3))
        number -= 7
        if number < self.inputs:
            return number + 4, -1, 2
        number -= self.inputs
        block = bisect_right(self.offsets, number) - 1
        slot = number - self.offsets[block]
        template = self.templates[block]
        ordinal, row = divmod(slot, 8)
        if ordinal == template.size:
            return template.first + template.size - 1, 1, 2
        output = template.first + ordinal
        return list(gate_clauses(output, template.gate(ordinal)))[row]

    def line_at(self, number):
        literals = self.clause(number)
        assert len({abs(lit) for lit in literals}) == 3
        result = (' '.join(f'{lit:>{self.field}d}' for lit in literals) + ' 0\n').encode()
        assert len(result) == self.line
        return result

    def byte(self, index):
        if index < len(self.header):
            return self.header[index]
        number, column = divmod(index - len(self.header), self.line)
        return self.line_at(number)[column]

    def materialize(self):
        return self.header + b''.join(self.line_at(j) for j in range(self.clause_count))


def new_file(inputs, port_lists, replies):
    templates = []
    first = 4 + inputs
    for ports, reply in zip(port_lists, replies, strict=True):
        template = BlockTemplate(ports, first, reply)
        templates.append(template)
        first += template.size
    return IndexedFile(inputs, templates)


def check_extension(file, source):
    assigned = {1: False, 2: False, 3: False}
    assigned.update({4 + i: bool(source >> i & 1) for i in range(file.inputs)})
    expected = True
    for table in file.templates:
        row = sum(int(truth(port, assigned)) << i for i, port in enumerate(table.ports))
        expected &= bool(table.reply(row))
        for gate in range(table.size):
            conjunction, left, right = table.gate(gate)
            args = [truth(left, assigned), truth(right, assigned)]
            assigned[table.first + gate] = all(args) if conjunction else any(args)
        assert assigned[table.first + table.size - 1] == bool(table.reply(row))
    return expected, assigned


def solver_code(solver, raw, additions):
    header, body = raw.split(b'\n', maxsplit=1)
    count = int(header.split()[-1])
    header = header.rsplit(b' ', maxsplit=1)[0] + b' ' + str(count + len(additions)).encode() + b'\n'
    appended = b''.join((' '.join(map(str, clause)) + ' 0\n').encode() for clause in additions)
    return run([solver, '-q'], input=header + body + appended, capture_output=True, check=False).returncode


def audit_blocks(solver):
    cases = 0
    for relation in range(256):
        file = new_file(3, [[4, 5, 6]], [lambda row, table=relation: table >> row & 1])
        for assignment in range(8):
            passed, _ = check_extension(file, assignment)
            assert passed == bool(relation >> assignment & 1)
            cases += 1

    # Two shared interfaces, with signed/repeated inputs and pinned constants.
    # These functions intentionally ignore some table arguments.
    file = new_file(4, [[4, 5, -6, 4, 1], [6, 7, -4, -1, 7]],
                    [lambda a: (a ^ (a >> 1)) & 1,
                     lambda a: ((a >> 1) ^ (a >> 2)) & 1])
    raw = file.materialize()
    probes = set(range(0, len(raw), 61)) | set(range(len(file.header))) | {len(raw) - 1}
    assert all(raw[j] == file.byte(j) for j in probes)
    parsed = [tuple(map(int, row.split()[:-1])) for row in raw.splitlines()[1:]]
    checked = 0
    for source in range(16):
        passed, assigned = check_extension(file, source)
        assert all(any(truth(lit, assigned) for lit in row) for row in parsed) == passed
        if solver:
            units = [(i if assigned[i] else -i,) for i in range(4, 4 + file.inputs)]
            assert solver_code(solver, raw, units) == (10 if passed else 20)
            if passed:
                # Exclude its full completed assignment while keeping its inputs.
                block = tuple(-i if bit else i for i, bit in assigned.items())
                assert solver_code(solver, raw, [*units, block]) == 20
                checked += 1

    # The indexed circuit can only ask for K consecutive replies in one high row.
    probes_by_gate = []
    table = BlockTemplate(tuple(range(4, 12)), 12, lambda a: probes_by_gate.append(a) or bool(a.bit_count() % 2))
    dynamic_gates = 0
    for gate in range(table.size):
        probes_by_gate.clear()
        table.gate(gate)
        if probes_by_gate:
            high = gate - table.row_tests
            assert probes_by_gate == list(range(high * table.low_rows, (high + 1) * table.low_rows))
            dynamic_gates += 1
    assert dynamic_gates == table.high_rows
    print(f'{cases} relation/input pairs, {len(probes)} physical byte queries, {dynamic_gates} indexed row masks')
    print(f'Four-bit shared-input file has {file.variables} variables and {file.clause_count} proper clauses')
    if solver:
        print(f'CaDiCaL checked 16 fixed inputs and blocked the full unique extension on each of {checked} positives')


def audit_threshold():
    good, baseline, damaged = (guarded_dimacs(checks) for checks in ([], [False], [False, False]))
    sizes = tuple(map(len, (good, baseline, damaged)))
    assert sizes[0] < sizes[1] < sizes[2] and len(models(good)) == 1 and not models(baseline)
    trials = queries = 0
    for first, second, index in product(range(2), repeat=3):
        # A deterministic source makes two stores, reads its given address and accepts iff it reads one.
        positive = bool((first, second)[index])
        presentations = []
        for claim, order, inverse in product(range(2), permutations(range(3)), permutations(range(3))):
            chronological = [(0, 0, 0, first), (1, 1, 0, second), (index, 2, claim, claim)]
            sorted_rows = [chronological[i] for i in order]
            defects = [not ok for ok in trace_checks(chronological, sorted_rows, order, inverse, claim)]
            for flag in (False, True):
                actual = baseline if not flag else (damaged if any(defects) else good)
                presentations.append((flag, actual))
                for k in range(sizes[0] - 1, sizes[2] + 1):
                    # This existential test of strict > requires at most one fault at a middle threshold.
                    larger = sizes[1] > k if not flag else (k < sizes[0] or (k < sizes[2] and any(defects)))
                    assert larger == (len(actual) > k)
                    queries += 1
                trials += 1
        shortest = min(len(raw) for _, raw in presentations)
        for flag, raw in presentations:
            if len(raw) == shortest:
                assert raw == (good if flag else baseline)
                assert len(models(raw)) == int(positive)
    print(f'{trials} trace/flag presentations, {queries} strict-threshold checks; both minimum-file verdicts verified')


def native_word_map(a, width):
    """Public-address word program with stores, modular arithmetic and bitwise operations."""
    mask = (1 << width) - 1
    private = [0] * 8
    for step in range(24):
        slot = step % len(private)
        private[slot] = (a * (2 * step + 1) + 3) & mask
        a = (private[slot] ^ ((private[(slot + 3) % len(private)] << 1) & mask)) & mask
    return a


def audit_triangular(solver):
    width = 4
    mask = (1 << width) - 1
    ports = []
    predicates = []
    checks = 0
    for j in range(1, width + 1):
        ports.append([*range(4, 4 + j), 4 + width + j - 1])
        for a, b in product(range(1 << width), repeat=2):
            if (a - b) % (1 << j) == 0:
                assert (native_word_map(a, width) - native_word_map(b, width)) % (1 << j) == 0
                checks += 1

        def output_bit(tuple_bits, j=j):
            low = tuple_bits % (1 << j)
            expected = native_word_map(low, width) >> (j - 1) & 1
            return expected == (tuple_bits >> j)

        predicates.append(output_bit)
    file = new_file(2 * width, ports, predicates)
    raw = file.materialize()
    positives = 0
    for pair in range(1 << (2 * width)):
        passed, assigned = check_extension(file, pair)
        assert passed == (pair >> width == native_word_map(pair & mask, width))
        if solver:
            units = [(i if assigned[i] else -i,) for i in range(4, 4 + file.inputs)]
            assert solver_code(solver, raw, units) == (10 if passed else 20)
            if passed:
                exclusion = tuple(-i if bit else i for i, bit in assigned.items())
                assert solver_code(solver, raw, [*units, exclusion]) == 20
        positives += passed
    assert positives == 1 << width
    print(f'{checks} congruences and 256 pairs for a four-bit native transition; {positives} uniquely completed graph rows')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='optional CaDiCaL binary accepting DIMACS on stdin')
    solver = parser.parse_args().solver
    audit_blocks(solver)
    audit_triangular(solver)
    audit_threshold()
