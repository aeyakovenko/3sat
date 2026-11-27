"""Audit a lane-local bitonic/Tseitin preprocessing of small 3-CNFs."""
from collections import defaultdict
from itertools import combinations_with_replacement, product


def stages(lanes):
    network = []
    size = 2
    while size <= lanes:
        gap = size // 2
        while gap:
            network.append((size, gap))
            gap //= 2
        size *= 2
    return network


class Layout:
    def __init__(self):
        self.owner = [None]
        self.clauses = defaultdict(list)
        self.gates = []
        self.outputs = {}
        self.occurrences = {}

    def wire(self, block):
        self.owner.append(block)
        return len(self.owner) - 1

    def clause(self, block, *literals):
        assert 1 <= len(literals) <= 3
        self.clauses[block].append(literals + (literals[-1],) * (3 - len(literals)))

    def gate(self, block, op, *inputs):
        z = self.wire(block)
        self.gates.append((z, op, inputs))
        emit = lambda *lits: self.clause(block, *lits)
        if op == 'pin':
            emit(z if inputs[0] else -z)
        elif op == 'and':
            a, b = inputs
            emit(-a, -b, z)
            emit(a, -z)
            emit(b, -z)
        elif op == 'or':
            a, b = inputs
            emit(a, b, -z)
            emit(-a, z)
            emit(-b, z)
        elif op == 'xor':
            a, b = inputs
            emit(-a, -b, -z)
            emit(a, b, -z)
            emit(a, -b, z)
            emit(-a, b, z)
        elif op == 'mux':
            c, a, b = inputs
            emit(-c, -a, z)
            emit(-c, a, -z)
            emit(c, -b, z)
            emit(c, b, -z)
        else:
            raise ValueError(op)
        return z


def compile_formula(formula, universe):
    layout = Layout()
    count = len(formula)
    lanes = 1 << (max(1, 4 * count) - 1).bit_length()
    width = (universe + count + 1).bit_length()
    network = stages(lanes)
    records = []
    for lane in range(lanes):
        block = ('lane', 0, lane)
        j, k = divmod(lane, 4)
        real = j < count and k < 3
        key = abs(formula[j][k]) if real else 0
        record = [layout.gate(block, 'pin', int(not real))]
        record += [layout.gate(block, 'pin', key >> i & 1) for i in reversed(range(width))]
        bit = layout.wire(block) if real else layout.gate(block, 'pin', 0)
        if real:
            layout.occurrences[bit] = (j, k)
        record.append(bit)
        records.append(record)
        for var in record:
            layout.outputs[var] = (0, lane)
    for j, clause in enumerate(formula):
        pins = [records[4*j+k][-1] * (1 if lit > 0 else -1) for k, lit in enumerate(clause)]
        layout.clause(('clause', j), *pins)
    for level, (size, gap) in enumerate(network, start=1):
        updated = []
        for lane, own in enumerate(records):
            block = ('lane', level, lane)
            other = records[lane ^ gap]
            smaller = layout.gate(block, 'pin', 0)
            for a, b in reversed(list(zip(own, other))):
                equal = -layout.gate(block, 'xor', a, b)
                keep = layout.gate(block, 'and', equal, smaller)
                less = layout.gate(block, 'and', -a, b)
                smaller = layout.gate(block, 'or', less, keep)
            take_min = bool(lane & size) == bool(lane & gap)
            select = smaller if take_min else -smaller
            record = [layout.gate(block, 'mux', select, a, b) for a, b in zip(own, other)]
            updated.append(record)
            for var in record:
                layout.outputs[var] = (level, lane)
        records = updated
    for lane, (left, right) in enumerate(zip(records, records[1:])):
        block = ('adjacent', lane)
        match = layout.gate(block, 'and', -left[0], -right[0])
        for a, b in zip(left[1:-1], right[1:-1]):
            match = layout.gate(block, 'and', match, -layout.gate(block, 'xor', a, b))
        layout.clause(block, -match, -left[-1], right[-1])
        layout.clause(block, -match, left[-1], -right[-1])
    return layout, network, lanes, records


def check_incidence(layout, network, lanes):
    exhaustive = defaultdict(set)
    for block, clauses in layout.clauses.items():
        for local, clause in enumerate(clauses):
            for slot, literal in enumerate(clause):
                exhaustive[abs(literal)].add((block, local, slot))
    maximum = 0
    for var, owner in enumerate(layout.owner[1:], start=1):
        candidates = {owner}
        if var in layout.outputs:
            level, lane = layout.outputs[var]
            if level < len(network):
                partner = lane ^ network[level][1]
                candidates.update((('lane', level + 1, lane), ('lane', level + 1, partner)))
            else:
                candidates.update(('adjacent', i) for i in (lane - 1, lane) if 0 <= i < lanes - 1)
        if var in layout.occurrences:
            j, _ = layout.occurrences[var]
            candidates.add(('clause', j))
        slots = [(block, local, slot) for block in sorted(candidates)
                 for local, clause in enumerate(layout.clauses.get(block, ()))
                 for slot, literal in enumerate(clause) if abs(literal) == var]
        assert len(slots) == len(set(slots)) and set(slots) == exhaustive[var]
        local_index = {position: i for i, position in enumerate(slots)}
        for position in exhaustive[var]:
            block, local, slot = slots[local_index[position]]
            assert abs(layout.clauses[block][local][slot]) == var
        maximum = max(maximum, len(candidates))
    return sum(map(len, exhaustive.values())), maximum


def check_semantics(layout, formula, records):
    # One bit per occurrence assignment, including assignments that disagree on repeated IDs.
    count = 1 << (3 * len(formula))
    mask = (1 << count) - 1
    values = [0] * len(layout.owner)
    for var, (j, k) in layout.occurrences.items():
        bit = 3*j+k
        values[var] = sum(1 << case for case in range(count) if case >> bit & 1)

    def literal(i):
        return values[abs(i)] ^ (mask if i < 0 else 0)

    for var, op, inputs in layout.gates:
        if op == 'pin':
            values[var] = mask if inputs[0] else 0
            continue
        parts = [literal(i) for i in inputs]
        if op == 'and':
            values[var] = parts[0] & parts[1]
        elif op == 'or':
            values[var] = parts[0] | parts[1]
        elif op == 'xor':
            values[var] = parts[0] ^ parts[1]
        else:
            c, a, b = parts
            values[var] = (c & a) | ((mask ^ c) & b)
    accepted = mask
    for clauses in layout.clauses.values():
        for a, b, c in clauses:
            accepted &= literal(a) | literal(b) | literal(c)

    literals = [lit for clause in formula for lit in clause]
    variables = sorted(set(map(abs, literals)))
    expected = 0
    for bits in product((0, 1), repeat=len(variables)):
        truth = dict(zip(variables, bits))
        if all(any(truth[abs(lit)] == (lit > 0) for lit in clause) for clause in formula):
            case = sum(truth[abs(lit)] << i for i, lit in enumerate(literals))
            expected |= 1 << case
    assert accepted == expected

    # Inspect the entire final sorting output independently, also on rejected guesses.
    real = len(literals)
    for case in range(count):
        want = sorted([(0, abs(lit), case >> i & 1) for i, lit in enumerate(literals)]
                      + [(1, 0, 0)] * (len(records) - real))
        for record, (dummy, key, bit) in zip(records, want):
            got = 0
            for var in record:
                got = 2*got + (values[var] >> case & 1)
            assert got == (dummy << (len(record)-1)) + 2*key + bit
    return count, accepted.bit_count()


def check_gate_templates():
    checked = 0
    for op, arity in [('pin', 0), ('and', 2), ('or', 2), ('xor', 2), ('mux', 3)]:
        for params in product((False, True), repeat=max(1, arity)):
            for output in (False, True):
                layout = Layout()
                block = ('test',)
                inputs = [layout.wire(block) for _ in range(arity)]
                z = layout.gate(block, op, *(inputs if arity else params))
                env = dict(zip(inputs, params))
                env[z] = output
                satisfied = all(any(env[abs(v)] == (v > 0) for v in clause)
                                for clause in layout.clauses[block])
                expected = {'pin': lambda: params[0], 'and': lambda: all(params),
                            'or': lambda: any(params), 'xor': lambda: params[0] != params[1],
                            'mux': lambda: params[1] if params[0] else params[2]}[op]()
                assert satisfied == (output == expected)
                checked += 1
    return checked


def cases():
    yield (), 1
    for clause in combinations_with_replacement((-2, -1, 1, 2), 3):
        yield (clause,), 2
    for formula in [((1, 1, 1), (-1, -1, -1)), ((7, -1, 7), (-7, 1, -1)),
                    ((-3, -3, 1), (3, 3, -1), (-1, 1, 3)),
                    ((1, 1, 1), (1, 1, 1), (-1, -1, -1)),
                    ((1, -16, 2), (16, 2, 2), (-16, -1, -2), (16, -16, 1))]:
        yield formula, max(abs(lit) for clause in formula for lit in clause)


def main():
    templates = check_gate_templates()
    formulas = guesses = consistent_sat = clauses = slots = variables = max_blocks = 0
    widths = set()
    for formula, universe in cases():
        layout, network, lanes, records = compile_formula(formula, universe)
        incidences, local_blocks = check_incidence(layout, network, lanes)
        count, good = check_semantics(layout, formula, records)
        formulas += 1
        guesses += count
        consistent_sat += good
        clauses += sum(map(len, layout.clauses.values()))
        slots += incidences
        variables += len(layout.owner)-1
        max_blocks = max(max_blocks, local_blocks)
        widths.add(lanes)
    assert slots == 3 * clauses
    print(f'{formulas} formulas; {guesses} occurrence assignments ({consistent_sat} accepted); '
          f'{templates} gate truth/output cases')
    print(f'{variables} variables, {clauses} clauses, {slots} literal slots; '
          f'lanes {sorted(widths)}, maximum {max_blocks} candidate blocks per variable')


if __name__ == '__main__':
    main()
