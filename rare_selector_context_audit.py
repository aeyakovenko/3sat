"""Check the shared lookup circuit and the sound graph-pruning count."""

from collections import deque
from itertools import product
from math import prod


def pairs(size):
    span = 2
    while span <= size:
        gap = span // 2
        while gap:
            for i in range(size):
                j = i ^ gap
                if j > i:
                    yield i, j, (i & span) == 0
            gap //= 2
        span *= 2


def by_rows(table, addresses):
    rows = [(i, 0, v) for i, v in enumerate(table)]
    rows += [(v, 1, 0) for v in addresses]
    for i, j, ascending in pairs(len(rows)):
        if (rows[i][:2] > rows[j][:2] if ascending else rows[i][:2] < rows[j][:2]):
            rows[i], rows[j] = rows[j], rows[i]
    assert [r[:2] for r in rows] == sorted(r[:2] for r in rows)
    parity = last = 0
    for _, tag, v in rows:
        if tag:
            parity ^= last
        else:
            last = v
    return parity


def negate_assignment(v, value):
    return -v if value else v


class Circuit:
    def __init__(self):
        self.variables = 3
        self.clauses = [tuple(negate_assignment(i, b) for i, b in enumerate(bits, 1))
                        for bits in product(range(2), repeat=3) if any(bits)]
        self.zero, self.one = self.new(), self.new()
        self.clauses.extend([(-self.zero, 1, 2), (self.one, 1, 2)])

    def new(self):
        self.variables += 1
        return self.variables

    def gate(self, op, *inputs):
        z = self.new()
        unique = list(dict.fromkeys(inputs))
        for bits in product(range(2), repeat=len(unique)):
            vals = dict(zip(unique, bits))
            expected = op(*(vals[v] for v in inputs))
            literals = [negate_assignment(v, vals[v]) for v in unique]
            literals.append(z if expected else -z)
            if len(literals) == 2:
                literals.append(1)
            self.clauses.append(tuple(literals))
        return z

    def choose(self, condition, yes, no):
        delta = self.gate(int.__xor__, yes, no)
        masked = self.gate(int.__and__, condition, delta)
        return self.gate(int.__xor__, no, masked)

    def swap(self, a, b, ascending):
        # Address bits are in big-endian order, followed by tag, then payload.
        lhs, rhs = (b, a) if ascending else (a, b)
        less = self.zero
        for x, y in reversed(list(zip(lhs[:-1], rhs[:-1]))):
            lessbit = self.gate(lambda p, q: (1 - p) & q, x, y)
            equal = self.gate(lambda p, q: int(p == q), x, y)
            smaller_tail = self.gate(int.__and__, equal, less)
            less = self.gate(int.__or__, lessbit, smaller_tail)
        return ([self.choose(less, y, x) for x, y in zip(a, b)],
                [self.choose(less, x, y) for x, y in zip(a, b)])


def circuit(t):
    m = 1 << t
    c = Circuit()
    data = [c.new() for _ in range(m)]
    selectors = [[c.new() for _ in range(t)] for _ in range(m)]
    rows = []
    for j, value in enumerate(data):
        addr = [c.one if j >> k & 1 else c.zero for k in reversed(range(t))]
        rows.append([*addr, c.zero, value])
    rows.extend([*addr, c.one, c.zero] for addr in selectors)
    for i, j, ascending in pairs(2 * m):
        rows[i], rows[j] = c.swap(rows[i], rows[j], ascending)
    last = parity = c.zero
    for row in rows:
        tag, payload = row[-2:]
        last = c.choose(tag, last, payload)
        contribution = c.gate(int.__and__, tag, last)
        parity = c.gate(int.__xor__, parity, contribution)
    c.clauses.append((parity, 1, 2))
    return c, data, selectors


def render(c, data, selectors, table, addresses):
    pinvars = data + [v for block in selectors for v in block]
    values = list(table) + [a >> k & 1 for a in addresses
                            for k in reversed(range(len(selectors[0])))]
    count = len(c.clauses) + len(pinvars)
    raw = bytearray(f'p cnf {c.variables} {count}\n', 'ascii')
    for clause in c.clauses:
        raw.extend((' '.join(map(str, clause)) + ' 0\n').encode())
    # Fixed-size field makes the sign cells different native words at these lengths.
    offsets = []
    for v, val in zip(pinvars, values):
        raw.extend(b' ' * 16)
        offsets.append(len(raw))
        raw.extend(((' ' if val else '-') + f'{v} 1 2 0\n').encode())
    width = 16 * (((8 * len(raw) + 1).bit_length() + 15) // 16)
    assert len(set(pos // (width // 8) for pos in offsets)) == len(offsets)
    return raw


def propagated_verdict(raw):
    header, *lines = raw.decode('ascii').splitlines()
    p, cnf, declared, count = header.split()
    assert (p, cnf) == ('p', 'cnf') and len(lines) == int(count)
    clauses = []
    for line in lines:
        a, b, c, zero = map(int, line.split())
        assert zero == 0 and len({abs(a), abs(b), abs(c)}) == 3
        assert 0 < min(map(abs, (a, b, c))) <= max(map(abs, (a, b, c))) <= int(declared)
        clauses.append((a, b, c))
    assert len(set(clauses[:7])) == 7
    assert all({abs(x) for x in clause} == {1, 2, 3} and min(clause) < 0
               for clause in clauses[:7])
    incident = [[] for _ in range(int(declared) + 1)]
    for clause in clauses:
        for literal in clause:
            incident[abs(literal)].append(clause)
    values = {}
    work = deque([-1, -2, -3])
    while work:
        literal = work.popleft()
        v, val = abs(literal), literal > 0
        if v in values:
            if values[v] != val:
                return False
            continue
        values[v] = val
        for clause in incident[v]:
            if any(abs(a) in values and values[abs(a)] == (a > 0) for a in clause):
                continue
            unknown = [a for a in clause if abs(a) not in values]
            if not unknown:
                return False
            if len(unknown) == 1:
                work.append(unknown[0])
    assert all(any(values.get(abs(a)) == (a > 0) for a in clause) for clause in clauses)
    return True


def graph_sets():
    t, s = 3, 2
    attained = set()
    for labels in product(range(t), repeat=s):
        for edges in product(range(s + 2), repeat=2 * s):
            for start in range(s + 2):
                accepted = 0
                for u in range(1 << t):
                    current = start
                    for _ in range(s):
                        if current >= s:
                            break
                        current = edges[2 * current + (u >> labels[current] & 1)]
                    if current == s + 1:
                        accepted |= 1 << u
                attained.add(accepted)
    full = (1 << (1 << t)) - 1
    tables = [v for v in range(full + 1) if v.bit_count() == 4]
    limits = [max(mask.bit_count() for mask in attained
                  if mask & v in (0, mask)) for v in tables]
    assert min(limits) == 0 and limits.count(0) == 2
    return prod((t ** s, (s + 2) ** (2 * s + 1))), len(attained), limits.count(0)


if __name__ == '__main__':
    naive = samples = 0
    for t in (1, 2):
        c, data, selectors = circuit(t)
        for n, (table, addresses) in enumerate(product(product(range(2), repeat=1 << t),
                                              product(range(1 << t), repeat=1 << t))):
            expected = sum(table[i] for i in addresses) % 2
            assert by_rows(table, addresses) == expected
            naive += 1
            if t == 1 or n % 127 == 0:
                assert propagated_verdict(render(c, data, selectors, table, addresses)) == expected
                samples += 1
    print(f'{naive} complete table/selector settings; {samples} parsed proper formulas')
    print('graph codes, distinct acceptance sets, best balanced three-bit tables:', graph_sets())
