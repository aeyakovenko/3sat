"""Replay tagged and concrete separate-opcode RAM traces across a common disclosure cut."""

from dataclasses import dataclass, field
from itertools import product
from random import Random

from sparse_edit_clock_audit import layout


@dataclass(frozen=True)
class Operand:
    kind: str
    value: int


def reg(i):
    return Operand('register', i)


def literal(x):
    return Operand('word', x)


def site(j):
    return Operand('tag', j)


def physical(x, assignment):
    return assignment[x.value] if x.kind == 'tag' else x.value


def binary(op, a, b, modulus):
    if op == 'add':
        return (a + b) % modulus
    if op == 'mul':
        return (a * b) % modulus
    if op == 'xor':
        return a ^ b
    if op == 'and':
        return a & b
    if op == 'eq':
        return int(a == b)
    if op == 'lt':
        return int(a < b)
    raise ValueError(op)


@dataclass(frozen=True)
class Guard:
    operation: str
    x: Operand
    y: Operand
    output: int

    def scope(self):
        return frozenset(a.value for a in (self.x, self.y) if a.kind == 'tag')

    def accepts(self, assignment, modulus):
        if self.operation == 'same':
            return physical(self.x, assignment) == self.output
        return binary(self.operation, physical(self.x, assignment), physical(self.y, assignment), modulus) == self.output


@dataclass
class Machine:
    memory: dict
    registers: dict = field(default_factory=dict)
    exposure: set = field(default_factory=set)
    writes: set = field(default_factory=set)

    def clone(self):
        return Machine(dict(self.memory), dict(self.registers), set(self.exposure), set(self.writes))


def initial(points, with_tags):
    return Machine({k: site(k) if with_tags else literal(v) for k, v in enumerate(points)})


def execute(machine, instructions, assignment, modulus, with_tags):
    events, guards = [], []
    for op, dest, left, right in instructions:
        def get(arg):
            return machine.registers.get(arg.value, literal(0)) if arg.kind == 'register' else arg

        def record(guard):
            if with_tags and guard.scope():
                guards.append(guard)

        x, y = get(left), get(right)
        a, b = physical(x, assignment), physical(y, assignment)
        if op == 'load':
            record(Guard('same', x, literal(0), a))
            machine.registers[dest] = machine.memory.get(a, literal(0))
            if a not in machine.writes:
                machine.exposure.add(a)
            events.append((op, a))
        elif op == 'store':
            record(Guard('same', x, literal(0), a))
            machine.memory[a] = y
            machine.writes.add(a)
            events.append((op, a))
        elif op == 'copy':
            machine.registers[dest] = x
            events.append((op,))
        else:
            operation = op[1:] if op.startswith('?') else op
            value = binary(operation, a, b, modulus)
            record(Guard(operation, x, y, value))
            if not op.startswith('?'):
                machine.registers[dest] = literal(value)
            # The allocation of a branch's successors can be arbitrary; a
            # fixed path is exactly replayed when the logged outcome agrees.
            events.append((op, value))
    return events, guards


def pins(machine, center):
    return [Guard('same', tag, literal(0), center) for tag in machine.registers.values() if tag.kind == 'tag']


def free_components(m, guards):
    graph = [set() for _ in range(m)]
    edges = []
    marks = set()
    for g in guards:
        scope = sorted(g.scope())
        if len(scope) == 1:
            marks.add(scope[0])
        elif len(scope) == 2:
            a, b = scope
            graph[a].add(b)
            graph[b].add(a)
            edges.append((a, b))
    remaining = set(range(m))
    free = []
    while remaining:
        stack = [next(iter(remaining))]
        component = set()
        while stack:
            j = stack.pop()
            if j in component:
                continue
            component.add(j)
            stack.extend(graph[j] - component)
        remaining -= component
        edge_count = sum(a in component for a, _ in edges)
        if not marks.intersection(component) and edge_count == len(component) - 1:
            free.append(sorted(component))
    return free


def alternatives(m, alphabet, guards, modulus):
    center = alphabet[2]
    base = [center] * m
    blocks = []
    for component in free_components(m, guards):
        relevant = [g for g in guards if g.scope() & set(component)]
        for settings in product(alphabet, repeat=len(component)):
            if all(x == center for x in settings):
                continue
            trial = base.copy()
            for j, x in zip(component, settings, strict=True):
                trial[j] = x
            if all(g.accepts(trial, modulus) for g in relevant):
                blocks.append(list(zip(component, settings, strict=True)))
                break
        else:
            raise AssertionError(('free component had no perturbation', component, relevant))
    cube = []
    for mask in range(1 << len(blocks)):
        assignment = base.copy()
        for k, block in enumerate(blocks):
            if mask >> k & 1:
                for j, x in block:
                    assignment[j] = x
        assert all(g.accepts(assignment, modulus) for g in guards)
        cube.append(assignment)
    return cube


def load(dst, addr):
    return 'load', dst, addr, literal(0)


def copy(dst, arg):
    return 'copy', dst, arg, literal(0)


def store(addr, payload):
    return 'store', 0, addr, payload


def program(m, center, rng):
    order = list(range(m))
    rng.shuffle(order)
    prefix = []
    alias_base = 128
    for j in order[:-1]:
        prefix.extend((load(0, literal(j)), store(literal(alias_base+j), reg(0))))
        # Vary which prior observations constrain pairs and which stores are dead.
        if rng.randrange(4) == 0:
            prefix.extend((load(1, literal(rng.choice(order[:-1]))),
                           (rng.choice(('add', 'xor', 'and', '?eq')), 1, reg(0), reg(1))))
    # Complete first disclosure exactly at the designated cut.
    prefix.extend((copy(1, literal(0)), load(0, literal(order[-1]))))
    # A later read of this overwritten address only forwards a known tag.
    first = rng.choice(order[:-1])
    second = rng.choice(order[:-1])
    suffix = [load(1, literal(first)), load(2, literal(second)), store(reg(1), reg(2)),
              load(2, reg(1)), ('add', 1, reg(0), reg(2))]
    for j in rng.sample(order, len(order)):
        addr = rng.choice((j, alias_base+j))
        suffix.extend((load(0, literal(addr)), ('?eq', 0, reg(0), literal(center))))
    return prefix, suffix


def audit():
    rng = Random(2811)
    width = 128
    _, _, alphabet = layout(width)
    modulus, center, m = 1 << width, alphabet[2], 6
    base = [center]*m
    # With one frozen raw tag already at the common address, three suffix
    # instructions can discover and constrain two formerly free components.
    sharp_prefix = [load(0, literal(0)), store(literal(center), reg(0))]
    sharp_prefix.extend(load(0, literal(j)) for j in range(1, m))
    sharp_suffix = [load(0, literal(1)), load(1, reg(0)),
                    ('?eq', 0, reg(1), literal(center))]
    initial_machine = initial(base, True)
    _, fixed = execute(initial_machine, sharp_prefix, base, modulus, True)
    fixed += pins(initial_machine, center)
    _, extra = execute(initial_machine, sharp_suffix, base, modulus, True)
    assert len(free_components(m, fixed)) == m-1
    assert len(free_components(m, fixed+extra)) == m-3
    prefixes = suffixes = fibers = witnessed = 0
    for _ in range(160):
        roster = [program(m, center, rng) for _ in range(1+rng.randrange(3))]
        current_guards = []
        tracked = []
        for body, tail in roster:
            machine = initial(base, True)
            path, guards = execute(machine, body, base, modulus, True)
            assert set(range(m)) <= machine.exposure
            current_guards.extend(guards + pins(machine, center))
            tracked.append((machine, path, tail))
            prefixes += 1
        d = len(free_components(m, current_guards))
        # Every actual machine keeps identical controllers on the whole product;
        # its cells may still contain independent old tags.
        for assignment in alternatives(m, alphabet, current_guards, modulus):
            for (body, _), (frozen, path, _) in zip(roster, tracked, strict=True):
                actual = initial(assignment, False)
                logged, _ = execute(actual, body, assignment, modulus, False)
                assert logged == path
                assert actual.registers == {i: literal(physical(x, base)) for i, x in frozen.registers.items()}
                assert actual.memory == {i: literal(physical(x, assignment)) for i, x in frozen.memory.items()}
            fibers += 1
        added = []
        budgets = []
        for frozen, _, tail in tracked:
            before = len(free_components(m, current_guards + added))
            for steps in range(len(tail)+1):
                _, extra = execute(frozen.clone(), tail[:steps], base, modulus, True)
                after = len(free_components(m, current_guards + added + extra))
                assert 0 <= before - after <= (steps + 1)//2, (before, after, steps)
                suffixes += 1
            t = rng.randrange(len(tail)+1)
            _, extra = execute(frozen.clone(), tail[:t], base, modulus, True)
            budgets.append(t)
            added.extend(extra)
        remaining = len(free_components(m, current_guards+added))
        assert remaining >= d-sum((t+1)//2 for t in budgets)
        for assignment in alternatives(m, alphabet, current_guards+added, modulus):
            for (body, tail), t in zip(roster, budgets, strict=True):
                reference = initial(base, False)
                other = initial(assignment, False)
                instructions = body + tail[:t]
                a, _ = execute(reference, instructions, base, modulus, False)
                b, _ = execute(other, instructions, assignment, modulus, False)
                assert a == b
            witnessed += 1
    print(f'{prefixes} fully disclosed prefixes, {fibers} common frozen-state experiments, '
          f'{suffixes} suffix-budget inequalities, {witnessed} common extended paths.')


if __name__ == '__main__':
    audit()
