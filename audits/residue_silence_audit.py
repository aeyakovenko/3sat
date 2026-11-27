"""Compare concrete word bytecode with low residues and optional exact zero tags."""

from collections import deque
from typing import NamedTuple


def assemble(source):
    code, labels = [], {}
    for ins in source:
        if ins[0] == "label":
            labels[ins[1]] = len(code)
        else:
            code.append(ins)
    return tuple((*ins[:-1], labels[ins[-1]]) if ins[0] in ("jz", "jmp") else ins
                 for ins in code)


def threshold(k):
    c, x, z = range(3)
    return assemble([("const", c, 1), *[("double", c, c)] * (k - 1),
                     ("jz", c, "stop"), ("load", x), *[("double", x, x)] * k,
                     ("add", z, x, c), ("jz", z, "pulse"),
                     ("label", "stop"), ("idle",), ("label", "pulse"), ("signal",)])


LOOP = assemble([("const", 0, 1), ("label", "again"), ("double", 1, 0),
                 ("jz", 1, "check"), ("copy", 0, 1), ("jmp", "again"),
                 ("label", "check"), ("jz", 0, "pulse"), ("idle",),
                 ("label", "pulse"), ("signal",)])


def concrete(code, width, loaded):
    """There is at most one load along any path in these programs."""
    modulus = 1 << width
    pc, registers, seen = 0, [0, 0, 0], set()
    while (pc, tuple(registers)) not in seen:
        seen.add((pc, tuple(registers)))
        op, *p = code[pc]
        if op in ("signal", "idle"):
            return op == "signal", seen
        if op == "const":
            registers[p[0]] = p[1] % modulus
        elif op == "load":
            registers[p[0]] = loaded
        elif op == "double":
            registers[p[0]] = 2 * registers[p[1]] % modulus
        elif op == "add":
            registers[p[0]] = (registers[p[1]] + registers[p[2]]) % modulus
        elif op == "copy":
            registers[p[0]] = registers[p[1]]
        elif op == "jmp" or (op == "jz" and registers[p[0]] == 0):
            pc = p[-1]
            continue
        elif op != "jz":
            raise ValueError(op)
        pc += 1
    return False, seen


class Value(NamedTuple):
    residue: int
    zero: bool | None


def abstract(code, width, precision, tagged=False):
    """Only reached tuples are enqueued. A low-zero residue can hide a high bit."""
    mask = (1 << precision) - 1

    def possibilities(value, known_zero=None):
        residue = value & mask
        if not tagged:
            return (Value(residue, None),)
        if residue != 0 or precision == width:
            return (Value(residue, residue == 0),)
        if known_zero is not None:
            return (Value(residue, known_zero),)
        return (Value(0, True), Value(0, False))

    initial = (0, (possibilities(0, True)[0],) * 3)
    pending, seen = deque([initial]), {initial}
    while pending:
        pc, regs = pending.popleft()
        op, *p = code[pc]
        if op in ("idle", "signal"):
            continue
        if op == "jmp":
            following = [(p[0], regs)]
        elif op == "jz":
            v = regs[p[0]]
            if v.zero is not None:
                branches = (v.zero,)
            elif v.residue != 0 or precision == width:
                branches = (v.residue == 0,)
            else:
                branches = (False, True)
            following = [(p[1] if zero else pc + 1, regs) for zero in branches]
        else:
            if op == "const":
                values = possibilities(p[1], p[1] % (1 << width) == 0)
            elif op == "load":
                values = [v for r in range(mask + 1) for v in possibilities(r)]
            elif op == "copy":
                values = (regs[p[1]],)
            elif op == "double":
                a = regs[p[1]]
                values = possibilities(2 * a.residue, True if a.zero is True else None)
            elif op == "add":
                a, b = regs[p[1]], regs[p[2]]
                known = b.zero if a.zero is True else a.zero if b.zero is True else None
                values = possibilities(a.residue + b.residue, known)
            else:
                raise ValueError(op)
            following = [(pc + 1, regs[:p[0]] + (v,) + regs[p[0] + 1:]) for v in values]
        for state in following:
            if state not in seen:
                seen.add(state)
                pending.append(state)
    return any(code[pc][0] == "signal" for pc, _ in seen), seen


def projected(trace, precision, tagged):
    mask = (1 << precision) - 1
    return {(pc, tuple(Value(a & mask, a == 0 if tagged else None) for a in regs))
            for pc, regs in trace}


def main():
    load_cases = threshold_cases = loop_cases = 0
    for width in range(1, 9):
        for k in range(1, 11):
            code = threshold(k)
            trace = set()
            for word in range(1 << width):
                pulse, states = concrete(code, width, word)
                assert not pulse
                trace.update(states)
                load_cases += 1
            for b in range(width + 1):
                pulse, states = abstract(code, width, b)
                assert pulse == (b < width and b < k)
                assert projected(trace, b, False) <= states
                threshold_cases += 1
        pulse, trace = concrete(LOOP, width, 0)
        assert not pulse
        for b in range(width + 1):
            for tagged in (False, True):
                pulse, states = abstract(LOOP, width, b, tagged)
                assert pulse == (not tagged and b < width)
                assert projected(trace, b, tagged) <= states
                if tagged:
                    # PC 1 starts the loop; PC 5 checks a after z compares zero.
                    assert {pc for pc, _ in states} >= {1, 5}
                    assert all(regs[0].zero is False for pc, regs in states if pc in (1, 5))
                loop_cases += 1
    print(f"{load_cases} concrete threshold runs, {threshold_cases} residue threshold cases, "
          f"{loop_cases} loop abstractions; all concrete projections included")


if __name__ == "__main__":
    main()
