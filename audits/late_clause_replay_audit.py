"""Compare last-discovery replay with cold word-RAM runs on actual DIMACS files."""
from dataclasses import dataclass
from itertools import product
from math import ceil, log10, log2

from late_clause_support_audit import models


@dataclass(frozen=True)
class Layout:
    r: int
    count: int
    bits: int = 8192
    variables: int = 3

    @property
    def word_bytes(self):
        return 2 * ceil(48 * log2(self.bits + 2) / 16)

    @property
    def field(self):
        return 1 + ceil(log10(self.bits + 2))

    @property
    def anchors(self):
        return tuple(self.variables + i for i in (1, 2, 3))

    def record(self, clause):
        assert len({abs(x) for x in clause}) == 3
        return (" ".join(f"{x:>{self.field}}" for x in clause) + " 0\n").encode()

    @property
    def prefix(self):
        anchors = self.anchors
        # Forbid each assignment to the anchors except all false.
        clauses = [tuple(-x if b else x for x, b in zip(anchors, bits))
                   for bits in product((False, True), repeat=3) if any(bits)]
        head = f"p cnf {anchors[-1]} {7 + self.r * self.count}\n".encode()
        data = head + b"".join(self.record(c) for c in clauses)
        return data + b" " * (-len(data) % self.word_bytes)

    @property
    def first(self):
        return len(self.prefix) // self.word_bytes

    def packet(self, clauses):
        pad = tuple(-x for x in self.anchors)
        clauses = (*clauses, *((pad,) * (self.r - len(clauses))))
        assert len(clauses) == self.r
        data = b"".join(self.record(c) for c in clauses)
        assert len(data) <= self.word_bytes
        return int.from_bytes(data.ljust(self.word_bytes), "little")

    def pins(self, literals):
        return self.packet([(x, *self.anchors[:2]) for x in literals])

    def file(self, packets):
        body = self.prefix + b"".join(
            x.to_bytes(self.word_bytes, "little") for x in packets)
        assert len(packets) == self.count and 8 * len(body) <= self.bits
        return body.ljust(self.bits // 8)


def file_verdict(data):
    header, *fields = data.splitlines()
    tag, fmt, n, k = header.split()
    assert (tag, fmt) == (b"p", b"cnf")
    numbers = list(map(int, b" ".join(fields).split()))
    assert len(numbers) == 4 * int(k)
    rows = [numbers[i:i + 4] for i in range(0, len(numbers), 4)]
    assert all(z == 0 and len({abs(x), abs(y), abs(w)}) == 3
               and all(1 <= abs(a) <= int(n) for a in (x, y, w))
               for x, y, w, z in rows)
    return bool(models([row[:3] for row in rows], int(n)))


def program(layout, mode):
    """Return a finite word-RAM program specialized to this valid layout."""
    code, labels = [], {}

    def emit(op, *args):
        code.append((op, *args))

    def mark(label):
        labels[label] = len(code)

    # Input, status array and packet-copy array have disjoint address ranges.
    seen, saved, scratch = 64, 96, 128
    count, base = layout.count, layout.first
    emit("set", "remaining", count)
    emit("set", "i", 0)
    mark("discover")
    emit("add", "addr", "i", base)
    emit("load", "word", "addr")
    emit("add", "ptr", "i", saved)
    emit("store", "ptr", "word")
    emit("store", "addr", 0)             # overwrite an already read word
    emit("load", "observed", "addr")     # must see the replacement
    emit("jnz", "observed", "false")
    emit("add", "ptr", "i", seen)
    emit("store", "ptr", 1)
    emit("add", "remaining", "remaining", -1)
    if mode != "normal":
        for pin, bit in ((1, 1), (-1, 2)):
            emit("eq", "same", "word", layout.pins((pin,)))
            emit("mul", "same", "same", bit)
            emit("or", "contradiction", "contradiction", "same")
        emit("eq", "both", "contradiction", 3)
        if mode == "early":
            emit("jnz", "both", "false")
    emit("jz", "remaining", "solve")
    # The sign of the just-read first literal chooses clockwise or anticlockwise.
    emit("shr", "sign", "word", 8 * (layout.field - 2))
    emit("and", "sign", "sign", 255)
    emit("eq", "negative", "sign", 45)
    emit("mul", "direction", "negative", count - 2)
    emit("add", "direction", "direction", 1)
    mark("next")
    emit("add", "i", "i", "direction")
    emit("mod", "i", "i", count)
    emit("add", "ptr", "i", seen)
    emit("load", "used", "ptr")
    emit("jnz", "used", "next")
    if mode == "blind":
        emit("jz", "both", "discover")
        emit("add", "addr", "i", base)
        emit("store", "addr", 717)       # destroys the first unopened original
        emit("load", "observed", "addr")
        emit("store", scratch, "observed")
        emit("halt", 0)
    else:
        emit("jmp", "discover")

    mark("solve")
    emit("set", "assignment", 0)
    mark("trial")
    emit("store", scratch, "assignment")
    emit("store", scratch, "word")       # multiple writes to the same location
    emit("set", "j", 0)
    mark("packet")
    emit("add", "ptr", "j", saved)
    emit("load", "checked", "ptr")
    stride = len(layout.record((1, 2, 3)))
    for row in range(layout.r):
        emit("set", "satisfied", 0)
        for pos in range(3):
            last = row * stride + pos * (layout.field + 1) + layout.field - 1
            emit("shr", "digit", "checked", 8 * last)
            emit("and", "digit", "digit", 255)
            emit("add", "bit", "digit", -49)   # dense variables 1..6
            emit("shr", "value", "assignment", "bit")
            emit("and", "value", "value", 1)
            emit("shr", "sign", "checked", 8 * (last - 1))
            emit("and", "sign", "sign", 255)
            emit("eq", "minus", "sign", 45)
            emit("xor", "value", "value", "minus")
            emit("or", "satisfied", "satisfied", "value")
        emit("jz", "satisfied", "reject_trial")
    emit("add", "j", "j", 1)
    emit("eq", "done", "j", count)
    emit("jz", "done", "packet")
    emit("halt", 1)
    mark("reject_trial")
    emit("add", "assignment", "assignment", 1)
    emit("eq", "done", "assignment", 1 << layout.variables)
    emit("jz", "done", "trial")
    mark("false")
    emit("halt", 0)
    return [(*ins[:-1], labels[ins[-1]]) if ins[0] in ("jmp", "jz", "jnz")
            else ins for ins in code]


class Guest:
    def __init__(self, code, data, width):
        self.code, self.pc, self.steps = code, 0, 0
        self.mask = (1 << (8 * width)) - 1
        self.reg, self.answer = {}, None
        self.mem = {i // width: int.from_bytes(data[i:i + width], "little")
                    for i in range(0, len(data), width)}

    def val(self, x):
        return x if isinstance(x, int) else self.reg.get(x, 0)

    def step(self, log=None):
        op, *args = self.code[self.pc]
        self.pc += 1
        self.steps += 1
        if op == "halt":
            self.answer = bool(self.val(args[0]))
        elif op == "jmp":
            self.pc = args[0]
        elif op in ("jz", "jnz"):
            if bool(self.val(args[0])) == (op == "jnz"):
                self.pc = args[1]
        elif op == "store":
            addr, value = map(self.val, args)
            if log is not None:
                log.append((addr, self.mem.get(addr)))
            self.mem[addr] = value
        elif op == "load":
            self.reg[args[0]] = self.mem.get(self.val(args[1]), 0)
        elif op == "set":
            self.reg[args[0]] = self.val(args[1])
        else:
            a, b = self.val(args[1]), self.val(args[2])
            if op == "add":
                value = a + b
            elif op == "mul":
                value = a * b
            elif op == "mod":
                value = a % b
            elif op == "shr":
                value = a >> b
            elif op == "and":
                value = a & b
            elif op == "or":
                value = a | b
            elif op == "xor":
                value = a ^ b
            elif op == "eq":
                value = int(a == b)
            else:
                raise ValueError(op)
            self.reg[args[0]] = value & self.mask

    def finish(self, log=None):
        while self.answer is None:
            assert self.steps < 100_000
            self.step(log)
        return self.answer, self.steps

    def control(self):
        return self.pc, self.steps, self.reg.copy(), self.answer


def check(layout, data_packets, mode):
    code = program(layout, mode)
    blank = int.from_bytes(b" " * layout.word_bytes, "little")
    guest = Guest(code, layout.file([blank] * layout.count), layout.word_bytes)
    addresses = tuple(range(layout.first, layout.first + layout.count))
    opened = {}
    while guest.answer is None:
        ins = code[guest.pc]
        if ins[0] in ("load", "store"):
            addr = guest.val(ins[2] if ins[0] == "load" else ins[1])
            if addr in addresses and addr not in opened:
                if ins[0] == "store" or len(opened) == len(data_packets):
                    break
                opened[addr] = guest.mem[addr] = data_packets[len(opened)]
        guest.step()
    reason = ("early" if guest.answer is not None else
              "blind" if code[guest.pc][0] == "store" else "normal")
    assert reason == mode
    holes = [a for a in addresses if a not in opened]
    query_addr = holes[0] if reason == "early" else addr
    assert query_addr in holes
    if reason == "normal":
        assert holes == [query_addr]
    remaining = iter(data_packets[len(opened):])
    original = {a: opened[a] if a in opened else next(remaining)
                for a in addresses if a != query_addr}
    for a, data in original.items():
        if a not in opened:
            guest.mem[a] = data

    # The full frozen copy is a test oracle. Replay itself restores only logged stores.
    control, frozen = guest.control(), guest.mem.copy()
    lits = (1, -1, 2, -2, 3, -3)
    lengths, answers, results = set(), set(), 0
    for size in range(layout.r + 1):
        for pins in product(lits, repeat=size):
            query = layout.pins(pins)
            physical = layout.file([query if a == query_addr else original[a] for a in addresses])
            truth = file_verdict(physical)
            cold = Guest(code, physical, layout.word_bytes)
            expected = cold.finish()
            assert expected[0] == truth
            if reason == "normal" or results == 0:
                guest.mem[query_addr] = query
                undo = []
                observed = guest.finish(undo)
                assert observed == expected and guest.reg == cold.reg and guest.mem == cold.mem
                if reason == "normal":
                    assert len(undo) > len({a for a, _ in undo})
                    assert any(old is None for _, old in undo)
                if reason == "blind":
                    assert undo[0] == (query_addr, query) and guest.reg["observed"] == 717
                if reason == "early":
                    assert not undo and guest.answer is False
                for a, old in reversed(undo):
                    if old is None:
                        del guest.mem[a]
                    else:
                        guest.mem[a] = old
                assert guest.mem[query_addr] == query
                guest.mem[query_addr] = frozen[query_addr]
                guest.pc, guest.steps, saved_regs, guest.answer = control
                guest.reg = saved_regs.copy()
                assert guest.mem == frozen and guest.control() == control
                if reason != "normal":
                    representative = expected, cold.control(), cold.mem.copy()
            else:
                result, registers, memory = representative
                assert result == expected and registers == cold.control()
                if reason == "blind":
                    assert memory == cold.mem
                else:
                    assert all(memory[a] == word for a, word in cold.mem.items() if a != query_addr)
            lengths.add(expected[1] - control[1])
            answers.add(truth)
            results += 1
    if reason == "normal":
        assert len(lengths) > 1 and answers == {False, True}
    else:
        assert answers == {False}
    return results, tuple(opened), lengths


def main():
    totals = {"normal": 0, "early": 0, "blind": 0}
    suffixes = set()
    for r in (1, 2):
        layout = Layout(r, 5)
        orders = set()
        for first in ((1, 2, 3), (-1, 2, 3)):
            data = [layout.packet([first]), layout.pins((3,)),
                    layout.packet([(-1, -2, -3)]), layout.packet([(1, -2, 3)])]
            n, order, lengths = check(layout, data, "normal")
            orders.add(order)
            suffixes.update(lengths)
            totals["normal"] += n
        assert len(orders) == 2
        forced = [layout.pins((1,)), layout.pins((-1,)),
                  layout.packet([(1, 2, 3)]), layout.packet([(-1, -2, -3)])]
        for mode in ("early", "blind"):
            n, _, _ = check(layout, forced, mode)
            totals[mode] += n
    print(f"{totals['normal']} rollback continuations agreed with fresh executions; "
          f"{totals['early']} early-halt and {totals['blind']} blind-store completions agreed.")
    print(f"Genuine suffix clocks ranged from {min(suffixes)} to {max(suffixes)} guest instructions.")


if __name__ == "__main__":
    main()
