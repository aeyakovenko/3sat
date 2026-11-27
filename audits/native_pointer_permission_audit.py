"""A bit-RAM certificate for two ordinary DIMACS files at every width h >= 11.

The first half of the B=2^h memory bits holds the file, least significant
bit first in each byte. The sign character starts at A=B/2-8*len(TAIL).
The scratch bit Q=B-1-A is in the other half. Registers start at zero.
The two files differ only at the sign character. This program decides this
promise family; on other files it merely inspects the same physical bit.

All-width induction: by tick 6 the branch knows the sign and P=Q. At tick
7 either store has pinned memory[Q]. The following jump and clear leave the
sign only in memory. For 0 <= j < B/8, tick 9+2*j starts the addition with
X=8*j. Its result is nonzero exactly for j < B/8-1. Thus the loop leaves
X=0 at tick B/4+9, and the final indirect load recovers the sign. No store
aliases A. Unmentioned memory cells and dead registers may vary arbitrarily.
All guards and equalities in the certificate are synchronous digit predicates:
for the two loop phases substitute X=4*t-36 or X=4*t-32 modulo B.
Comparisons to B/4+c and B/2+c use the top two bits and a fixed carry.
The finite tests below exercise these claims on actual bit arrays.
"""

from dataclasses import dataclass
from itertools import product


TAIL = b"-4 -2 -3 0\n"
# Seven clauses force variables 1, 2 and 3 true. The next forces variable
# 4 true as well. Either choice for the final clause is distinct from these.
PREFIX = b"p cnf 4 9\n" + b"".join(
    (" ".join(str(-i if negative else i) for i, negative in enumerate(signs, 1))
     + " 0\n").encode("ascii")
    for signs in product((False, True), repeat=3)
    if signs != (True, True, True)
) + b"4 -1 -2 0\n"

# Both store paths take two ticks. Constant addition and one's complement
# use the current word modulus; LOAD and STORE address one memory bit.
PROGRAM = (
    ("ONES",),                      # 0: P := all ones
    ("HALVE",),                     # 1: P := P >> 1
    ("PADD", 1 - 8 * len(TAIL)),    # 2: P := sign bit address
    ("LOAD",),                     # 3: X := memory[P]
    ("COMPLEMENT",),               # 4: P := complement P
    ("JZ", 8),                     # 5
    ("STORE", 1),                  # 6
    ("JMP", 10),                   # 7
    ("STORE", 0),                  # 8
    ("JMP", 10),                   # 9
    ("CLEAR",),                    # 10
    ("XADD", 8),                   # 11
    ("JNZ", 11),                   # 12
    ("LOAD",),                     # 13
    ("JZ", 16),                    # 14
    ("HALT", False),               # 15
    ("HALT", True),                # 16
)


def file_for(capacity, sign):
    last = TAIL if sign else b" " + TAIL[1:]
    padding = capacity // 16 - len(PREFIX) - len(last)
    assert padding >= 0
    return PREFIX + b" " * padding + last


def models(data):
    lines = data.decode("ascii").splitlines()
    assert lines[0].split() == ["p", "cnf", "4", "9"]
    clauses = [list(map(int, line.split())) for line in lines[1:]]
    assert len(clauses) == len({frozenset(clause[:3]) for clause in clauses}) == 9
    for clause in clauses:
        assert len(clause) == 4 and clause[-1] == 0
        names = {abs(literal) for literal in clause[:3]}
        assert len(names) == 3 and names <= {1, 2, 3, 4}
    return [
        values for values in product((False, True), repeat=4)
        if all(any(values[abs(lit) - 1] == (lit > 0) for lit in clause[:3])
               for clause in clauses)
    ]


def run(program, data, capacity):
    memory = bytearray(capacity // 8)
    memory[:len(data)] = data
    pc = p = x = 0
    for tick in range(capacity):
        op, *args = program[pc]
        if op == "HALT":
            return args[0], tick
        target = pc + 1
        if op == "ONES":
            p = capacity - 1
        elif op == "HALVE":
            p >>= 1
        elif op == "PADD":
            p = (p + args[0]) % capacity
        elif op == "COMPLEMENT":
            p ^= capacity - 1
        elif op == "LOAD":
            x = (memory[p // 8] >> (p % 8)) & 1
        elif op == "STORE":
            bit = 1 << (p % 8)
            memory[p // 8] = (memory[p // 8] & ~bit) | (args[0] << (p % 8))
        elif op == "CLEAR":
            x = 0
        elif op == "XADD":
            x = (x + args[0]) % capacity
        elif op == "JMP" or op == "JZ" and x == 0 or op == "JNZ" and x != 0:
            target = args[0]
        else:
            assert op in ("JZ", "JNZ")
        pc = target
    raise AssertionError("deadline exceeded")


@dataclass
class Permission:
    pc: int
    p: int | None                  # None permits every word
    x: int | None
    memory: dict[int, int]         # every unmentioned address permits both bits


def permission(tick, capacity, sign):
    address = capacity // 2 - 8 * len(TAIL)
    scratch = capacity - 1 - address
    loop_end = 9 + capacity // 4
    memory = {}
    if tick <= 3:
        memory[address] = sign
    if tick >= 7:
        memory[scratch] = sign
    if tick < 9:
        pc = (0, 1, 2, 3, 4, 5, 6 if sign else 8, 7 if sign else 9, 10)[tick]
    elif tick < loop_end:
        pc = 11 + (tick - 9) % 2
    elif tick < loop_end + 2:
        pc = 13 + (tick - loop_end)
    else:
        pc = 15 if sign else 16
    if tick == 0 or tick > loop_end:
        p = None
    elif tick < 5:
        p = (capacity - 1, capacity // 2 - 1, address, address)[tick - 1]
    else:
        p = scratch
    if tick <= 3 or tick >= loop_end + 2:
        x = None
    elif tick <= 8 or tick == loop_end + 1:
        x = sign
    elif tick <= loop_end:
        x = ((tick - 9 + (tick - 9) % 2) * 4) % capacity
    return Permission(pc, p, x, memory)


def allows(word, value):
    return word is None or word == value


def check_word(wanted, possibilities):
    if wanted is not None:
        assert possibilities == {wanted}, "register permission"


def check_transition(program, before, after, capacity):
    """Project the instruction over every permitted source, including aliases."""
    op, *args = program[before.pc]
    p, x = before.p, before.x
    ps = None if p is None else {p}
    xs = None if x is None else {x}
    pcs = {before.pc + 1}
    if op == "ONES":
        ps = {capacity - 1}
    elif op == "HALVE":
        ps = None if p is None else {p // 2}
    elif op in ("PADD", "COMPLEMENT"):
        if p is not None:
            ps = {(p + args[0]) % capacity} if op == "PADD" else {capacity - 1 - p}
    elif op == "LOAD":
        if p is None:
            xs = set(before.memory.values())
            if len(before.memory) < capacity:
                xs.update((0, 1))
        else:
            xs = {before.memory[p]} if p in before.memory else {0, 1}
    elif op == "CLEAR":
        xs = {0}
    elif op == "XADD":
        xs = None if x is None else {(x + args[0]) % capacity}
    elif op in ("JZ", "JNZ"):
        possible_zero = {True, False} if x is None else {x == 0}
        pcs = {args[0] if zero == (op == "JZ") else before.pc + 1
               for zero in possible_zero}
    elif op == "JMP":
        pcs = {args[0]}
    elif op == "HALT":
        pcs = {before.pc}
    else:
        assert op == "STORE"
    assert pcs == {after.pc}, "control permission"
    check_word(after.p, ps)
    check_word(after.x, xs)
    for address, required in after.memory.items():
        possible = set()
        if op == "STORE" and allows(p, address):
            possible.add(args[0])
        if op != "STORE" or p != address:
            if address in before.memory:
                possible.add(before.memory[address])
            else:
                possible.update((0, 1))
        assert possible == {required}, "memory permission"


def check_initial(state, data):
    assert state.pc == 0 and allows(state.p, 0) and allows(state.x, 0)
    for address, required in state.memory.items():
        bit = (data[address // 8] >> (address % 8)) & 1 if address < 8 * len(data) else 0
        assert bit == required, "input permission"


def must_reject(test, expected):
    try:
        test()
    except AssertionError as error:
        assert str(error) == expected, (str(error), expected)
    else:
        raise AssertionError(f"fault passed: {expected}")


def main():
    transitions = 0
    for h in range(11, 16):
        capacity = 1 << h
        for sign in (0, 1):
            data = file_for(capacity, sign)
            assert models(data) == ([] if sign else [(True, True, True, True)])
            verdict, halt = run(PROGRAM, data, capacity)
            assert verdict == (not sign) and halt == capacity // 4 + 11
            prev = permission(0, capacity, sign)
            check_initial(prev, data)
            for tick in range(1, capacity):
                curr = permission(tick, capacity, sign)
                check_transition(PROGRAM, prev, curr, capacity)
                prev = curr
            assert PROGRAM[prev.pc] == ("HALT", verdict)
            transitions += capacity - 1

            must_reject(lambda: check_initial(permission(0, capacity, 1 - sign), data),
                        "input permission")
            weak = permission(3, capacity, sign)
            weak.memory.clear()
            must_reject(lambda: check_transition(PROGRAM, weak, permission(4, capacity, sign),
                                                 capacity), "register permission")
            broken = list(PROGRAM)
            store = 6 if sign else 8
            broken[store] = ("STORE", 1 - sign)
            assert run(broken, data, capacity)[0] != verdict
            must_reject(lambda: check_transition(broken, permission(6, capacity, sign),
                                                 permission(7, capacity, sign), capacity),
                        "memory permission")
    print(f"10 proper DIMACS files; {transitions:,} projected native transitions; "
          "30 rejected faults; all checks passed")


if __name__ == "__main__":
    main()
