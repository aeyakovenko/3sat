"""Exhaustive two-address test of the native separator proof on four instructions."""

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Row:
    before: int
    load: bool
    address: int
    value: int
    after: int
    anchor: int | None = None


def instruction(op, register, memory, reply=None):
    # Both load opcodes and both stores use the current register as an address bit.
    if op < 2:
        address = register ^ op
        anchor, value = memory[address]
        if reply is not None:
            value = reply
        return Row(register, True, address, value, value, anchor)
    return Row(register, False, register, op - 2, register)


def real_run(program):
    memory = [(None, 0), (None, 0)]
    register = 0
    rows = []
    for time, op in enumerate(program):
        row = instruction(op, register, memory)
        if not row.load:
            memory[row.address] = (time, row.value)
        register = row.after
        rows.append(row)
    return rows


def possible_anchors(rows, time, forbid_different=True):
    """Try each previously matching write and the zero-initialization sentinel."""
    row = rows[time]
    history = [(j, r.value) for j, r in enumerate(rows[:time])
               if not r.load and r.address == row.address]
    candidates = [j for j, value in history if value == row.value]
    if row.value == 0:
        candidates.append(None)
    if not forbid_different:
        return candidates
    return [j for j in candidates
            if all(value == row.value for k, value in history if j is None or j < k)]


def layouts(length):
    # -1 is the cut set. Noncut neighbours are in the same component.
    for groups in product((-1, 0, 1), repeat=length):
        if all(a == b or -1 in (a, b) for a, b in zip(groups, groups[1:])):
            yield groups


def certificate_rows(program, groups, cut_data):
    banks = [[(None, 0), (None, 0)] for _ in range(2)]
    rows = []
    for t, (op, owner) in enumerate(zip(program, groups)):
        before = rows[-1].after if rows else 0
        if owner == -1:
            before, reply = cut_data[t]
            row = instruction(op, before, banks[0], reply)
        else:
            row = instruction(op, before, banks[owner])
        if not row.load:
            for bank_id, bank in enumerate(banks):
                if owner in (-1, bank_id):
                    bank[row.address] = (t, row.value)
        rows.append(row)
    return rows


def layout_covers(real, groups, allow_equal):
    for t, row in enumerate(real):
        if not row.load or groups[t] == -1:
            continue
        anchors = possible_anchors(real, t) if allow_equal else [row.anchor]
        if not any(s is None or groups[s] in (-1, groups[t]) for s in anchors):
            return False
    return True


def passes(rows, groups, strict):
    for t, row in enumerate(rows):
        if row.before != (rows[t-1].after if t else 0):
            return False
        if row.load:
            anchors = possible_anchors(rows, t, forbid_different=strict)
            # Cut records may guess any named source. Component replay fixes its source.
            if (not anchors if groups[t] == -1 else row.anchor not in anchors):
                return False
    return True


def observable(rows):
    return [(r.before, r.address, r.value, r.after) for r in rows]


def main():
    certificates = strengthened = false_without_guard = 0
    honest_layouts = 0
    example = None
    for program in product(range(4), repeat=4):
        real = real_run(program)
        for groups in layouts(len(program)):
            cut_times = [t for t, owner in enumerate(groups) if owner == -1]
            covers = layout_covers(real, groups, allow_equal=True)
            honest_layouts += covers
            strengthened += covers and not layout_covers(real, groups, allow_equal=False)
            if covers:
                genuine_data = {t: (real[t].before, real[t].value) for t in cut_times}
                built = certificate_rows(program, groups, genuine_data)
                assert observable(built) == observable(real) and passes(built, groups, True)
            guesses = [tuple(product(range(2), range(2) if program[t] < 2 else (0,)))
                       for t in cut_times]
            for choices in product(*guesses):
                built = certificate_rows(program, groups, dict(zip(cut_times, choices)))
                certificates += 1
                if observable(built) == observable(real):
                    continue
                assert not passes(built, groups, True)
                if passes(built, groups, False) and built[-1].after != real[-1].after:
                    false_without_guard += 1
                    if example is None:
                        example = (program, groups, choices)
    assert strengthened > 0 and false_without_guard > 0
    print(f"{certificates} candidate certificates, {honest_layouts} covered genuine layouts")
    print(f"{strengthened} genuine layouts covered only with same-value anchors")
    print(f"{false_without_guard} wrong final registers pass if intervening different writes are ignored")
    print(f"First such (program, layout, cut guesses): {example}")


if __name__ == "__main__":
    main()
