"""Check deferred slot placement and exact handoffs on finite equality paths."""

from copy import deepcopy
from dataclasses import dataclass
from itertools import permutations, product


def records(left, right, group_size):
    rows = []
    for start in range(0, len(left), group_size):
        for side, symbols in enumerate((left, right)):
            for i in range(start, start + group_size):
                rows.append((i, side, symbols[i]))
    return rows


def disconnected_pins(rows):
    length = len(rows) // 2
    graph = {}
    for i, side, value in rows:
        a, b = i + side, (i, value)
        graph.setdefault(a, []).append(b)
        graph.setdefault(b, []).append(a)
    reached = {0}
    todo = [0]
    while todo:
        for v in graph[todo.pop()]:
            if v not in reached:
                todo.append(v)
                reached.add(v)
    return length not in reached


@dataclass
class Registers:
    low: int
    high: int
    reverse: bool = False
    pending: tuple | None = None


def advance(reg, work, lookup, discoveries):
    """An adaptive scan of fresh slots, cut immediately after a specified load."""
    for _ in range(discoveries):
        if reg.pending is not None:
            i, side, value = reg.pending
            work[i, side] = value
        if reg.reverse:
            slot = reg.high
            reg.high -= 1
        else:
            slot = reg.low
            reg.low += 1
        row = lookup(slot)
        reg.reverse = bool((sum(row) + slot) % 2)
        reg.pending = row


def finish(reg, work, lookup, length):
    advance(reg, work, lookup, max(0, reg.high - reg.low + 1))
    i, side, value = reg.pending
    work[i, side] = value
    # Make actual revisits to a data-dependent parity class of the physical slots.
    for slot in range(int(reg.reverse), 2 * length, 2):
        i, side, value = lookup(slot)
        assert work[i, side] == value
    return any(work[i, 0] != work[i, 1] for i in range(length))


def handoff(left, right, group_size, group):
    length = len(left)
    rows = records(left, right, group_size)
    assigned = {}

    def disclose(slot):
        if slot not in assigned:
            assigned[slot] = rows[len(assigned)]
        return assigned[slot]

    reg = Registers(0, 2 * length - 1)
    # Nonzero initial words make writes of zero genuine clear operations.
    work = {(i, side): 1 for i in range(length) for side in (0, 1)}
    start = 2 * group * group_size
    advance(reg, work, disclose, start)
    earlier = assigned.copy()
    baseline = work.copy()
    advance(reg, work, disclose, group_size)
    boundary = len(assigned)
    alice_slots = assigned.keys() - earlier.keys()
    alice_contents = {slot: assigned[slot] for slot in alice_slots}
    changed = {address: value for address, value in work.items() if value != baseline[address]}
    bob_work = baseline | changed
    assert bob_work == work
    bob_reg = deepcopy(reg)
    true_verdict = finish(reg, work, disclose, length)
    novel = {}
    returned = {}

    def bob_lookup(slot):
        if slot in earlier:
            return earlier[slot]
        if slot in alice_slots:
            if slot not in returned:
                returned[slot] = alice_contents[slot]
            return returned[slot]
        if slot not in novel:
            novel[slot] = rows[boundary + len(novel)]
        return novel[slot]

    assert finish(bob_reg, bob_work, bob_lookup, length) == true_verdict == (left != right)
    assert earlier | alice_contents | novel == assigned
    assert disconnected_pins(list(assigned.values())) == true_verdict
    static_work = {(i, side): 1 for i in range(length) for side in (0, 1)}
    assert finish(Registers(0, 2 * length - 1), static_work, assigned.__getitem__, length) == true_verdict
    return len(changed), len(returned)


def cycle_signs():
    checked = 0
    for n in (4, 8):
        k = n // 2
        for tail in permutations(range(1, n)):
            order = (0,) + tail
            x = z = 0
            for vertex in order:
                if vertex < k:
                    x ^= 1
                else:
                    z ^= x
            ranks = sum(i for i, v in enumerate(order) if v < k)
            assert z == (k * (n - 1) - ranks - k * (k - 1) // 2) % 2
            checked += 1
    return checked


def main():
    tests = changes = returns = 0
    h = size = 2
    for group in range(h):
        for fixed, x, y in product(product(range(3), repeat=size), repeat=3):
            left, right = (x + fixed, y + fixed) if group == 0 else (fixed + x, fixed + y)
            diff, revisits = handoff(left, right, size, group)
            changes += diff
            returns += revisits
            tests += 1
    assert changes and returns
    print(f"{tests} complete deferred placements, static replays, and cut reconstructions; "
          f"{changes} changed cells and {returns} distinct returns in tested cuts.")
    print(f"{cycle_signs()} fixed-start cycles checked for the bipartition formula.")


if __name__ == "__main__":
    main()
