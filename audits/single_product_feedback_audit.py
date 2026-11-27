"""Check modular tap collisions and run serial AND/XOR feedback on actual bits."""
from collections import defaultdict
from itertools import combinations_with_replacement, product


def triples(slots, period=None):
    values = [sum(abc) for abc in combinations_with_replacement(slots, 3)]
    return values if period is None else [v % period for v in values]


def is_b3(slots, period=None):
    values = triples(slots, period)
    return len(set(values)) == len(values)


def greedy_slots(count):
    slots = [0]
    while len(slots) < count:
        new = slots[-1] + 1
        while not is_b3(slots + [new]):
            new += 1
        slots.append(new)
    period = 3 * slots[-1] + 1
    assert is_b3(slots, period)
    return slots, period


def arrivals(slots, period):
    bank = defaultdict(list)
    for h, i, j in product(range(len(slots)), repeat=3):
        if i != j:
            t = (slots[h] + slots[j] - slots[i]) % period
            bank[t].append((h, i, j))
    return bank


def count_collisions(slots, period):
    singles = pairs = 0
    by_slot = arrivals(slots, period)
    for dest, t in enumerate(slots):
        for h, i, j in by_slot[t]:
            assert h == i and j == dest
            singles += 1
    for t, taps in by_slot.items():
        for h, i, j in taps:
            for hh, k, l in taps:
                if i != k:
                    assert (h, hh, j, t) == (i, k, l, slots[j])
                    pairs += 1
    return singles, pairs


def smallest_b2_failure():
    # A Sidon set protects genuine slots, but allows phantom products elsewhere.
    for period in range(3, 40):
        for a in range(1, period):
            for b in range(a + 1, period):
                slots = [0, a, b]
                sums = [(s + u) % period for s, u in combinations_with_replacement(slots, 2)]
                if len(sums) != len(set(sums)) or is_b3(slots, period):
                    continue
                for t, taps in arrivals(slots, period).items():
                    if t not in slots:
                        for left, right in product(taps, repeat=2):
                            if left[1] != right[1]:
                                return period, slots, t, left, right
    raise AssertionError("no counterexample")


def parity(bits):
    result = 0
    for bit in bits:
        result ^= bit
    return result


def simulate(gates, initial, periods):
    """gates[j][side] is (source vertex, number of periods back).
    Two copies of each gate serve as disjoint left/right source banks.
    """
    slots, period = greedy_slots(2 * len(gates))
    left, right = [], []
    for j, operands in enumerate(gates):
        for dest_phase in slots[2*j:2*j+2]:
            for side, (i, lag) in enumerate(operands):
                assert i != j and (lag == 1 or (lag == 0 and i < j))
                delay = lag * period + dest_phase - slots[2*i+side]
                assert delay > 0
                (left if side == 0 else right).append(delay)
    assert len(set(left)) == len(left) and len(set(right)) == len(right)
    assert set(left).isdisjoint(right)
    clock = {phase: 1 for phase in slots}
    # All unmarked cells, and all times before the initial period, are zero.
    history = {phase-period: initial[j//2] for j, phase in enumerate(slots)}
    previous = initial
    nonzero = 0
    for epoch in range(periods):
        expected = []
        for operands in gates:
            bits = [(previous if lag else expected)[i] for i, lag in operands]
            expected.append(1 ^ (bits[0] & bits[1]))
        for phase in range(period):
            t = epoch*period + phase
            lhs = parity(history.get(t-a, 0) for a in left)
            rhs = parity(history.get(t-b, 0) for b in right)
            bit = clock.get(phase, 0) ^ (lhs & rhs)
            history[t] = bit
            if phase in clock:
                assert bit == expected[slots.index(phase)//2]
            else:
                assert bit == 0
            nonzero += bit
        previous = expected
    return periods*period, nonzero


def autonomous(initial_x, initial_y, periods):
    """No clock bit, no constant term. Two initialized copies of one regenerate it."""
    # Each of the two operand lists names (node, lag) pairs.
    nodes = [
        ([(1, 1)], [(1, 1)]),                 # K0 <- K1
        ([(0, 0)], [(0, 0)]),                 # K1 <- current K0
        ([(3, 1)], [(4, 1)]),                 # A <- old X AND old Y
        ([(0, 0), (2, 0)], [(0, 0)]),         # X <- K0 XOR A
        ([(0, 0), (3, 1)], [(0, 0)]),         # Y <- K0 XOR old X
    ]
    slots, period = greedy_slots(2 * len(nodes))
    delays = [[], []]
    for j, node in enumerate(nodes):
        for dest_phase in slots[2*j:2*j+2]:
            for side in range(2):
                for i, lag in node[side]:
                    assert i != j
                    delay = lag * period + dest_phase - slots[2*i + side]
                    assert delay > 0
                    delays[side].append(delay)
    for bank in delays:
        assert len(set(bank)) == len(bank)
    assert set(delays[0]).isdisjoint(delays[1])
    old = [0, 1, 0, initial_x, initial_y]  # just two marked K1 seeds when X=Y=0
    history = {phase-period: old[j//2] for j, phase in enumerate(slots)}
    phase_to_node = {phase: j//2 for j, phase in enumerate(slots)}
    for epoch in range(periods):
        conjunction = old[3] & old[4]
        expected = [1, 1, conjunction, 1 ^ conjunction, 1 ^ old[3]]
        for phase in range(period):
            t = epoch*period + phase
            # This is the complete homogeneous recurrence.
            history[t] = (parity(history.get(t-a, 0) for a in delays[0]) &
                          parity(history.get(t-a, 0) for a in delays[1]))
            assert history[t] == (expected[phase_to_node[phase]] if phase in phase_to_node else 0)
        old = expected
    return periods*period


def bounded_cell(left, center, right):
    # The two-bit wall symbol is sticky even when a neighbor comes from the
    # wrong epoch. Blank is zero. The two ordinary symbols have a nonlinear rule.
    if center == 2:
        return 2
    return center ^ ((left == 1) and (right != 1))


def delayed_binary_queue(start, rows):
    """One variable bit lag and a finite control, independent of the tape width."""
    width = len(start)
    lag = 2 * (width - 2)
    assert start[0] == start[-1] == 2
    fifo = [cell >> j & 1 for cell in start[2:] for j in range(2)]
    assert len(fifo) == lag
    penultimate, last = start[:2]
    pending, partial, phase, cursor = 2, 0, 0, 0
    previous = start
    for _ in range(rows):
        expected = [bounded_cell(previous[(i-1) % width], x, previous[(i+1) % width])
                    for i, x in enumerate(previous)]
        observed = []
        for _ in range(width):
            emitted = 0
            for _ in range(2):
                old_bit = fifo[cursor]
                out_bit = pending >> phase & 1
                fifo[cursor] = out_bit
                cursor = (cursor + 1) % lag
                emitted |= out_bit << phase
                partial |= old_bit << phase
                if phase:
                    pending = bounded_cell(penultimate, last, partial)
                    penultimate, last = last, partial
                    partial = 0
                phase ^= 1
            observed.append(emitted)
        assert observed == expected
        previous = expected


def single_wall_boot(width, sweep_count):
    """Zero-filled FIFO and uniform bootstrap state. Input is solely its length."""
    fifo = [0] * (2*(width-2))
    cursor = 0
    pending = 2  # initial control state emits wall
    boot = True
    penultimate = last = partial = phase = 0
    row = [2, 1] + [0]*(width-2)
    for _ in range(sweep_count):
        observed = []
        for _ in range(width):
            emitted = 0
            for _ in range(2):
                old = fifo[cursor]
                new = pending >> phase & 1
                fifo[cursor] = new
                cursor = (cursor+1) % len(fifo)
                emitted |= new << phase
                partial |= old << phase
                if phase:
                    pending = 1 if boot else bounded_cell(penultimate, last, partial)
                    boot = False
                    penultimate, last = last, partial
                    partial = 0
                phase ^= 1
            observed.append(emitted)
        assert observed == row
        row = [bounded_cell(row[(j-1) % width], v, row[(j+1) % width])
               for j, v in enumerate(row)]


def main():
    single = pair = layouts = 0
    for m in range(2, 9):
        slots, period = greedy_slots(m)
        # Also test a modular translate, with labels wrapping across zero.
        for shift in {0, period - 1}:
            shifted = [(x + shift) % period for x in slots]
            assert is_b3(shifted, period)
            a, b = count_collisions(shifted, period)
            single += a
            pair += b
            layouts += 1
    # The simple synchronous register network has repeated use of one operand.
    sync = [((1, 1), (2, 1)), ((2, 1), (2, 1)), ((1, 1), (0, 1))]
    # The same epoch shares gate A between B and C; D feeds back to the next A and C.
    mixed = [((3, 1), (2, 1)), ((0, 0), (0, 0)),
             ((0, 0), (3, 1)), ((1, 0), (2, 0))]
    clocks = nonzero = runs = 0
    for gates in [sync, mixed]:
        for initial in product((0, 1), repeat=len(gates)):
            t, ones = simulate(gates, initial, 7)
            clocks += t
            nonzero += ones
            runs += 1
    print(f'{layouts} modular slot layouts, {single} active-slot and {pair} double-arrival identities')
    print(f'{runs} complete seven-period traces, {clocks} physical updates, {nonzero} nonzero outputs')
    pure_ticks = sum(autonomous(x, y, 7) for x, y in product((0, 1), repeat=2))
    print(f'4 complete autonomous homogeneous traces, {pure_ticks} physical updates')
    cases = 0
    for width in range(3, 10):
        for inside in product(range(2), repeat=width-2):
            delayed_binary_queue((2,) + inside + (2,), rows=15)
            cases += 1
    print(f'{cases} exhaustive tape seeds over seven widths, 15 sweeps by a single binary delay')
    for width in range(3, 65):
        single_wall_boot(width, sweep_count=18)
    print('62 single-wall binary FIFOs booted from zeros and checked for 18 full sweeps')
    print('smallest three-slot Sidon phantom (period, slots, phase, left, right):',
          smallest_b2_failure())


if __name__ == '__main__':
    main()
