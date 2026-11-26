"""Check the physical binary product feedback stream against a true radius-one CA.

Unclocked updates use one product of two XORs. The event queue includes *all*
nonnegative times reached by any nonzero tap, even residues outside the slots.
"""
from functools import cache
from heapq import heappop, heappush

from single_product_feedback_audit import greedy_slots


@cache
def machine(width, inject=()):
    # Nodes K0,K1 are initialized in the immediately previous CELL, u=-1.
    # I is one exactly at u=0. L copies the previous tape row's left cell.
    # M multiplies the previous center/right bits. X is the output tape bit.
    constant0, constant1, pulse, left, both, state = range(6)
    nodes = [
        ([(constant1, 1)], [(constant1, 1)]),
        ([(constant0, 1)], [(constant0, 1)]),
        ([(constant0, 0), (constant0, 2)], [(constant1, 0)]),
        ([(state, width+1)], [(state, width+1)]),
        ([(state, width)], [(state, width-1)]),
        ([(left, 0), (both, 0)] + [(pulse, offset) for offset in inject],
         [(constant0, 0)]),
    ]
    slots, period = greedy_slots(2*len(nodes))
    banks = [set(), set()]
    for j, inputs in enumerate(nodes):
        for dst in slots[2*j:2*j+2]:
            for side, terms in enumerate(inputs):
                for i, lag in terms:
                    delay = period*lag + dst - slots[2*i+side]
                    assert delay > 0 and i != j and delay not in banks[side]
                    banks[side].add(delay)
    return tuple(slots), period, tuple(tuple(sorted(b)) for b in banks)


def propagate(history, banks, stop):
    pending, times = {}, []

    def emit(source):
        for side, delays in enumerate(banks):
            for delay in delays:
                t = source+delay
                if 0 <= t < stop:
                    if t not in pending:
                        heappush(times, t)
                        pending[t] = 0
                    pending[t] ^= 1 << side

    for src in history:
        assert src < 0
        emit(src)
    outputs = set()
    while times:
        t = heappop(times)
        if pending.pop(t) == 3:
            outputs.add(t)
            emit(t)
    return outputs


def true_step(state):
    # X'(c) = X(c-1) XOR ( X(c) AND X(c+1) ) on the infinite integer tape.
    return {p for p in range(min(state, default=0)-1, max(state, default=0)+2)
            if ((p-1 in state) ^ ((p in state) and (p+1 in state)))}


def run(width, center, steps, virtual, inject=()):
    slots, period, banks = machine(width, inject)
    history = set()
    for phase in slots[:4]:
        history.add(-period+phase)
    for c in virtual:
        for phase in slots[-2:]:
            history.add(period*(c-width)+phase)
    stop = steps*width*period
    stream = propagate(history, banks, stop)
    residues = set(slots)
    assert all(t % period in residues for t in stream)
    for u in range(steps*width):
        for pair in range(6):
            assert (u*period+slots[2*pair] in stream) == (u*period+slots[2*pair+1] in stream)
        assert all(u*period+p in stream for p in slots[:4])
        assert (u*period+slots[4] in stream) == (u == 0)

    checked = outside_mismatches = 0
    reference = set(virtual)
    for row in range(steps):
        reference = true_step(reference)
        if row == 0:
            reference.update(inject)
        for c in range(width):
            good = ((row*width+c)*period+slots[-1] in stream) == (c in reference)
            # Cone for the final query at (steps-1, center). Initial predecessor
            # cells at time -1 lie within the stored negative row.
            if abs(c-center) <= steps-1-row:
                assert good
                checked += 1
            elif not good:
                outside_mismatches += 1
    return checked, outside_mismatches


def walled_machine(width):
    k0, k1, impulse, old_lwall, lwall, old_rwall, rwall, left, right, middle, state = range(11)
    nodes = [
        ([(k1, 1)], [(k1, 1)]),
        ([(k0, 0)], [(k0, 0)]),
        ([(k0, 0), (k0, 1)], [(k1, 0)]),
        ([(lwall, width)], [(k0, 0)]),
        ([(old_lwall, 0), (impulse, 0)], [(k0, 0)]),
        ([(rwall, width)], [(k0, 0)]),
        ([(old_rwall, 0), (impulse, width-1)], [(k0, 0)]),
        ([(k0, 0), (lwall, 0)], [(state, width+1)]),
        ([(k0, 0), (rwall, 0)], [(state, width-1)]),
        ([(state, width)], [(k0, 0)]),
        ([(left, 0), (right, 0), (middle, 0), (lwall, 0)], [(k0, 0)]),
    ]
    # With digits <4, each sum of three labels uniquely specifies its multiset.
    # Sparse physical scheduling lets us use this direct construction even for large P.
    slots = [4**i for i in range(2*len(nodes))]
    period = 3*slots[-1]+1
    banks = [set(), set()]
    for v, terms in enumerate(nodes):
        for dst in slots[2*v:2*v+2]:
            for side in (0, 1):
                for source, lag in terms[side]:
                    delay = lag*period+dst-slots[2*source+side]
                    assert source != v and delay > 0 and delay not in banks[side]
                    banks[side].add(delay)
    assert not banks[0].intersection(banks[1])
    return slots, period, banks


def guarded_strip(width, cells):
    slots, period, banks = walled_machine(width)
    history = {-period+slots[2], -period+slots[3]}  # only K1's two negative copies
    stop = cells*period
    stream = propagate(history, banks, stop)
    allowed = set(slots)
    assert all(t % period in allowed for t in stream)
    for seed in history:
        # Positive, disjoint delays cannot produce a first bit from one past 1.
        assert not propagate({seed}, banks, stop)
    reference, u = [0]*width, 0
    changes = [0, 0]
    while u < cells:
        row = [prev ^ (reference[c-1] if c else 1)
               ^ (reference[c+1] if c+1 < width else 0)
               for c, prev in enumerate(reference)]
        for c, x in enumerate(row):
            if u >= cells:
                break
            bit = lambda v: int(u*period+slots[2*v] in stream)
            assert all(bit(v) == int(u*period+slots[2*v+1] in stream) for v in range(11))
            assert (bit(0), bit(1), bit(2)) == (1, 1, int(u == 0))
            assert (bit(4), bit(6)) == (int(c == 0), int(c == width-1))
            assert bit(10) == x
            if c in (0, width-1):
                changes[int(c != 0)] += x != reference[c]
            u += 1
        reference = row
    return changes


def bounce(left, middle, right):
    blank, wall, east, west = range(4)
    if middle == wall:
        return wall
    if middle == east and right == wall:
        return west
    if middle == west and left == wall:
        return east
    if middle == blank:
        if left == east:
            return east
        if right == west:
            return west
    return blank


def fifo_transducer(width, rows):
    # The only varying delay is the stream of individual output bits at k*(W-2).
    # previous[] and the lane/word registers are part of a fixed finite controller.
    blank, wall, east, west = range(4)
    k = 2
    lag = k*(width-2)
    wire, previous = [], [blank]*3
    lane, incoming, emitting = 0, 0, blank
    boot = 0
    emitted, observed_home = [], []
    for bit_clock in range(k*(width*rows+1)):
        if lane == 0:
            # Record an observable bounded-register flag at the start of each
            # symbol; at c=0 this samples the previous row's home c=1.
            observed_home.append(previous[2] == east)
            emitting = (wall if boot == 0 else east if boot == 1 else bounce(*previous))
        delayed_bit = wire[bit_clock-lag] if bit_clock >= lag else 0
        output_bit = emitting >> lane & 1
        wire.append(output_bit)
        incoming |= delayed_bit << lane
        lane += 1
        if lane == k:
            emitted.append(sum(wire[-k+i] << i for i in range(k)))
            previous = [previous[1], previous[2], incoming]
            incoming, lane, boot = 0, 0, min(2, boot+1)
    row = [wall, east]+[blank]*(width-2)
    prev_home = blank
    hits = [0, 0]
    for r in range(rows+1):
        start = r*width
        take = min(width, len(emitted)-start)
        assert emitted[start:start+take] == row[:take]
        assert observed_home[start] == (prev_home == east)
        assert row[0] == wall and sum(x in (east, west) for x in row) == 1
        hits[0] += row[1] in (east, west)
        hits[1] += row[-1] in (east, west)
        prev_home = row[1]
        row = [bounce(row[(c-1) % width], row[c], row[(c+1) % width])
               for c in range(width)]
    assert min(hits) > 0
    return len(wire), len(emitted)


def physical_fifo_machine(width):
    k0, k1, pulse, old_even, even, imported_l, imported_r, wall, enabled, value, out = range(11)
    nodes = [
        ([(k1, 1)], [(k1, 1)]),
        ([(k0, 0)], [(k0, 0)]),
        ([(k0, 0), (k0, 1)], [(k1, 0)]),
        ([(even, 1)], [(k0, 0)]),
        ([(k0, 0), (old_even, 0)], [(k0, 0)]),
        ([(out, 2*(width-2))], [(k0, 0)]),
        ([(imported_l, 0)], [(k0, 0)]),
        ([(even, 0)], [(imported_r, 4)]),
        ([(k0, 0), (even, 0)], [(k0, 0), (imported_r, 5)]),
        ([(enabled, 0)], [(imported_r, 6), (imported_r, 2)]),
        ([(wall, 0), (value, 0), (pulse, 0), (pulse, 3)], [(k0, 0)]),
    ]
    # The incoming FIFO bit pays for ONE variable tap. Place its receiver in
    # the left bank only, then create its right-bank copy by one same-bit gate.
    slots, physical = {}, []
    for v in range(len(nodes)):
        sides = (0,) if v == imported_l else (1,) if v == imported_r else (0, 1)
        for side in sides:
            phase = 4**len(physical)
            slots[v, side] = phase
            physical.append((v, phase))
    period = 3*physical[-1][1]+1
    banks = [set(), set()]
    tagged = None
    for dest, phase in physical:
        for side, terms in enumerate(nodes[dest]):
            for source, lag in terms:
                delay = period*lag+phase-slots[source, side]
                assert source != dest and delay > 0 and delay not in banks[side]
                banks[side].add(delay)
                if (dest, source) == (imported_l, out):
                    assert tagged is None and side == 0
                    tagged = delay
    assert tagged is not None and not banks[0].intersection(banks[1])
    return slots, period, banks, tagged


def physical_fifo_audit():
    baseline = None
    rows_checked = bit_steps = imports = 0
    for width in range(3, 10):
        s, period, banks, long_delay = physical_fifo_machine(width)
        short = (banks[0]-{long_delay}, banks[1])
        assert long_delay == 2*period*(width-2)+s[5, 0]-s[10, 0]
        if baseline is None:
            baseline = (s, period, short)
        assert (s, period, short) == baseline
        history = {-period+s[1, side] for side in range(2)}
        rows = width**4 if width <= 4 else 3*width
        bit_count = 2*width*rows
        stream = propagate(history, banks, bit_count*period)
        phases = set(s.values())
        assert all(t % period in phases for t in stream)
        reference = [0, 1]+[0]*(width-2)
        emitted = []
        for row in range(rows):
            for c in range(width):
                for lane, expected in enumerate((int(c == 0), reference[c])):
                    u = 2*(width*row+c)+lane
                    get = lambda v, side: int(u*period+s[v, side] in stream)
                    for v in (0, 1, 2, 3, 4, 7, 8, 9, 10):
                        assert get(v, 0) == get(v, 1)
                    assert (get(0, 0), get(1, 0), get(2, 0), get(4, 0)) == (1, 1, int(u == 0), 1-lane)
                    lag = 2*(width-2)
                    imported = emitted[u-lag] if u >= lag else 0
                    assert get(5, 0) == imported == get(6, 1)
                    assert get(10, 0) == expected
                    emitted.append(get(10, 0))
                    imports += imported
            reference = [0]+[reference[c-1] ^ reference[(c+1)%width] for c in range(1, width)]
            rows_checked += 1
        bit_steps += bit_count
    return bit_steps, rows_checked, imports


def main():
    matches = seam = runs = 0
    for width, center, steps in ((9, 4, 3), (14, 7, 5)):
        candidates = (0, 1, center-1, center, center+1, width-2, width-1)
        for mask in range(1 << len(candidates)):
            initial = [c for i, c in enumerate(candidates) if mask >> i & 1]
            ok, off = run(width, center, steps, initial)
            matches += ok
            seam += off
            runs += 1
    assert seam > 0  # The full folded rectangle would be an invalid invariant.
    pulse_cells = 0
    for width, center, steps in ((13, 6, 4), (19, 9, 6)):
        for distance in (1, 2, 3):
            ok, _ = run(width, center, steps, [], (center, center+distance))
            pulse_cells += ok
    print(f'{runs} physical recurrences, {matches} correct cone cells, '
          f'{seam} differences outside the cone')
    print(f'{pulse_cells} cone cells from two injected markers, only four fixed negative clock-source bits')

    ticks = 0
    switches = [0, 0]
    for width in range(3, 11):
        cells = width**5+1 if width <= 4 else width*(2*width+1)
        observed = guarded_strip(width, cells)
        assert min(observed) > 0
        switches = [p+q for p, q in zip(switches, observed)]
        ticks += cells
    print(f'{ticks} exact full-strip cells for widths 3 to 10 with two fixed seeds; '
          f'{switches[0]} left and {switches[1]} right boundary changes, '
          'including the target PW^5+state-slot at W=3,4')

    fifo_bits = fifo_cells = 0
    for width in range(3, 17):
        rows = width**4 if width <= 6 else 4*width
        nbits, ncells = fifo_transducer(width, rows)
        fifo_bits += nbits
        fifo_cells += ncells
    print(f'{fifo_bits} single-long-delay FIFO bit steps, {fifo_cells} exact tape cells, '
          'widths 3 to 16, previous-home diagnostic checked at the W^5 cell for W=3 to 6')

    bits, rows, imports = physical_fifo_audit()
    print(f'{bits} physical single-variable-tap bit steps, {rows} entire circular CA rows '
          f'over 7 widths, {imports} nonzero imported bits; all other taps identical')


if __name__ == '__main__':
    main()
