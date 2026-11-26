"""Exact final-verdict fault checks on true scalar output slots and GF(2) subspaces."""
from heapq import heappop, heappush
from itertools import combinations


def flip(bits, pairs):
    mask = (1 << pairs) - 1
    return ((bits & mask) & (bits >> pairs)).bit_count() & 1


def subspaces(dim):
    """Yield each binary row space once via reduced row echelon bases."""
    for rank in range(dim + 1):
        for pivots in combinations(range(dim), rank):
            free = [(row, col) for row, pivot in enumerate(pivots)
                    for col in range(pivot + 1, dim) if col not in pivots]
            for bits in range(1 << len(free)):
                basis = [1 << pivot for pivot in pivots]
                for j, (row, col) in enumerate(free):
                    if (bits >> j) & 1:
                        basis[row] |= 1 << col
                yield basis


def span(basis):
    values = [0]
    for row in basis:
        values += [x ^ row for x in values]
    return values


def all_kernels():
    cases = sharp = 0
    populations = []
    for pairs in range(4):
        layouts = 0
        for basis in subspaces(2 * pairs):
            rank = len(basis)
            members = [z for z in range(1 << (2*pairs))
                       if not any((row & z).bit_count() & 1 for row in basis)]
            assert len(members) == 1 << (2*pairs-rank)
            flips = sum(flip(z, pairs) for z in members)
            dual = span(basis)
            signed = len(members) - 2*flips
            assert signed * (1 << rank) == (1 << pairs) * sum(
                1 - 2*flip(z, pairs) for z in dual
            )
            if rank <= pairs:
                lhs = 2 * (1 << pairs) * flips
                rhs = ((1 << pairs) - (1 << rank)) * len(members)
                assert lhs >= rhs
                assert (lhs == rhs) == all(not flip(z, pairs) for z in dual)
                sharp += lhs == rhs
            cases += 1
            layouts += 1
        populations.append(layouts)
    assert populations == [1, 5, 67, 2825]
    return cases, sharp


def one_and_observers():
    """All predicates on 2m bits using one AND and any affine operations.

    Subtract the value at zero. Constant shifts in the two operands then
    contribute only linear terms and are absorbed by the final linear term.
    """
    tested = 0
    minima = []
    for pairs in range(1, 4):
        size = 1 << (2 * pairs)
        linear = [sum(1 << x for x in range(size) if (u & x).bit_count() & 1)
                  for u in range(size)]
        flips = sum(1 << x for x in range(size) if flip(x, pairs))
        best = size
        for i, lhs in enumerate(linear):
            for rhs in linear[i:]:
                product_table = lhs & rhs
                for affine_tail in linear:
                    discrepancy = product_table ^ affine_tail
                    surviving_flips = (flips & ~discrepancy).bit_count()
                    best = min(best, surviving_flips)
                    tested += 1
        # The group-OR test on two (or all available) x-coordinates is optimal.
        budget = min(2, pairs)
        restricted = sum(flip(x, pairs) for x in range(size)
                         if not (x & ((1 << budget) - 1)))
        assert best == restricted
        minima.append(best)
    assert minima == [0, 0, 4]
    return tested, minima


def calibration(width):
    # The three serialized lanes are a, b and q. The all-zero registers generate
    # q-phase every third bit and initialize only the first home q to one.
    k0, k1, pulse, old_phase, q_phase, in_l, in_r, ab, out = range(9)
    nodes = [
        ([(k1, 1)], [(k1, 1)]),
        ([(k0, 0)], [(k0, 0)]),
        ([(k0, 0), (k0, 1)], [(k1, 0)]),
        ([(q_phase, 3)], [(k0, 0)]),
        ([(old_phase, 0), (pulse, 2)], [(k0, 0)]),
        ([(out, 3*(width-2))], [(k0, 0)]),
        ([(in_l, 0)], [(k0, 0)]),
        ([(in_l, 8)], [(in_r, 7)]),
        ([(in_l, 6), (ab, 0), (pulse, 5)], [(q_phase, 0)]),
    ]
    slots = {}
    for vertex in range(len(nodes)):
        sides = [0] if vertex == in_l else [1] if vertex == in_r else [0, 1]
        for side in sides:
            slots[vertex, side] = 4**len(slots)
    period = 3*max(slots.values()) + 1
    delays = [set(), set()]
    long_taps = 0
    for (target, _), dest in slots.items():
        for side, edges in enumerate(nodes[target]):
            for source, back in edges:
                delay = back*period + dest - slots[source, side]
                assert source != target and delay > 0 and delay not in delays[side]
                delays[side].add(delay)
                long_taps += source == out and target == in_l
    assert long_taps == 1 and delays[0].isdisjoint(delays[1])
    seeds = {-period + slots[k1, side] for side in (0, 1)}
    return period, delays, seeds, slots[out, 0], slots[out, 1], set(slots.values())


def physical_stream(delays, seeds, faults, limit):
    pending, queue = {}, []

    def event(t, bank_mask):
        if 0 <= t < limit:
            if t not in pending:
                pending[t] = 0
                heappush(queue, t)
            pending[t] ^= bank_mask

    def broadcast(t):
        for side, bank in enumerate(delays):
            for d in bank:
                event(t + d, 1 << side)

    for t in seeds:
        broadcast(t)
    for t in faults:
        event(t, 0)
    ones = set()
    while queue:
        t = heappop(queue)
        # The only perturbation to the scalar recurrence is this additive residual.
        if (pending.pop(t) == 3) ^ (t in faults):
            ones.add(t)
            broadcast(t)
    return ones


def physical_tests():
    width, pairs = 3, 3
    period, taps, seeds, out, other_copy, marks = calibration(width)
    readings = 0
    homes = 0
    for bits in range(1 << (2*pairs)):
        faults = set()
        for r in range(pairs):
            for lane in range(2):
                if bits >> (lane*pairs+r) & 1:
                    u = 3*(r*width+1) + lane
                    faults.add(u*period + out)
        limit = 3*(pairs+1)*width*period
        stream = physical_stream(taps, seeds, faults, limit)
        assert all(t % period in marks for t in stream)
        acc = 1
        for r in range(pairs+1):
            a = int(r < pairs) & (bits >> r & 1)
            b = int(r < pairs) & (bits >> (pairs+r) & 1)
            for col in range(width):
                lanes = [a, b, acc] if col == 1 else [0, 0, 0]
                for lane, expected in enumerate(lanes):
                    block = (3*(r*width+col)+lane)*period
                    assert (block + out in stream) == bool(expected)
                    # The other output copy obeys the recurrence throughout.
                    assert (block + other_copy in stream) == bool(lane == 2 and expected)
                    readings += 2
            homes += 1
            acc ^= a & b
        assert acc == (1 ^ flip(bits, pairs))
    return readings, homes


if __name__ == '__main__':
    kernels, sharp = all_kernels()
    nonlinear, minima = one_and_observers()
    readings, homes = physical_tests()
    print(f'{kernels} distinct syndrome kernels through m=3, {sharp} attaining the bound at r≤m')
    print(f'{nonlinear} one-AND observer descriptions; smallest passing flip counts {minima}')
    print(f'64 full scalar residual trajectories, {readings} output-copy checks, {homes} home verdicts')
