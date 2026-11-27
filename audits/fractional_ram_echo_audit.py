"""Check the one-address additive separation, using exact fibers and an optional LP."""

import argparse
from fractions import Fraction
from itertools import product


def cpu_log(pairs):
    bit = 0
    rows = []
    for a, b in pairs:
        rows.extend((bit, a, b))
        bit = a | b
    return (*rows, bit)


def memory_log(values):
    return (*[bit for old in values[:-1] for bit in (old, old, old)], values[-1])


def score(trace):
    level = 0
    for i in range(0, len(trace)-1, 3):
        old, a, b = trace[i:i+3]
        level = 2 * level + a + b - 2 * old
    return level


def logs(length):
    pairs = list(product((0, 1), repeat=2))
    cpu = [cpu_log(p) for p in product(pairs, repeat=length) if any(p[-1])]
    mem = [memory_log(writes) for writes in product((0, 1), repeat=length+1)]
    return cpu, mem


def equalities(trace):
    mass = difference = moment = 0
    repeated = []
    endpoint = 0
    for i in range((len(trace) - 1) // 3):
        old, a, b = trace[3*i:3*i+3]
        mass += 2*old-a-b
        difference += a-b
        moment += i*(a-b)
        repeated.append(a ^ b)
        endpoint ^= old ^ a
    return (mass, difference, moment), (*repeated, endpoint)


def several_loads(length, width, prime):
    all_rows = list(product((0, 1), repeat=width))
    checked = 0
    for rows in product(all_rows, repeat=length):
        if not any(rows[-1]):
            continue
        old = mass = 0
        moments = [0]*width
        for i, row in enumerate(rows):
            mass += width*old-sum(row)
            delta = sum(row[:-1]) - (width-1)*row[-1]
            for h in range(width):
                moments[h] = (moments[h] + pow(i, h, prime)*delta) % prime
            old = int(any(row))
        assert mass or any(moments)
        checked += 1
    return checked


def first_switch(length, initial_reads, later):
    """Full logs implementing the binary quotient argument for A_0 and B_0."""
    pairs = [initial_reads] + [(int(i not in later), 1) for i in range(1, length)]
    return cpu_log(pairs), memory_log([0] + [1]*length)


def check_binary_obstruction(length):
    # When the later A_i are independent in dimension length, a change of
    # basis sends them to the first length-1 standard coordinate vectors.
    # Enumerate all choices of A_0,B_0 and construct the actual colliding logs.
    high_bit = 1 << (length-1)
    for a, b in product(range(2*high_bit), repeat=2):
        candidates = [(a, (1, 0)), (b, (0, 1)), (a ^ b, (1, 1))]
        element, initial = next((v, pair) for v, pair in candidates if v < high_bit)
        later = {i for i in range(1, length) if element & (1 << (i-1))}
        cpu, memory = first_switch(length, initial, later)
        residue = 0
        for slot, (x, y) in enumerate(zip(cpu, memory)):
            if x == y:
                continue
            if slot == 1:
                residue ^= a
            elif slot == 2:
                residue ^= b
            else:
                assert slot % 3 == 1
                residue ^= 1 << (slot//3-1)
        assert cpu[-1] == 1 and residue == 0


def rational_errors(length, tied_stages):
    """Exact marginals of the construction, using one shared uniform dyadic draw."""
    repeats = length - len(tied_stages)
    size = 1 << repeats
    diff = [0] * (3*length + 1)
    for seed in range(size):
        threshold = 1
        pairs = []
        writes = []
        for i in range(length):
            a = int(seed < threshold)
            writes.append(a)
            if i in tied_stages:
                b = a
            else:
                b = int(threshold <= seed < 2*threshold)
                threshold *= 2
            pairs.append((a, b))
        writes.append(1)
        c, m = cpu_log(pairs), memory_log(writes)
        assert c[-1] == 1
        for i, (x, y) in enumerate(zip(c, m)):
            diff[i] += x-y
    assert threshold == size
    assert diff == [-1] + [0] * (len(diff)-1)
    return Fraction(sum(map(abs, diff)), size)


def check_lp(cpu, memory):
    """Optimize over mixtures of all logs, independently of the analytic score."""
    import numpy as np
    from scipy.optimize import linprog

    c, m = np.array(cpu).T, np.array(memory).T
    events, nc = c.shape
    nm = m.shape[1]
    gap = np.column_stack((c, -m))
    bounds_matrix = np.block([[gap, -np.eye(events)], [-gap, -np.eye(events)]])
    totals = np.zeros((2, nc + nm + events))
    totals[0, :nc] = 1
    totals[1, nc:nc+nm] = 1
    result = linprog([0] * (nc+nm) + [1] * events,
                     A_ub=bounds_matrix, b_ub=np.zeros(2*events),
                     A_eq=totals, b_eq=[1, 1], bounds=(0, None), method='highs')
    assert result.success, result.message
    return result.fun


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lp', action='store_true', help='independently solve the LP with SciPy through five stages')
    args = parser.parse_args()
    for length in range(1, 7):
        cpu, memory = logs(length)
        assert set(map(score, cpu)) == set(range(1, (1 << length)+1))
        assert set(map(score, memory)) == {0}
        assert all(any(z) for c in cpu for z in equalities(c))
        assert all(not any(z) for m in memory for z in equalities(m))
        check_binary_obstruction(length)
        kept = 0
        for tie_bits in product((False, True), repeat=length):
            tied = {i for i, value in enumerate(tie_bits) if value}
            expected = rational_errors(length, tied)
            if args.lp and length <= 5:
                restricted_cpu = [c for c in cpu if all(c[3*i+1] == c[3*i+2] for i in tied)]
                assert abs(check_lp(restricted_cpu, memory) - expected) < 1e-8
            kept += 1
        print(f'{length} stages: {len(cpu)} false CPU and {len(memory)} memory logs, '
              f'{kept} tie patterns; baseline distance 1/{1 << length}')


    for width, length, prime in [(3, 4, 5), (4, 3, 5)]:
        checked = several_loads(length, width, prime)
        print(f'{width} loads per stage: rejected all {checked} false logs across {length} stages')


if __name__ == '__main__':
    main()
