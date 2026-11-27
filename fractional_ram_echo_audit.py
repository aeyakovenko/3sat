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


if __name__ == '__main__':
    main()
