"""Exhaustive finite checks of the address-interval sweep in phase-histories.md."""

from itertools import groupby, product


def phases_of(rows, boundaries):
    starts = [0] + [i for i in range(1, len(rows)) if boundaries & (1 << (i - 1))]
    return [range(left, right) for left, right in zip(starts, starts[1:] + [len(rows)])]


def intervals(addresses):
    for _, equal_difference in groupby(enumerate(sorted(set(addresses))), key=lambda x: x[1] - x[0]):
        values = [address for _, address in equal_difference]
        yield values[0], values[-1] + 1


def sweep(rows, phases, universe):
    partition = [(0, universe, None)]
    previous_row = {}
    fragments = updates = 0
    for phase_id, phase in enumerate(phases):
        for left, right in intervals(rows[t] for t in phase):
            updated = []
            updates += 1
            for lo, hi, old_phase in partition:
                if hi <= left or right <= lo:
                    updated.append((lo, hi, old_phase))
                    continue
                if lo < left:
                    updated.append((lo, left, old_phase))
                if right < hi:
                    updated.append((right, hi, old_phase))
                fragments += 1
                for address in range(max(left, lo), min(right, hi)):
                    older = [] if old_phase is None else [
                        t for t in phases[old_phase] if rows[t] == address
                    ]
                    assert older or old_phase is None
                    last = older[-1] if older else None
                    for t in phase:
                        if rows[t] == address:
                            previous_row[t] = last
                            last = t
            partition = sorted(updated + [(left, right, phase_id)])
    assert fragments <= 1 + 3 * updates
    return [previous_row[t] for t in range(len(rows))]


def main():
    cases = 0
    for length in range(1, 7):
        for rows in product(range(3), repeat=length):
            expected = [next((j for j in range(t - 1, -1, -1) if rows[j] == address), None)
                        for t, address in enumerate(rows)]
            for cuts in range(1 << (length - 1)):
                assert sweep(rows, phases_of(rows, cuts), 3) == expected
                cases += 1
    print(f'{cases} traces with phase partitions matched chronological predecessors')


if __name__ == '__main__':
    main()
