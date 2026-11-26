"""Exercise the columnsort shuffles and constant-depth tiling used by the RAM compiler.

The local base sorter in this finite audit is a bitonic network. The asymptotic
construction substitutes a tabulated logarithmic-depth sorting network there.
"""

import argparse
import random


def dimensions(exponent):
    column_bits = (exponent - 1) // 3
    columns = 1 << column_bits
    rows = 1 << (exponent - column_bits)
    return rows, columns


def reshaped(position, rows, columns):
    return (position % columns) * rows + position // columns


def before_reshape(position, rows, columns):
    return (position % rows) * columns + position // rows


def stage_sources(previous, rows, columns, phase, small, large):
    """Gather a column's inputs by its position in the next phase."""
    size = rows * columns
    if phase == 0:
        return previous
    if phase == 1:
        return [previous[before_reshape(j, rows, columns)] for j in range(size)]
    if phase == 2:
        return [previous[reshaped(j, rows, columns)] for j in range(size)]
    half = rows // 2
    return [
        small if j < half else large if j >= size + half else previous[j - half]
        for j in range(size + rows)
    ]


def bitonic(values, compare):
    values = values.copy()
    span = 2
    while span <= len(values):
        gap = span // 2
        while gap:
            for left in range(len(values)):
                right = left ^ gap
                if right <= left:
                    continue
                low, high = compare(values[left], values[right])
                if left & span:
                    values[left], values[right] = high, low
                else:
                    values[left], values[right] = low, high
            gap //= 2
        span *= 2
    return values


def tiled_sort(values, levels, compare, small, large, visited):
    exponent = len(values).bit_length() - 1
    assert len(values) == 1 << exponent
    if not levels or exponent <= 3:
        return bitonic(values, compare)

    rows, columns = dimensions(exponent)
    previous = values
    for phase in range(4):
        incoming = stage_sources(previous, rows, columns, phase, small, large)
        active = columns + (phase == 3)
        assert len(incoming) == active * rows
        previous = []
        for child in range(active):
            # The enclosing rectangle reserves 2*columns child slots per phase.
            slot = phase * (2 * columns) + child
            assert divmod(slot, 2 * columns) == (phase, child)
            start = child * rows
            previous.extend(tiled_sort(incoming[start:start + rows], levels - 1,
                                       compare, small, large, visited))
        visited.add((exponent, phase, active))
    offset = rows // 2
    return previous[offset:offset + len(values)]


def check_shuffles(max_exponent):
    positions = 0
    for exponent in range(1, max_exponent + 1):
        rows, columns = dimensions(exponent)
        size = rows * columns
        assert size == 1 << exponent and rows % 2 == 0
        assert rows % columns == 0 and rows >= 2 * columns**2
        indices = list(range(size))
        # Independent description: write the old, column-major sequence row by
        # row, then read down each of the resulting new columns.
        expected = [p for column in range(columns) for p in indices[column::columns]]
        after = stage_sources(indices, rows, columns, 1, -1, size)
        assert after == expected
        assert stage_sources(after, rows, columns, 2, -1, size) == indices
        shifted = stage_sources(indices, rows, columns, 3, -1, size)
        half = rows // 2
        assert shifted == [-1] * half + indices + [size] * half
        for p in indices:
            assert before_reshape(reshaped(p, rows, columns), rows, columns) == p
            assert reshaped(before_reshape(p, rows, columns), rows, columns) == p
        positions += size
    return positions


def input_plane(bit, lanes):
    run = 1 << bit
    pattern = ((1 << run) - 1) << run
    width = 2 * run
    while width < lanes:
        pattern |= pattern << width
        width *= 2
    return pattern


def check_zero_one(wires):
    lanes = 1 << wires
    planes = [input_plane(bit, lanes) for bit in range(wires)]
    full = (1 << lanes) - 1
    output = tiled_sort(planes, 3, lambda x, y: (x & y, x | y), 0, full, set())
    # Read a complete Boolean input/output trace at each lane. The bit planes
    # are converted to byte arrays to keep readback linear in the lane count.
    packed = [z.to_bytes((lanes + 7) // 8, 'little') for z in output]
    for lane in range(lanes):
        zeros = wires - lane.bit_count()
        byte, bit = divmod(lane, 8)
        for channel, word in enumerate(packed):
            assert ((word[byte] >> bit) & 1) == (channel >= zeros)
    return lanes


def record_compare(x, y):
    return (x, y) if x <= y else (y, x)


def check_records(large):
    rng = random.Random(20261126)
    visited = set()
    cases = 0
    final_exponent = 14 if large else 11
    for exponent in range(4, final_exponent + 1):
        size = 1 << exponent
        inputs = [
            [0] * size,
            list(reversed(range(size))),
            [rng.randrange(8) for _ in range(size)],
            [rng.randrange(size * size) for _ in range(size)],
        ]
        for keys in inputs:
            # The position serves as a unique time, including on tied keys.
            records = [(0, k, i) for i, k in enumerate(keys)]
            expected = sorted(records)
            for levels in range(1, 4):
                actual = tiled_sort(records, levels, record_compare,
                                    (-1, 0, 0), (1, 0, 0), visited)
                assert actual == expected
                cases += 1
    return cases, len(visited)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--large', action='store_true')
    args = parser.parse_args()
    positions = check_shuffles(16 if args.large else 14)
    patterns = sum(check_zero_one(w) for w in (4, 8, 16))
    cases, phases = check_records(args.large)
    print(f'{positions} positions checked in both reshape directions and the shift')
    print(f'{patterns} Boolean inputs checked through 16 wires')
    print(f'{cases} tagged-record sorts across {phases} active phase layouts')
