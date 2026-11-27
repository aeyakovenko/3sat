"""Check orientation mixing and directly factored two-comparison paths on the high complementary inputs."""

from itertools import combinations, product

import numpy as np

from clocked_native_path import ALU, primitive, verdict


def complementary():
    return [(p, q, 15 - p, 15 - q) for p, q in product(range(4, 12), repeat=2)]


def mixed(x, y, first):
    return tuple(u if j in first else v for j, (u, v) in enumerate(zip(x, y)))


def check_mixing():
    target = complementary()
    orientation_pairs = 0
    for x, y in combinations(target, 2):
        bands = {i for i, word in enumerate(x) if word < 8}
        if bands == {i for i, word in enumerate(y) if word < 8}:
            assert not (verdict(mixed(x, y, bands)) and verdict(mixed(y, x, bands)))
            orientation_pairs += 1
        for choice in range(1, 15):
            first = {i for i in range(4) if (choice >> i) & 1}
            for a, b in ((0, 2), (1, 3)):
                if (a in first) != (b in first) and x[a] != y[a]:
                    assert not (verdict(mixed(x, y, first)) and verdict(mixed(y, x, first)))
    assert orientation_pairs == 480
    print('All 480 same-orientation pairs have a rejecting hybrid.')


def check_single_pair():
    # A literal/cell can appear on either side of every arithmetic or comparison instruction.
    codes = np.arange(256, dtype=np.int32)
    pair = (codes >> 4, codes & 15)
    raw = [*range(16), *pair]
    blocked = ((pair[0] & pair[1]) != 0) | (codes == 15)
    high = (pair[0] >= 4) & (pair[0] < 12) & (pair[0] + pair[1] == 15)
    assert np.count_nonzero(high) == 8
    operations = {}
    for name, left, right in product(ALU, raw, raw):
        values = np.broadcast_to(primitive(name, left, right), codes.shape)
        key = values.astype(np.uint8).tobytes()
        if key not in operations:
            operations[key] = values
    for result in operations.values():
        for other in raw:
            for name in ('eq', 'lt', 'slt'):
                for a, b in ((result, other), (other, result)):
                    outcome = np.asarray(primitive(name, a, b), dtype=bool)
                    # Both orientations of the branch are allowed.
                    assert not np.any(outcome[high]) or np.any(outcome[blocked])
                    assert np.all(outcome[high]) or not np.all(outcome[blocked])
    print(f'All {len(operations)} distinct one-ALU pair tables have the sentinel obstruction.')


def check_sharpness():
    # Four raw guards pin a complementary base in each surviving orientation at most.
    # One ALU and three guards can cover eight complementary points.
    codes = np.arange(65536, dtype=np.int32)
    p, q, m, n = [(codes >> sh) & 15 for sh in (12, 8, 4, 0)]
    accept = ((p ^ m) == 15) & (q == 4) & (n == 11)
    truth = ((p & m) == 0) & ((q & n) == 0) & ((m != 15) | (n != 15))
    assert np.all(truth[accept])
    target = (p >= 4) & (p < 12) & (q >= 4) & (q < 12) & (p + m == 15) & (q + n == 15)
    assert np.count_nonzero(target & accept) == 8


if __name__ == '__main__':
    check_mixing()
    check_single_pair()
    check_sharpness()
