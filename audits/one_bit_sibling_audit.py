"""Audit exact-length Boolean restriction pairs and the sound-reply search."""

from itertools import combinations, product
from random import Random

import pycosat

from one_byte_dense_successor_audit import adjustable, clause, encode, parse


def bound(rows):
    return max(abs(x) for row in rows for x in row)


def pin(literal):
    left, right = [u for u in (1, 2, 3) if u != abs(literal)][:2]
    return {clause(literal, i, j) for i, j in product((left, -left), (right, -right))}


def siblings(source, prefix):
    v = bound(source)
    x = len(prefix) + 1
    assert x <= v
    p, q = v + 1, v + 2
    a = v + 3 + (2 - (v + 3)) % 10
    b = a + 1
    common = source.copy()
    for i, bit in enumerate(prefix, 1):
        common.update(pin(i if bit else -i))
    for i in range(p, a):
        common.update(pin(-i))
    common.update(clause(p, i, j) for i, j in ((-a, x), (a, -x), (-b, -x), (b, x)))
    return common | {clause(p, q, b)}, common | {clause(p, q, a)}


def padded_pair(pair, target):
    left, right = pair
    v, c = bound(left), len(left)
    assert v == bound(right) and c == len(right)
    minimum = len(encode(left))
    assert minimum == len(encode(right))
    t = 0
    while True:
        next_min = (minimum + len(str(v+t+1)) + 7
                    + len(str(v+t+1)) - len(str(v+t))
                    + len(str(c+t+1)) - len(str(c+t)))
        if next_min > target:
            break
        minimum = next_min
        t += 1
    assert t >= 12
    slack = target - minimum
    added = set()
    for i in range(1, t + 1):
        g = v + i
        high = max(1, len(str(g)) - 1)
        take = min(slack, 2 * high) if t-i < 12 else 0
        added.add(adjustable(g, (1, high), take))
        slack -= take
    assert slack == 0
    return left | added, right | added


def models(source):
    return [bits for bits in product((False, True), repeat=bound(source))
            if all(any(bits[abs(z)-1] == (z > 0) for z in row) for row in source)]


def fork_labels(allowed, prefix):
    return tuple(any(row[:len(prefix)+1] == prefix + (bit,) for row in allowed)
                 for bit in (False, True))


def check_pair(pair, expected, target):
    left, right = (encode(rows) for rows in pair)
    assert len(left) == len(right) == target
    changes = [(x, y) for x, y in zip(left, right) if x != y]
    assert changes == [(ord('3'), ord('2'))] and ord('3') ^ ord('2') == 1
    actual = tuple(pycosat.solve(list(parse(raw))) != 'UNSAT' for raw in (left, right))
    assert actual == expected


def check_fork(source, prefix, expected, offsets):
    pair = siblings(source, prefix)
    base = len(encode(pair[0]))
    check_pair(pair, expected, base)
    v, c = bound(pair[0]), len(pair[0])
    minimum12 = (base + len(str(v+12))-len(str(v)) + len(str(c+12))-len(str(c))
                 + sum(len(str(v+i))+7 for i in range(1, 13)))
    for j in offsets:
        check_pair(padded_pair(pair, minimum12 + j), expected, minimum12 + j)
    return 1 + len(offsets)


def choose(labels, mask):
    # Fixed order on two lengths, two solver identities and two child values.
    # Each set bit makes the corresponding solver return its truthful verdict.
    for i in range(8):
        child = bool(i % 2)
        if mask & (1 << i):
            return child if labels[child] else not child
    return False


def search(allowed, v, timings):
    prefix = ()
    loss = None
    for depth in range(v):
        labels = fork_labels(allowed, prefix)
        mask = timings(prefix, depth)
        bit = choose(labels, mask)
        if any(labels) and not labels[bit]:
            assert labels[not bit] and mask == 0
            assert loss is None
            loss = prefix
        prefix += (bit,)
    accepted = prefix in allowed
    assert accepted == (bool(allowed) and loss is None)
    return loss is not None


def main():
    rng = Random(12571)
    audits = searches = failures = 0
    labels_seen = set()
    # All 255 nonempty three-variable cores; their possible verdicts and
    # restricted assignments are determined by independent brute force.
    triple = list(product((1, -1), (2, -2), (3, -3)))
    sources = [{row for j, row in enumerate(triple) if mask & (1 << j)}
               for mask in range(1, 256)]
    for v in (4, 5, 8, 9, 10):
        triples = list(combinations(range(1, v+1), 3))
        for _ in range(4):
            rows = {clause(i, i+1, i+2) for i in range(1, v-1)}
            for _ in range(4*v):
                rows.add(clause(*(i*rng.choice((-1, 1)) for i in rng.choice(triples))))
            sources.append(rows)
    for source in sources:
        allowed = models(source)
        v = bound(source)
        for depth in range(v):
            if v == 3:
                prefixes = list(product((False, True), repeat=depth))
            else:
                prefixes = [tuple(rng.choice((False, True)) for _ in range(depth))]
            for prefix in prefixes:
                expected = fork_labels(allowed, prefix)
                labels_seen.add(expected)
                audits += check_fork(source, prefix, expected, range(3))
        for policy in (lambda _p, _d: 0, lambda _p, _d: 255,
                       lambda _p, _d: rng.choice((0, 0, 1, 4, 16, 128))):
            failures += search(allowed, v, policy)
            searches += 1
    assert len(labels_seen) == 4 and failures
    # Crossing two-to-three decimal digits and a padding-header carry.
    for v in (96, 97, 98, 99, 100):
        source = set().union(*(pin(i) for i in range(3, v+1)))
        audits += check_fork(source, (False, True), (False, True), range(14))
    fork_masks = 0
    for labels in product((False, True), repeat=2):
        for mask in range(256):
            bit = choose(labels, mask)
            if any(labels) and not labels[bit]:
                assert labels[not bit] and mask == 0
            fork_masks += 1
    print(f'{audits} serialized one-bit pairs, including unpadded and consecutive exact lengths')
    print(f'{searches} complete assignment searches, {failures} satisfiable-source failures')
    print(f'{fork_masks} sibling-verdict and solver/length availability combinations')


if __name__ == '__main__':
    main()
