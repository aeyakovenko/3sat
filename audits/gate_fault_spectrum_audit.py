"""Compare Walsh coefficients of a gate-fault table with local quadratic elimination."""
from fractions import Fraction
from itertools import product
from math import comb
from random import Random


def gate_value(gate, bits):
    left, right, truth = gate
    a = (bits >> left) & 1 if left is not None else 0
    b = (bits >> right) & 1 if right is not None else 0
    return truth >> (a + 2 * b) & 1


def run(gates, faults):
    word = 0
    for i, gate in enumerate(gates):
        word |= (gate_value(gate, word) ^ (faults >> i & 1)) << i
    return word


def coefficient(gates, selected):
    terms = set()

    def flip(mask):
        terms.symmetric_difference_update((mask,))

    flip(1 << (len(gates) - 1))
    for i, (left, right, truth) in enumerate(gates):
        if not selected >> i & 1:
            continue
        flip(1 << i)
        base, l, r, lr = [truth >> a & 1 for a in range(4)]
        if base:
            flip(0)
        if left is not None and base ^ l:
            flip(1 << left)
        if right is not None and base ^ r:
            flip(1 << right)
        if left is not None and right is not None and base ^ l ^ r ^ lr:
            flip((1 << left) | (1 << right))
    pairs = 0
    while True:
        mixed = next((m for m in terms if m.bit_count() == 2), None)
        if mixed is None:
            break
        a = mixed & -mixed
        b = mixed ^ a
        terms.remove(mixed)
        left_terms = [m ^ a for m in terms if m & a]
        right_terms = [m ^ b for m in terms if m & b]
        terms = {m for m in terms if not m & mixed}
        for l in left_terms:
            for r in right_terms:
                flip(l | r)
        pairs += 1
    if any(terms):
        return Fraction(0)
    return Fraction(-1 if 0 in terms else 1, 1 << pairs)


def reached(gates, chosen):
    if not chosen:
        return 0
    stack = [len(gates) - 1]
    visited = 0
    while stack:
        i = stack.pop()
        if not chosen >> i & 1 or visited >> i & 1:
            continue
        visited |= 1 << i
        stack.extend(idx for idx in gates[i][:2] if idx is not None)
    return visited


def shapes(size):
    if size == 0:
        yield None
        return
    for lsize in range(size):
        for l in shapes(lsize):
            for r in shapes(size - lsize - 1):
                yield l, r


def apply_shape(gates, node, shape, used):
    if shape is None:
        return True
    if node is None or node in used:
        return False
    used.add(node)
    return all(apply_shape(gates, kid, branch, used)
               for kid, branch in zip(gates[node][:2], shape))


def check(gates, limit):
    n = len(gates)
    values = [1 - 2 * (run(gates, e) >> (n - 1)) for e in range(1 << n)]
    for i in range(n):
        for k in range(1 << n):
            if not (k >> i) & 1:
                l, r = values[k], values[k | (1 << i)]
                values[k], values[k | (1 << i)] = l + r, l - r
    shapes_seen = {0}
    for size in range(1, limit + 1):
        for tree in shapes(size):
            used = set()
            if apply_shape(gates, n - 1, tree, used):
                shapes_seen.add(sum(1 << j for j in used))
    low_mass = 0
    for mask, scaled in enumerate(values):
        local = coefficient(gates, mask)
        assert local == Fraction(scaled, 1 << n)
        if scaled:
            assert reached(gates, mask) == mask
            if mask.bit_count() <= limit:
                assert mask in shapes_seen
                low_mass += local * local
    assert low_mass == 1 or 1 - low_mass >= Fraction(1, 4 ** limit)
    assert sum(s * s for s in values) == 4 ** n
    return 1 << n


if __name__ == "__main__":
    rng = Random(314159)
    total = 0
    for a, b, truth in product(range(2), range(2), range(16)):
        total += check([(None, None, a), (None, None, b), (0, 1, truth)], 3)
    for n in range(2, 10):
        for _ in range(35):
            gates = [(None, None, rng.randrange(2))]
            gates.extend((rng.randrange(i), rng.randrange(i), rng.randrange(16)) for i in range(1, n))
            total += check(gates, min(n, 4))
    for size in range(8):
        assert sum(1 for _ in shapes(size)) == comb(2 * size, size) // (size + 1)
    print(f"{total:,} exact coefficients checked against direct Walsh transforms")
