"""Finite checks for binary backgrounds, affine consequences, and a false codeword."""

from itertools import combinations, product
from random import Random


def check_local_hulls():
    count = 0
    for n in range(5):
        rows = range(1 << n)
        masks = [x for x in rows if x.bit_count() <= 2]
        for size in range(4):
            for accepted in combinations(rows, size):
                affine = set(accepted)
                if size == 3:
                    a, b, c = accepted
                    affine.add(a ^ b ^ c)
                hull = {x for x in rows if all(any((x ^ y) & m == 0 for y in accepted)
                                                 for m in masks)}
                assert set(accepted) == affine & hull
                count += 1
    return count


def check_pin_projection():
    rng = Random(83)
    systems = pins_tested = 0
    for n in (2, 3, 4):
        rows = range(1 << n)
        tests = [(m, bad) for m in rows if 1 <= m.bit_count() <= 2
                 for bad in rows if bad & m == bad]
        pin_patterns = [(m, value) for m in rows for value in rows if value & m == value]
        if n == 2:
            families = (tuple(c for i, c in enumerate(tests) if used >> i & 1)
                        for used in range(1 << len(tests)))
        else:
            families = (rng.sample(tests, rng.randrange(1, len(tests) // 2))
                        for _ in range(400))
        for clauses in families:
            solutions = [x for x in rows if all(x & mask != bad for mask, bad in clauses)]
            forbidden = {(m, value) for m, value in pin_patterns if m.bit_count() <= 2
                         and all(x & m != value for x in solutions)}
            for mask, value in pin_patterns:
                fits = any(x & mask == value for x in solutions)
                obstruction = any(m & mask == m and value & m == y for m, y in forbidden)
                assert fits != obstruction
                pins_tested += 1
            systems += 1
    return systems, pins_tested


def check_parity_compilation():
    # Minimize the number of failed slots of a private split and its two
    # bit-link clauses, also allowing the parity ports to disagree with flags.
    for direction, parent, left, right in product(range(2), repeat=4):
        edge_failures = (left and direction != 0) + (right and direction != 1)
        costs = [edge_failures + (p != (l ^ r)) +
                 (p != parent) + (l != left) + (r != right)
                 for p, l, r in product(range(2), repeat=3)]
        expected_feasible = parent == left + right and edge_failures == 0
        assert (min(costs) == 0) == expected_feasible
    # Each inactive, unmarked tree can be completed in the binary background
    # using root only, or in the parity background with all flags zero.
    for direction in range(2):
        parent, left, right = 1, 0, 0
        assert not (left and direction) and not (right and not direction)
        parent, left, right = 0, 0, 0
        assert parent == left ^ right


def field_table(j, modulus):
    q = 1 << j

    def multiply(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & q:
                a ^= modulus
        return result

    return [[multiply(a, b) for b in range(q)] for a in range(q)]


def code_check(j, modulus):
    q = 1 << j
    degree = q // 4
    mul = field_table(j, modulus)
    inv = [0] + [mul[a].index(1) for a in range(1, q)]

    def value(coefficients, a):
        result = 0
        for c in reversed(coefficients):
            result = mul[result][a] ^ c
        return result

    target = [value((0,) * degree + (1,), a) for a in range(q)]
    distances = [[(target[a] ^ u).bit_count() + mul[a][target[a] ^ u].bit_count()
                  for u in range(q)] for a in range(q)]
    minimum = 2*j*q
    for coefficients in product(range(q), repeat=degree):
        distance = sum(distances[a][value(coefficients, a)] for a in range(q))
        minimum = min(minimum, distance)
    assert minimum > 0

    # Construct each Lagrange interpolant in the monomial basis; multiply out
    # its factors and compare both binary coordinates at every required block.
    count = 0
    for size in range(degree + 1):
        for subset in combinations(range(q), size):
            coefficients = [0] * degree
            for a in subset:
                numerator = [1]
                denominator = 1
                for b in subset:
                    if b == a:
                        continue
                    denominator = mul[denominator][a ^ b]
                    new = [0] * (len(numerator) + 1)
                    for i, c in enumerate(numerator):
                        new[i] ^= mul[b][c]
                        new[i+1] ^= c
                    numerator = new
                scale = mul[target[a]][inv[denominator]]
                for i, c in enumerate(numerator):
                    coefficients[i] ^= mul[scale][c]
            for a in subset:
                u = value(coefficients, a)
                assert (u, mul[a][u]) == (target[a], mul[a][target[a]])
            count += 1
    return count, minimum, q**degree


if __name__ == "__main__":
    check_parity_compilation()
    print("Checked all split, port and edge assignments for disjoint ternary parity rows")
    print(f"{check_local_hulls()} relations with at most three tuples")
    systems, pins = check_pin_projection()
    print(f"{systems} explicit binary backgrounds, {pins} pin projections")
    for degree, modulus in [(2, 0b111), (3, 0b1011), (4, 0b10011)]:
        subsets, distance, messages = code_check(degree, modulus)
        print(f"GF(2^{degree}): {subsets} interpolated subsets, {messages} "
              f"messages, minimum false-word distance {distance}/{2*degree*(1<<degree)}")
