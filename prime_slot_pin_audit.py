"""Exhaust low-bit subcubes and a bounded-gap example for width-one pins.

After fixing the higher folded timestamp blocks, a scalar F_2 product of
layer entries accepts either nothing or a subcube of the remaining low bits.
Run with Python 3, without dependencies.
"""

from itertools import product


def low_cubes(h):
    # A pattern entry is 0, 1, or free. Generate the actual integer indices.
    for pattern in product((0, 1, None), repeat=h):
        points = [sum(1 << j for j, bit in enumerate(pattern) if bit == 1)]
        for j, bit in enumerate(pattern):
            if bit is None:
                points += [x + (1 << j) for x in points]
        yield pattern.count(None), tuple(points)


def residue_checks():
    checked = 0
    # For odd composites too, addition of any power of two cycles through all
    # residues. The prime case alone suffices for the slot calibration below.
    for h in range(1, 9):
        for free, points in low_cubes(h):
            assert len(points) == 1 << free
            for period in (3, 5, 7, 11, 9, 15):
                residues = {x % period for x in points}
                assert len(residues) >= min(period, free+1)
                if len(residues) < period:
                    assert len(points) <= 1 << (len(residues)-1)
                checked += 1
    # Free bit positions equally spaced by the order of 2 attain f+1 residues.
    for p in (3, 5, 7, 11):
        order = next(j for j in range(1, p) if pow(2, j, p) == 1)
        for free in range(p-1):
            points = [sum(bit << (order*j) for j, bit in enumerate(bits))
                      for bits in product((0, 1), repeat=free)]
            assert {x % p for x in points} == set(range(free+1))
    # The odd-period hypothesis matters when only a single residue is omitted.
    assert len({x % 4 for x in range(0, 256, 2)}) == 2
    return checked


def bounded_gap_checks(p, h):
    B = 1 << h
    # L={p,pB+1}, R={2p}; two negative seeds. The long tap reads off-slot
    # when t is a multiple of p, and the right bank kills all other residues.
    values = {-2*p: 1, -p: 1}
    for t in range(2*p*B):
        values[t] = (values.get(t-p, 0) ^ values.get(t-p*B-1, 0)) * values.get(t-2*p, 0)
        assert values[t] == int(t % p == 0)

    cubes = [points for _, points in low_cubes(h)]
    pairs = 0
    for block in range(p):
        start = (p+block)*B
        zero = [()] + [c for c in cubes if all(values[start+x] == 0 for x in c)]
        one = [()] + [c for c in cubes if all(values[start+x] == 1 for x in c)]
        assert max(map(len, zero)) <= 1 << (p-2)
        assert max(map(len, one)) == 1
        assert B // (2*p) > (1 << (p-2)) + 1
        for zeros, ones in product(zero, one):
            chain = [-1, *sorted(zeros+ones), B]
            assert max(y-x for x, y in zip(chain, chain[1:])) > 2*p
            pairs += 1
    return pairs


def linear_image(columns, x):
    result = 0
    for j, column in enumerate(columns):
        if x & (1 << j):
            result ^= column
    return result


def matrix_cycle_checks():
    matrices = cycles = 0
    odd_prime_divisors = set()
    for width in range(1, 4):
        n = 1 << width
        for columns in product(range(n), repeat=width):
            complete = {0}
            for vector in range(1, n):
                path = {}
                x = vector
                while x not in complete and x not in path:
                    path[x] = len(path)
                    x = linear_image(columns, x)
                if x in path:
                    period = len(path)-path[x]
                    cycles += 1
                    # Width <= 3 implies cycle lengths <= 7.
                    for p in (3, 5, 7):
                        if period % p == 0:
                            order = next(j for j in range(1, p) if pow(2, j, p) == 1)
                            assert order <= width
                            odd_prime_divisors.add(p)
                complete.update(path)
            matrices += 1
    assert odd_prime_divisors == {3, 7}
    return matrices, cycles


def field_five_checks(h):
    # GF(16) using the degree-four cyclotomic polynomial for the fifth roots.
    def multiply(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & 16:
                a ^= 0b11111
        return result

    def trace(a):
        result = 0
        for _ in range(4):
            result ^= a
            a = multiply(a, a)
        assert result in (0, 1)
        return result

    assert all(any(multiply(a, b) == 1 for b in range(1, 16)) for a in range(1, 16))
    root = 2
    power = 1
    for _ in range(4):
        power = multiply(power, root)
        assert power != 1
    assert multiply(power, root) == 1
    # At bit j the one-transition multiplies by root^(2^j). Zero is identity.
    layers, square = [], root
    for _ in range(h):
        layers.append(tuple(multiply(1 << j, square) for j in range(4)))
        square = multiply(square, square)
    for t in range(1 << h):
        x = 1
        for j, columns in enumerate(layers):
            if (t >> j) & 1:
                x = linear_image(columns, x)
        assert trace(x) == int(t % 5 != 0)
    return 1 << h


def check_gate_projection():
    """Restrict physical taps to possible nonzero sources and compare gate inputs."""
    from single_product_feedback_audit import greedy_slots, is_b3

    slots, _ = greedy_slots(6)
    gate_banks = [
        (((2, 1), (4, 1)), ((3, 1),)),
        (((0, 0),), ((1, 0),)),
        (((0, 0), (2, 1)), ((1, 0), (3, 1))),
    ]
    checks = 0
    for period in (223, 256):
        assert period > 3*max(slots) and is_b3(slots, period)
        banks = [[], []]
        for i, slot in enumerate(slots):
            for side, inputs in enumerate(gate_banks[i//2]):
                banks[side].extend(lag*period + slot - slots[parent] for parent, lag in inputs)
        assert all(len(set(bank)) == len(bank) and min(bank) > 0 for bank in banks)
        assert set(banks[0]).isdisjoint(banks[1])
        for dest in range(period):
            parents = []
            for bank in banks:
                arrivals = []
                for delay in bank:
                    offset, source = divmod(dest-delay, period)
                    if source in slots:
                        arrivals.append((slots.index(source), -offset))
                parents.append(sorted(arrivals))
            if dest in slots:
                expected = gate_banks[slots.index(dest)//2]
                assert parents == [sorted(side) for side in expected]
            else:
                assert not parents[0] or not parents[1]
            checks += 1
    return checks


if __name__ == '__main__':
    tests = residue_checks()
    pairs = bounded_gap_checks(3, 5) + bounded_gap_checks(5, 7)
    matrices, cycles = matrix_cycle_checks()
    field = field_five_checks(12)
    print(f'{tests} subcube/modulus checks, {pairs} sound pin pairs, '
          f'{matrices} matrices ({cycles} nonzero cycles), and {field} GF(16) inputs passed')
    print(f'{check_gate_projection()} slot and off-slot parent checks passed')
