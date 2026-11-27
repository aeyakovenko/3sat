"""Finite checks for integer-polynomial images and frozen-bank bulk transformations."""

from bisect import bisect_left
from collections import defaultdict
from dataclasses import dataclass
from itertools import pairwise, product
from math import comb, factorial
from random import Random


def evaluate(coefficients, x, modulus):
    result = 0
    for coefficient in reversed(coefficients):
        result = (result * x + coefficient) % modulus
    return result


def valuation(x, b):
    return min(b, (x & -x).bit_length() - 1) if x else b


def reverse(x, width):
    result = 0
    for _ in range(width):
        result = 2 * result + (x & 1)
        x >>= 1
    return result


@dataclass(frozen=True)
class Leaf:
    centre: int
    depth: int
    fixed: int
    precision: int
    normalized: tuple[int, ...]
    bits: int

    def predecessor(self, address, cutoff, reversed_time):
        b, h, s = self.bits, self.depth, self.precision
        if (address - self.fixed) % (1 << s) or not cutoff:
            return None
        target = (address - self.fixed) >> s
        y = 0
        for i in range(b - s):
            if (evaluate(self.normalized, y, 1 << (i + 1)) - target) & (1 << i):
                y += 1 << i
        depth = h + b - s
        start = self.centre + (y << h)
        if reversed_time:
            lo = reverse(start, depth) << (b - depth)
            return min(cutoff, lo + (1 << (b - depth))) - 1 if lo < cutoff else None
        if start >= cutoff:
            return None
        return start + ((cutoff - 1 - start) >> depth << depth)


def image_leaves(coefficients, bits, initial=(0, 0)):
    modulus = 1 << bits
    frontier = [initial]
    leaves = []
    bad = defaultdict(int)
    while frontier:
        a, h = frontier.pop()
        shifted = [
            sum(
                coefficients[i] * comb(i, k) * pow(a, i - k, modulus)
                for i in range(k, len(coefficients))
            )
            * pow(2, h * k, modulus)
            % modulus
            for k in range(len(coefficients))
        ]
        s = min((valuation(v, bits) for v in shifted[1:]), default=bits)
        if s == bits or (
            valuation(shifted[1], bits) == s
            and all(valuation(v, bits) > s for v in shifted[2:])
        ):
            normalized = tuple([0] + [v >> s for v in shifted[1:]])
            leaves.append(Leaf(a, h, shifted[0], s, normalized, bits))
        else:
            bad[h] += 1
            frontier.extend([(a, h + 1), (a + (1 << h), h + 1)])
    bound = max(1, 2 * (len(coefficients) - 2))
    assert all(n <= bound for n in bad.values())
    return leaves


def reversed_prefix(length, bits):
    start = 0
    while start < length:
        width = (length - start).bit_length() - 1
        prefix_bits = bits - width
        yield reverse(start >> width, prefix_bits), prefix_bits
        start += 1 << width


class Archive:
    def __init__(self, polys, lengths, reversed_times, bits):
        self.bits = bits
        self.lengths = lengths
        self.reversed_times = reversed_times
        self.leaves = []
        self.directory = defaultdict(list)
        for i, (poly, length, rev) in enumerate(
            zip(polys, lengths, reversed_times, strict=True)
        ):
            assert rev or length == 1 << bits
            starts = reversed_prefix(length, bits) if rev else [(0, 0)]
            leaves = [
                leaf for start in starts for leaf in image_leaves(poly, bits, start)
            ]
            self.leaves.append(leaves)
            for s, residue in {
                (leaf.precision, leaf.fixed % (1 << leaf.precision)) for leaf in leaves
            }:
                self.directory[s, residue].append(i)

    def local(self, phase, addr, cutoff):
        possibilities = [
            leaf.predecessor(addr, cutoff, self.reversed_times[phase])
            for leaf in self.leaves[phase]
        ]
        return max((t for t in possibilities if t is not None), default=None)

    def earlier(self, phase, addr, cutoff):
        result = self.local(phase, addr, cutoff)
        if result is not None:
            return phase, result
        previous = -1
        for s in range(self.bits + 1):
            phases = self.directory[s, addr % (1 << s)]
            idx = bisect_left(phases, phase)
            if idx:
                previous = max(previous, phases[idx - 1])
        if previous < 0:
            return None
        end = self.local(previous, addr, self.lengths[previous])
        assert end is not None
        return previous, end


def differences(column, modulus):
    coefficients = []
    while column:
        coefficients.append(column[0])
        column = [(y - x) % modulus for x, y in pairwise(column)]
    return tuple(coefficients)


def newton(coeffs, x, modulus):
    return sum(comb(x, i) * c for i, c in enumerate(coeffs) if i <= x) % modulus


def exact_distance(bits, dimensions):
    modulus = 1 << bits
    side = min(modulus, 2 * bits)
    points = list(product(range(modulus), repeat=dimensions))
    generators = []
    for degrees in product(range(side), repeat=dimensions):
        cost = sum(valuation(factorial(j), bits) for j in degrees)
        if cost >= bits:
            continue
        column = []
        for x in points:
            value = 1 << cost
            for v, j in zip(x, degrees, strict=True):
                value *= comb(v, j) if j <= v else 0
            column.append(value % modulus)
        generators.append((modulus >> cost, column))
    least = len(points)
    checks = 0

    def visit(i, vector):
        nonlocal least, checks
        if i == len(generators):
            if any(vector):
                least = min(least, sum(v != 0 for v in vector))
            checks += 1
            return
        choices, column = generators[i]
        for _ in range(choices):
            visit(i + 1, vector)
            vector = [(v + c) % modulus for v, c in zip(vector, column, strict=True)]

    visit(0, [0] * len(points))
    max_degree = max(
        sum(h)
        for h in product(range(bits + 1), repeat=dimensions)
        if sum((1 << k) - 1 - k for k in h) < bits
    )
    assert least == 1 << (dimensions * bits - max_degree)
    return checks


class Transform:
    """Exact finite-difference coordinates. Only the test harness uses small b."""

    def __init__(self, bits, key, payload):
        self.bits = bits
        self.modulus = 1 << bits
        grid = range(2 * bits)
        self.key_table = differences(
            [key(x) % self.modulus for x in grid], self.modulus
        )
        along_value = [
            differences([payload(x, v) % self.modulus for v in grid], self.modulus)
            for x in grid
        ]
        self.table = tuple(
            differences([row[i] for row in along_value], self.modulus) for i in grid
        )

    def key(self, x):
        return newton(self.key_table, x, self.modulus)

    def payload(self, x, v):
        return newton(
            [newton(row, x, self.modulus) for row in self.table], v, self.modulus
        )

    def apply(self, x, v):
        return self.key(x), self.payload(x, v)

    def after(self, old):
        return Transform(
            self.bits,
            lambda x: self.key(old.key(x)),
            lambda x, v: self.payload(*old.apply(x, v)),
        )

    def inverse_key(self, key):
        x = 0
        for bit in range(self.bits):
            if (self.key(x) ^ key) & (1 << bit):
                x |= 1 << bit
        assert self.key(x) == key
        return x


class CompactBank:
    """Reference implementation with flat ordered maps instead of a balanced sequence tree."""

    def __init__(self, bits, initial):
        self.identity = Transform(bits, lambda x: x, lambda _x, v: v)
        self.whole = self.identity
        self.active = []
        self.segments = [self.identity]
        self.initial = initial

    def bulk(self, op):
        self.whole = op.after(self.whole)
        self.segments[-1] = op.after(self.segments[-1])

    def store(self, x, value):
        origin = self.whole.inverse_key(x)
        for j, (old, _, _) in enumerate(self.active):
            if old == origin:
                self.segments[j] = self.segments[j + 1].after(self.segments[j])
                del self.segments[j + 1]
                del self.active[j]
                break
        self.active.append((origin, x, value))
        self.segments.append(self.identity)

    def load(self, x):
        origin = self.whole.inverse_key(x)
        for j, (old, key, value) in enumerate(self.active):
            if old == origin:
                for op in self.segments[j + 1 :]:
                    key, value = op.apply(key, value)
                assert key == x
                return value
        return self.whole.payload(origin, self.initial[origin])


def xor_store_audit():
    checked = 0
    for guest_bits in range(1, 9):
        words = 1 << guest_bits
        key_bit = words * words
        scale = 2 * key_bit
        host_mask = words * scale - 1
        bank = [0] * words
        for target, replacement in [
            (a, (31 * a + k) % words) for k in (1, 3, 7) for a in range(words)
        ]:
            old = bank[target] // scale
            for address in range(words):
                u = -((target - address) ** 2) & host_mask
                indicator = (scale - (u + key_bit - (u ^ key_bit))) & host_mask
                assert indicator == (scale if address == target else 0)
                prev = bank[address]
                bank[address] = (prev + (replacement - old) * indicator) & host_mask
                assert bank[address] == (replacement * scale if address == target else prev)
                checked += 1
    return checked


def precision_audit():
    checked = 0
    for width in range(1, 7):
        size = 1 << width
        modulus = 1 << (3 * width)
        mask = (1 << (width - 1))
        for address, target in product(range(size), repeat=2):
            positive = (address - target) % modulus
            negative = (target - address) % modulus
            plus = positive + mask - (positive ^ mask)
            minus = negative + mask - (negative ^ mask)
            assert (size - plus) * (size - minus) == size * size * (address == target)
            checked += 1
        for precision in range(width + 1):
            step = 1 << precision
            count = size // step
            power = precision * (count - 1) + valuation(factorial(count - 1), 3 * width)
            for target in range(size):
                residue = target % step
                same_chart = range(residue, size, step)
                values = []
                for address in same_chart:
                    product_at_address = 1
                    for other in same_chart:
                        if other != target:
                            product_at_address = product_at_address * (address - other) % modulus
                    values.append(product_at_address)
                    if address != target:
                        assert product_at_address == 0
                survivor = values[target // step]
                assert valuation(survivor, 3 * width) == min(power, 3 * width)
                difference = sum(
                    (-1) ** (count - 1 - j) * comb(count - 1, j) * val
                    for j, val in enumerate(values)
                )
                assert valuation(difference % modulus, 3 * width) == min(power, 3 * width)
                checked += 1
    return checked


def main():
    rng = Random(19417)
    image_checks = archives = bank_checks = supports = 0
    for b in range(1, 9):
        modulus = 1 << b
        for _ in range(35):
            polys = [
                [rng.randrange(modulus) for _ in range(rng.randrange(1, 8))]
                for _ in range(5)
            ]
            revs = [rng.randrange(2) == 1 for _ in polys]
            lengths = [rng.randrange(modulus + 1) if rev else modulus for rev in revs]
            archive = Archive(polys, lengths, revs, b)
            last = {}
            for i, (poly, rev, length) in enumerate(
                zip(polys, revs, lengths, strict=True)
            ):
                image = {
                    evaluate(poly, reverse(t, b) if rev else t, modulus)
                    for t in range(length)
                }
                from_balls = {
                    v
                    for v in range(modulus)
                    if any(
                        (v - ball.fixed) % (1 << ball.precision) == 0
                        for ball in archive.leaves[i]
                    )
                }
                assert image == from_balls
                image_checks += 1
                for t in range(length + 1):
                    probes = [rng.randrange(modulus)] if t < length else range(modulus)
                    for addr in probes:
                        assert archive.earlier(i, addr, t) == last.get(addr)
                        archives += 1
                    if t < length:
                        last[evaluate(poly, reverse(t, b) if rev else t, modulus)] = (
                            i,
                            t,
                        )
        max_bits = (2 * b - 1).bit_length()
        index = (1 << b.bit_length() - 1) - 1 if b > 1 else 1
        assert valuation(factorial(index), b) < b
        scale = 1 << (b - 1 - valuation(factorial(index), b))
        sparse_values = [
            scale * factorial(index) * comb(x, index) % modulus if x >= index else 0
            for x in range(modulus)
        ]
        assert sum(v != 0 for v in sparse_values) == modulus // (index + 1)
        for _ in range(90):
            coeffs = [rng.randrange(modulus) for _ in range(2 * b + 4)]
            vals = [evaluate(coeffs, x, modulus) for x in range(modulus)]
            q = min(valuation(v, b) for v in vals)
            if q == b:
                continue
            lowest = [(v >> q) & 1 for v in vals]
            assert all(lowest[x] == lowest[x % (1 << max_bits)] for x in range(modulus))
            assert sum(v != 0 for v in vals) * (1 << max_bits) >= modulus
            supports += 1
    for b in (2, 3, 4, 5):
        modulus = 1 << b
        dense = [rng.randrange(modulus) for _ in range(modulus)]
        bank = CompactBank(b, dense.copy())
        for i in range(70):
            if i % 3:
                a, c, r = (
                    rng.randrange(modulus) | 1,
                    rng.randrange(modulus),
                    rng.randrange(modulus),
                )
                coeffs = [rng.randrange(modulus) for _ in range(5)]

                def key(x, a=a, c=c, r=r, modulus=modulus):
                    return (a * x + c + 2 * r * x * x) % modulus

                def val(x, v, cs=coeffs, modulus=modulus):
                    return (
                        cs[0] + cs[1] * x + cs[2] * v + cs[3] * x * v + cs[4] * v * v
                    ) % modulus

                op = Transform(b, key, val)
                updated = [None] * modulus
                for x, v in enumerate(dense):
                    updated[key(x)] = val(x, v)
                assert None not in updated
                dense = updated
                bank.bulk(op)
            else:
                x, v = rng.randrange(modulus), rng.randrange(modulus)
                dense[x] = v
                bank.store(x, v)
            assert len(bank.segments) == 1 + len({entry[0] for entry in bank.active})
            for key, value in enumerate(dense):
                assert bank.load(key) == value
                bank_checks += 1
        for x, a in product(range(modulus), repeat=2):
            h = (x - a) % modulus >> (b - 1)
            hn = (a - x) % modulus >> (b - 1)
            assert (1 - h) * (1 - hn) == (x == a)
    distance_tests = sum(
        exact_distance(b, d)
        for b, d in ((1, 1), (2, 1), (3, 1), (4, 1), (1, 2), (2, 2), (1, 3))
    )
    print(
        f"{image_checks} exact image partitions, {archives} historical predecessors, "
        f"{bank_checks} full-memory comparisons, {supports} checked support classes, "
        f"{distance_tests} exhaustively enumerated polynomial functions, "
        f"{xor_store_audit()} one-XOR simulated point-write checks, "
        f"{precision_audit()} threshold and sharp difference checks"
    )


if __name__ == "__main__":
    main()
