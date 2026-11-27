"""Independently compare grouped restrictions, sparse correction and physical pages."""

from collections import Counter
from itertools import combinations
from math import comb
from random import Random


def xor_sum(bits):
    result = 0
    for bit in bits:
        result ^= bit
    return result


def coefficients(table):
    """Unique ANF on a numerical initial segment, a downward-closed Boolean domain."""
    result = list(table)
    for coord in range((len(result) - 1).bit_length()):
        bit = 1 << coord
        for mask in range(len(result)):
            if mask & bit:
                result[mask] ^= result[mask ^ bit]
    return result


def grouped_words(table, low_bits, groups):
    """Clamp high groups, sum their finite differences, and return physical words."""
    size = len(table)
    width = (size - 1).bit_length()
    lanes = 1 << low_bits
    high_width = width - low_bits
    assert 1 <= groups <= high_width
    bounds = [high_width * i // groups for i in range(groups + 1)]
    masks = [((1 << (b - a)) - 1) << a for a, b in zip(bounds, bounds[1:])]
    pages = (size + lanes - 1) // lanes
    parts = []
    for i, absent in enumerate(masks):
        start, end = bounds[i], bounds[i + 1]
        left = (1 << start) - 1

        def insert_zero(key):
            return (key & left) | ((key >> start) << end)

        def remove_field(key):
            return (key & left) | ((key >> end) << start)

        part = []
        for key in range(1 << (high_width - end + start)):
            address = insert_zero(key) * lanes
            part.append(sum(table[x] << (x - address)
                            for x in range(address, min(address + lanes, size))))
        for earlier in masks[:i]:
            reduced_mask = remove_field(earlier)
            for key in reversed(range(len(part))):
                part[key] ^= part[key & ~reduced_mask]
        parts.append((start, end, left, part))

    def word(high):
        return xor_sum(part[(high & left) | ((high >> end) << start)]
                       for start, end, left, part in parts)

    result = [word(high) for high in range(pages)]
    if size % lanes:
        result[-1] &= (1 << (size % lanes)) - 1
    return result


def bits(words, lanes, size):
    return [(words[x // lanes] >> (x % lanes)) & 1 for x in range(size)]


def cofactor_words(table, low_bits, degree):
    """Interpolate from sparse high addresses, then descend coefficients by degree."""
    size = len(table)
    lanes = 1 << low_bits
    highs = (size - 1).bit_length() - low_bits
    masks = [[sum(1 << i for i in subset) for subset in combinations(range(highs), j)]
             for j in range(min(highs, degree) + 1)]
    values = {}
    for layer in masks:
        for h in layer:
            start = h * lanes
            values[h] = sum(table[x] << (x - start)
                            for x in range(start, min(size, start + lanes)))
    for j in range(highs):
        bit = 1 << j
        for h in values:
            if h & bit:
                values[h] ^= values[h ^ bit]
    # In colex order terms containing the top variable form a consecutive tail.
    packed = [[values[h] for h in sorted(layer)] for layer in masks]
    def descend(level, layers):
        if level == 0:
            return layers[0]
        split = [comb(level - 1, j) if j <= level - 1 else 0
                 for j in range(len(layers))]
        left = [row[:n] for row, n in zip(layers, split) if n]
        right = [row.copy() for row in left]
        for j in range(len(right)):
            if j + 1 < len(layers):
                add = layers[j + 1][split[j + 1]:]
                if add:
                    assert len(add) == len(right[j])
                    right[j] = [a ^ b for a, b in zip(right[j], add)]
        return descend(level - 1, left) + descend(level - 1, right)
    result = descend(highs, packed)[:(size + lanes - 1) // lanes]
    if size % lanes:
        result[-1] &= (1 << (size % lanes)) - 1
    return result


def dyadic_cover(start, stop):
    while start < stop:
        cap = 1 << ((stop - start).bit_length() - 1)
        length = min(cap, start & -start) if start else cap
        yield start, length
        start += length


def emit_intervals(pieces, width, low_bits):
    """Descend each aligned restriction and join it at its physical offset."""
    result = 0
    end = 0
    for stop, polynomial in pieces:
        assert end < stop <= 1 << width
        for start, size in dyadic_cover(end, stop):
            assert start % size == 0
            free = size.bit_length() - 1
            restricted = Counter()
            for monomial in polynomial:
                high = monomial & -size
                if high & start == high:
                    restricted[monomial & (size - 1)] ^= 1
            terms = [mask for mask, on in restricted.items() if on]
            values = [xor_sum(int(z & term == term) for term in terms)
                      for z in range(size)]
            lane_bits = min(free, low_bits)
            degree = max((mask.bit_count() for mask in terms), default=0)
            for j, word in enumerate(cofactor_words(values, lane_bits, degree)):
                result |= word << (start + (j << lane_bits))
        end = stop
    return [(result >> i) & 1 for i in range(end)]


def multiply(a, b, modulus, width):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a >> width:
            a ^= modulus
        b >>= 1
    return result


def spread_direction(tag, code, field_bits, blocks, modulus):
    mask = (1 << field_bits) - 1
    delta = code
    for j in range(1, blocks):
        coefficient = tag & mask
        tag >>= field_bits
        delta |= multiply(coefficient, code, modulus, field_bits) << (field_bits * j)
    return delta


def certify_value(corrupted, position, errors, degree, modulus):
    width = (len(corrupted) - 1).bit_length()
    field_bits = degree + 1
    blocks = width // field_bits
    assert (1 << (field_bits * (blocks - 1))) >= 2 * errors + 1
    votes = []
    for tag in range(2 * errors + 1):
        votes.append(xor_sum(corrupted[position ^ spread_direction(
            tag, z, field_bits, blocks, modulus)] for z in range(1, 1 << field_bits)))
    return int(sum(votes) > errors)


def polynomial_table(width, degree, random):
    coeffs = [random.randrange(2) if x.bit_count() <= degree else 0
              for x in range(1 << width)]
    return coefficients(coeffs)


def run():
    counts = Counter()
    rng = Random(20261127)
    for width in range(3, 10):
        for low_bits in range(1, min(4, width - 1) + 1):
            for groups in range(1, width - low_bits + 1):
                for trial in range(5):
                    table = polynomial_table(width, groups - 1, rng)
                    size = rng.randrange((1 << (width - 1)) + 1, (1 << width) + 1)
                    if trial == 0:
                        size = 1 << width
                    table = table[:size]
                    assert bits(cofactor_words(table, low_bits, groups - 1),
                                1 << low_bits, size) == table
                    assert bits(grouped_words(table, low_bits, groups),
                                1 << low_bits, size) == table
                    counts['bounded-degree physical files'] += 1
                    counts['physical output bits'] += size
    # Check the group-missing condition on every Boolean truth table at width four.
    for mask in range(1 << 16):
        table = [(mask >> x) & 1 for x in range(16)]
        anf = coefficients(table)
        expected = not any(bit and x & 4 and x & 8 for x, bit in enumerate(anf))
        assert (bits(grouped_words(table, 2, 2), 4, 16) == table) == expected
        counts['all four-bit functions classified'] += 1
    for degree, width, modulus in [(1, 6, 0b111), (2, 9, 0b1011), (3, 12, 0b10011)]:
        field_bits = degree + 1
        blocks = width // field_bits
        for errors in [0, 1, 2, 3, 5]:
            g = polynomial_table(width, degree, rng)
            marked = set(rng.sample(range(len(g)), errors))
            f = [v ^ int(i in marked) for i, v in enumerate(g)]
            trials = set(rng.sample(range(len(g)), min(50, len(g)))) | marked
            for x in trials:
                assert certify_value(f, x, errors, degree, modulus) == g[x]
                counts['sparse-correction positions'] += 1
            sets = [{spread_direction(tag, z, field_bits, blocks, modulus)
                     for z in range(1, 1 << field_bits)} for tag in range(2 * errors + 1)]
            assert all(len(a) == (1 << field_bits) - 1 and 0 not in a for a in sets)
            assert all(a.isdisjoint(b) for a, b in combinations(sets, 2))
            counts['disjoint-subspace families'] += 1
    for width in range(3, 10):
        for _ in range(30):
            stop = rng.randint((1 << (width - 1)) + 1, 1 << width)
            endpoints = sorted(rng.sample(range(1, stop), rng.randrange(1, min(15, stop))))
            endpoints.append(stop)
            pieces = []
            truth = []
            for limit in endpoints:
                terms = rng.sample(range(1 << width), rng.randint(0, min(15, 1 << width)))
                pieces.append((limit, terms))
                truth.extend(xor_sum(int(x & term == term) for term in terms)
                             for x in range(len(truth), limit))
            assert emit_intervals(pieces, width, min(3, width)) == truth
            counts['piecewise physical files'] += 1
            counts['piecewise active intervals'] += len(pieces)
            counts['piecewise valid bits'] += stop
    print(dict(counts))


if __name__ == '__main__':
    run()
