"""Check cyclic Walsh signatures, all C5-to-C6 affine maps, and their hard-suite images."""

from collections import Counter
from functools import reduce
from itertools import permutations
from operator import xor

FIVE_BIT_SUITE = (9, 7, 19, 3, 25, 29, 5, 31, 14, 12, 23, 11, 18, 26, 13, 27)


def cover(mask, size):
    return all(((mask >> i) | (mask >> ((i + 1) % size))) & 1 for i in range(size))


def walsh(coefficients):
    coeffs = coefficients.copy()
    distance = 1
    while distance < len(coeffs):
        for start in range(0, len(coeffs), 2 * distance):
            for i in range(start, start + distance):
                a, b = coeffs[i], coeffs[i + distance]
                coeffs[i], coeffs[i + distance] = a + b, a - b
        distance *= 2
    return coeffs


def signed_trace(mask, size):
    a, b, c, d = 1, 0, 0, 1
    for i in range(size):
        sign = -1 if mask >> i & 1 else 1
        a, b, c, d = a + b, sign * a, c + d, sign * c
    return (a + d) * (-1 if mask.bit_count() % 2 else 1)


def rotate(mask, size, offset):
    word_mask = (1 << size) - 1
    return ((mask << offset) | (mask >> (size - offset))) & word_mask


def check_coefficients():
    previous_count = 11
    for size in range(6, 16):
        values = [int(cover(x, size)) for x in range(1 << size)]
        coefficients = walsh(values)
        assert all(c == signed_trace(i, size) for i, c in enumerate(coefficients))
        required = 2 * previous_count - sum(values)
        eligible = {i for i, c in enumerate(coefficients) if i and abs(c) == required}
        expected = {rotate(7, size, i) for i in range(size)}
        if size == 6:
            expected.update((21, 42))
        if size == 8:
            expected.update((17, 34, 68, 136))
        assert eligible == expected
        peak = max(map(abs, coefficients[1:]))
        assert {i for i, c in enumerate(coefficients) if abs(c) == peak} == {
            1 << j for j in range(size)
        }
        previous_count = sum(values)
        print(f'length {size}, covers {previous_count}, eligible normals {len(eligible)}')


def span(basis):
    values = [0]
    for a in basis:
        if a in values:
            return []
        values += [a ^ x for x in values]
    return values


def affine_five_to_six():
    source = {x for x in range(32) if cover(x, 5)}
    zero = reduce(xor, source, 0)
    centered_source = {x ^ zero for x in source}
    basis = []
    for a in sorted(centered_source):
        if a not in span(basis):
            basis.append(a)
    assert len(basis) == 5
    index = {a: j for j, a in enumerate(span(basis))}
    source_coeffs = [index[a] for a in centered_source]
    mappings = set()
    plane_sizes = Counter()
    for normal in range(1, 64):
        for bias in (0, 1):
            target = {x for x in range(64)
                      if cover(x, 6) and (x & normal).bit_count() % 2 == bias}
            if len(target) != len(source):
                continue
            origin = reduce(xor, target, 0)
            shifted = {x ^ origin for x in target}
            count = 0
            for image in permutations(sorted(shifted - {0}), 5):
                expanded = span(image)
                if not expanded or any(expanded[j] not in shifted for j in source_coeffs):
                    continue
                output = tuple(origin ^ expanded[index[x ^ zero]] for x in range(32))
                assert len(set(output)) == 32
                assert all(cover(x, 5) == cover(y, 6) for x, y in enumerate(output))
                assert output not in mappings
                mappings.add(output)
                count += 1
            plane_sizes[count] += 1
    assert plane_sizes == {0: 2, 10: 6}
    return mappings


def dihedral(x, n, offset, orientation):
    return sum(((x >> j) & 1) << ((offset + orientation * j) % n) for j in range(n))


def dihedral_xor_maps():
    maps = set()
    # Insert between positions zero and one, then rotate the target site.
    for target_offset in range(6):
        for source_offset in range(5):
            for orientation in (1, -1):
                output = []
                for x in range(32):
                    y = dihedral(x, 5, source_offset, orientation)
                    bit = (y ^ (y >> 1)) & 1
                    extended = (y & 1) | (bit << 1) | ((y & ~1) << 1)
                    output.append(rotate(extended, 6, target_offset))
                maps.add(tuple(output))
    return maps


if __name__ == '__main__':
    check_coefficients()
    mappings = affine_five_to_six()
    assert mappings == dihedral_xor_maps()
    suites = {frozenset(g[x] for x in FIVE_BIT_SUITE) for g in mappings}
    assert len(mappings) == len(suites) == 60
    from small_cyclic_selector_clock import feasible
    assert all(feasible(sorted(suite), 6, 3, 5) for suite in suites)
    print('C5 to C6: 60 affine maps and 60 distinct images of the inherited suite')
