"""Exhaust affine operand restrictions for short modular word additions."""

from itertools import combinations, product


def spans(basis):
    values = [0]
    for direction in basis:
        values.extend([value ^ direction for value in values])
    return values


def reduced_bases(bits, dimension):
    for pivots in combinations(range(bits), dimension):
        free = [index for index in range(bits) if index not in pivots]
        slots = [(row, col) for row, pivot in enumerate(pivots) for col in free if col > pivot]
        for assignment in range(1 << len(slots)):
            rows = [1 << pivot for pivot in pivots]
            for index, (row, column) in enumerate(slots):
                if assignment >> index & 1:
                    rows[row] |= 1 << column
            yield rows, free


def bitset(points):
    return sum(1 << point for point in points)


def triangular(width):
    masks = {}
    for choices in product(range(6), repeat=width - 1):
        points = []
        for x, y in product(range(1 << width), repeat=2):
            carry = 0
            for index, choice in enumerate(choices):
                a, b = (x >> index) & 1, (y >> index) & 1
                forms = (a ^ carry, b ^ carry, a ^ b)
                if forms[choice // 2] != choice % 2:
                    break
                carry = (a & b) ^ (a & carry) ^ (b & carry)
            else:
                points.append(x | y << width)
        assert len(points) == 1 << (width + 1)
        mask = bitset(points)
        assert mask not in masks
        masks[mask] = choices
    return masks


def audit(width):
    bits = 2 * width
    low = (1 << width) - 1
    outputs = [((pair & low) + (pair >> width)) & low for pair in range(1 << bits)]
    charts = triangular(width)
    incidence = [sum((mask >> value) & 1 for mask in charts) for value in range(1 << bits)]
    assert set(incidence) == {3 ** (width - 1)}

    total = 0
    affine = 0
    largest = set()
    for dimension in range(bits + 1):
        for basis, free in reduced_bases(bits, dimension):
            directions = spans(basis)
            for base in spans([1 << index for index in free]):
                total += 1
                delta = [outputs[base ^ row] ^ outputs[base] for row in basis]
                linear_values = spans(delta)
                if not all(outputs[base ^ point] == outputs[base] ^ prediction
                           for point, prediction in zip(directions, linear_values)):
                    continue
                affine += 1
                mask = bitset(base ^ point for point in directions)
                assert any(mask & chart == mask for chart in charts)
                if dimension == width + 1:
                    largest.add(mask)
    assert largest == set(charts)
    print(f'{width} bits: {total} nonempty operand flats, {affine} affine additions, '
          f'{len(charts)} maximal flats, {incidence[0]} through each point')


def sum_observations(width, masks, pair):
    bits = ((pair & ((1 << width) - 1)) + (pair >> width)) % (1 << width)
    return sum(((bits & mask).bit_count() % 2) << index for index, mask in enumerate(masks))


def check_scalar_elimination(width, mask, original):
    points = original
    coefficient = (mask >> (width - 1)) & 1
    for i in range(width - 2, -1, -1):
        incoming = (mask >> i) & 1 if i else 0
        if coefficient:
            chosen = [p for p in points if ((p ^ (p >> width)) >> i) & 1 == incoming]
            if chosen:
                points = chosen
                incoming = 0
            else:
                incoming = 1
        coefficient = incoming
    assert len(points) << (width // 2) >= len(original)
    base = points[0]
    vector_values = {p ^ base: sum_observations(width, [mask], p) ^
                     sum_observations(width, [mask], base) for p in points}
    basis = []
    covered = {0}
    for p in vector_values:
        if p not in covered:
            basis.append(p)
            covered.update([q ^ p for q in covered])
    assert covered == set(vector_values)
    assert all(vector_values[q ^ p] == vector_values[q] ^ vector_values[p]
               for p in basis for q in covered)


def audit_scalar(width):
    tested = 0
    for dimension in range(2 * width + 1):
        for basis, free in reduced_bases(2 * width, dimension):
            directions = spans(basis)
            for base in spans([1 << index for index in free]):
                points = [base ^ row for row in directions]
                for mask in range(1 << width):
                    check_scalar_elimination(width, mask, points)
                    tested += 1
    print(f'{width} bits: {tested} scalar masks on affine operand flats checked')


def check_vector_elimination(width, masks, original):
    points = original
    coefficients = [sum(((mask >> i) & 1) << index for index, mask in enumerate(masks))
                    for i in range(width - 1, 0, -1)]
    block_size = 1 << len(masks)
    for start in range(0, len(coefficients), block_size):
        end = min(start + block_size, len(coefficients))
        preferred = {}
        if end - start == block_size:
            locations = {0: start}
            running = 0
            for row in range(start, end):
                running ^= coefficients[row]
                if running in locations:
                    first = locations[running]
                    if first > start:
                        preferred[first - 1] = 0
                    preferred.update((j, 1) for j in range(first, row))
                    break
                locations[running] = row + 1
            else:
                raise AssertionError('missing zero-sum interval')
        for row in range(start, end):
            if not coefficients[row]:
                continue
            value = preferred.get(row, 0)
            lane = width - 2 - row
            subset = [p for p in points if ((p ^ (p >> width)) >> lane) & 1 == value]
            if subset:
                points = subset
            else:
                value ^= 1
            if value and row + 1 < len(coefficients):
                coefficients[row + 1] ^= coefficients[row]
    h = width - 1
    assert len(points) << (h - h // block_size) >= len(original)
    base = points[0]
    obs = {p ^ base: sum_observations(width, masks, p) ^ sum_observations(width, masks, base)
           for p in points}
    covered = {0}
    for direction, delta in obs.items():
        if direction in covered:
            continue
        for p in covered:
            assert obs[p ^ direction] == obs[p] ^ delta
        covered.update([p ^ direction for p in covered])
    assert covered == set(obs)


def audit_first_stage_hyperplanes():
    charts = []
    for first, second in product(range(6), repeat=2):
        plane = []
        for point in range(16):
            a, b, x, y = [(point >> i) & 1 for i in range(4)]
            if (a, b, a ^ b)[first // 2] != first % 2:
                continue
            carry = a & b
            if (x ^ carry, y ^ carry, x ^ y)[second // 2] == second % 2:
                plane.append(point)
        assert len(plane) == 4
        charts.append(bitset(plane))
    assert len(set(charts)) == 36
    for mask in range(1, 16):
        for rhs in (0, 1):
            hyperplane = bitset(p for p in range(16) if (p & mask).bit_count() % 2 == rhs)
            assert any(chart & hyperplane == chart for chart in charts)
    print('All 30 first-stage affine hyperplanes contain a two-dimensional carry chart')


def audit_vectors():
    from random import Random

    generator = Random(25711)
    tested = 0
    for width in range(3, 13):
        for count in (1, 2, 3):
            for _ in range(30):
                base = generator.getrandbits(2 * width)
                directions = [generator.getrandbits(2 * width) for _ in range(7)]
                points = sorted({base ^ q for q in spans(directions)})
                masks = [generator.getrandbits(width) for _ in range(count)]
                check_vector_elimination(width, masks, points)
                tested += 1
    print(f'{tested} correlated vector-output cases checked')


def audit_attainment():
    for width in range(1, 13):
        m = width // 2
        for x, y in product(range(1 << m), repeat=2):
            a = sum(((x >> i) & 1) << (2 * i) for i in range(m))
            b = sum(((y >> i) & 1) << (2 * i) for i in range(m))
            observed = sum(((a + b) >> (2 * i + 1)) & 1 for i in range(m)) % 2
            assert observed == (x & y).bit_count() % 2


if __name__ == '__main__':
    for word_width in range(1, 4):
        audit(word_width)
    assert len(triangular(4)) == 216
    for word_width in range(1, 4):
        audit_scalar(word_width)
    audit_first_stage_hyperplanes()
    audit_vectors()
    audit_attainment()
