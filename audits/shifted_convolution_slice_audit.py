"""Exhaust small affine restrictions of a vector of shifted binary inner products."""

from itertools import product


def split_index(point, length):
    return point & ((1 << length) - 1), point >> length


def shifted_inner_products(left, right, outputs):
    return sum(((left & (right >> h)).bit_count() % 2) << h for h in range(outputs))


def check_small(length, outputs):
    width = 2 * length + outputs - 1
    assert length - outputs in (0, 1)
    size = 1 << width
    full = (1 << size) - 1
    values = []
    cardinalities = []
    for point in range(size):
        left, right = split_index(point, length)
        expected = shifted_inner_products(left, right, outputs)
        values.append(expected)

        kept = (1 << outputs) - 1
        frozen = (left & ~kept) | ((left ^ 1) & 1)
        even_samples = sum(((right >> (2 * h)) & 1) << h for h in range(outputs))
        candidate = shifted_inner_products(frozen, right, outputs) ^ even_samples ^ 1
        assert candidate != expected
        assert (((candidate ^ expected) & (frozen ^ left)).bit_count() % 2) == 1

    affines = []
    for linear in range(1 << width):
        bits = sum(((linear & point).bit_count() % 2) << point for point in range(size))
        affines.extend([bits, full ^ bits])
    slices = [(0, full)]
    if length - outputs == 1:
        slices.extend((1, mask) for mask in affines[2:])

    targets = [
        sum(((value >> h) & 1) << point for point, value in enumerate(values))
        for h in range(outputs)
    ]
    certifications = 0
    minima = [size] * (length - outputs + 1)
    for codimension, points in slices:
        agreements = [
            {points & ~(target ^ affine) for affine in affines} for target in targets
        ]
        minimum = size
        for choices in product(*agreements):
            common = points
            for mask in choices:
                common &= mask
            minimum = min(minimum, common.bit_count())
            certifications += 1
        cardinalities.append(minimum)
        minima[codimension] = min(minima[codimension], minimum)
        assert minimum > 0
        lower_numerator = (1 << length) - ((1 << outputs) - 1) * (1 << codimension)
        assert minimum * (1 << (length + outputs)) >= points.bit_count() * lower_numerator
    assert all(cardinalities)
    return len(slices), certifications, minima, size


def main():
    for length, outputs in ((2, 1), (2, 2), (3, 2)):
        flats, maps, minima, cases = check_small(length, outputs)
        print(
            f"d={length}, m={outputs}: {flats} large flats, {maps} affine outputs; "
            f"minimum hits by codimension {minima}; {cases} upper-slice points"
        )


if __name__ == "__main__":
    main()
