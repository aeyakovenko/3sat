"""Finite checks for substring-template-rigidity.md, using only Python's standard library."""

from itertools import combinations


def rotations(word, width):
    mask = (1 << width) - 1
    for shift in range(width):
        yield ((word << shift) | (word >> (width - shift))) & mask


def periodic_seeds(side):
    # Smallest b satisfying 2^(2b) >= side^3.
    width = ((side**3 - 1).bit_length() + 1) // 2
    radius = (width - 1) // 32
    error_masks = [
        sum(1 << pos for pos in positions)
        for weight in range(radius + 1)
        for positions in combinations(range(width), weight)
    ]
    forbidden = bytearray(1 << width)
    seeds = []
    for word in range(1 << width):
        if forbidden[word]:
            continue
        seeds.append(word)
        if len(seeds) == side:
            return width, seeds
        for rotate in rotations(word, width):
            for error in error_masks:
                forbidden[rotate ^ error] = 1
    raise AssertionError(f"Only {len(seeds)} seeds available at side {side}")


def minimum_rotated_distance(seeds, width):
    smallest = width
    for i, word in enumerate(seeds):
        for rotate in rotations(word, width):
            for previous in seeds[:i]:
                smallest = min(smallest, (rotate ^ previous).bit_count())
    return smallest


def rank_one_check():
    # Each four-bit row is appended in displayed, row-major order.
    approximants = set()
    for left in range(16):
        for right in range(16):
            matrix = 0
            for row in range(4):
                active = left & (1 << (3 - row))
                matrix = (matrix << 4) | (right if active else 0)
            approximants.add(matrix)

    def distance(matrix):
        return min((matrix ^ other).bit_count() for other in approximants)

    for matrix in range(1 << 16):
        nearest = distance(matrix)
        if nearest <= 1:
            continue
        clear_distances = [
            distance(matrix ^ (1 << bit)) for bit in range(16) if matrix & (1 << bit)
        ]
        assert nearest == 2 and all(d == 1 for d in clear_distances)
        return matrix, nearest, clear_distances
    raise AssertionError("No four-by-four witness")


if __name__ == "__main__":
    for side in (128, 256, 512):
        width, seeds = periodic_seeds(side)
        distance = minimum_rotated_distance(seeds, width)
        assert 32 * distance >= width
        print(f"side={side} width={width} seeds={len(seeds)} min_rotated_distance={distance}")
    matrix, distance, clear_distances = rank_one_check()
    print(f"first={matrix:016b} rank_one_distance={distance} clearing_one={clear_distances}")
