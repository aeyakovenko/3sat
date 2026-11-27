"""Check the ternary incidence and binary rank calculation in small dimensions."""

from itertools import product


def point_representatives(dimension):
    for first_one in range(dimension):
        for suffix in product(range(3), repeat=dimension - first_one - 1):
            yield (0,) * first_one + (1,) + suffix


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def check(dimension):
    points = list(point_representatives(dimension))
    size = (3**dimension - 1) // 2
    degree = (3 ** (dimension - 1) - 1) // 2
    intersection = (3 ** (dimension - 2) - 1) // 2
    assert len(points) == size
    rows = []
    for point in points:
        row = 0
        for column, normal in enumerate(points):
            if sum(x * y for x, y in zip(point, normal)) % 3 == 0:
                row |= 1 << column
        assert row.bit_count() == degree
        assert all((previous & row).bit_count() == intersection for previous in rows)
        rows.append(row)
    rank = binary_rank(rows)
    assert rank >= size - 1
    print(f"dimension={dimension}, side={size}, degree={degree}, binary rank={rank}")


if __name__ == "__main__":
    for dimension in range(2, 7):
        check(dimension)
