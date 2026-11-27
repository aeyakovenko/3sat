"""Check small affine terminal obstructions from advertised-snapshot-offers.md."""

from itertools import combinations


def consistent(rows: tuple[int, ...], dimension: int) -> bool:
    mask = (1 << dimension) - 1
    return any(all(((row & value & mask).bit_count() % 2) == (row >> dimension)
                   for row in rows) for value in range(1 << dimension))


def shortest_contradiction(rows: tuple[int, ...], dimension: int) -> int | None:
    target = 1 << dimension
    distances = {0: 0}
    for row in rows:
        smaller = distances.copy()
        for state, cost in distances.items():
            nxt = state ^ row
            if cost + 1 < smaller.get(nxt, len(rows) + 1):
                smaller[nxt] = cost + 1
        distances = smaller
    return distances.get(target)


def exhaustive(dimension: int) -> None:
    universe = tuple(range(1 << (dimension + 1)))
    failed = 0
    longest = 0
    for size in range(len(universe) + 1):
        for rows in combinations(universe, size):
            certificate = shortest_contradiction(rows, dimension)
            assert (certificate is None) == consistent(rows, dimension)
            if certificate is not None:
                failed += 1
                longest = max(longest, certificate)
    assert longest == dimension + 1
    print(f"dimension {dimension}: {failed} inconsistent systems, largest minimum support {longest}")


if __name__ == "__main__":
    for d in range(4):
        exhaustive(d)
