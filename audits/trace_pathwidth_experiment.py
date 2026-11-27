"""Finite tests of consecutive-visit authentication and computation-graph width."""

from itertools import product


def possible_predecessors(positions):
    """Enumerate earlier same-address links, requiring an unused successor port."""
    parents = []
    has_successor = set()

    def extend(time):
        if time == len(positions):
            yield tuple(parents)
            return
        previous = [i for i in range(time) if positions[i] == positions[time]]
        if not previous:
            parents.append(None)
            yield from extend(time + 1)
            parents.pop()
            return
        for i in previous:
            if i in has_successor:
                continue
            has_successor.add(i)
            parents.append(i)
            yield from extend(time + 1)
            parents.pop()
            has_successor.remove(i)

    yield from extend(0)


def verify_links():
    walks = 0
    for moves in product((-1, 0, 1), repeat=7):
        positions = [0]
        for move in moves:
            positions.append(positions[-1] + move)
        earliest, latest = 0, -1
        seen = {}
        expected = []
        for time, address in enumerate(positions):
            first = not earliest <= address <= latest
            assert first == (address not in seen)
            expected.append(seen.get(address))
            seen[address] = time
            earliest, latest = min(earliest, address), max(latest, address)
        assert list(possible_predecessors(positions)) == [tuple(expected)]
        walks += 1
    return walks


def pathwidth(positions):
    """Exact minimum vertex-separation number by DP on prefixes of an ordering."""
    size = len(positions)
    neighbors = [0] * size

    def link(a, b):
        neighbors[a] |= 1 << b
        neighbors[b] |= 1 << a

    previous = {}
    for i, address in enumerate(positions):
        if i:
            link(i - 1, i)
        if address in previous:
            link(previous[address], i)
        previous[address] = i

    width = bytearray(1 << size)
    for subset in range(1, 1 << size):
        prior = size
        boundary = 0
        bits = subset
        while bits:
            bit = bits & -bits
            v = bit.bit_length() - 1
            boundary += int(bool(neighbors[v] & ~subset))
            prior = min(prior, width[subset ^ bit])
            bits ^= bit
        width[subset] = max(prior, boundary)
    return width[-1]


def main():
    print(f"Unique predecessor chains on {verify_links()} tape-head walks")
    for length in range(2, 9):
        sweep = list(range(length))
        width = pathwidth(sweep + sweep[::-1])
        assert width <= 3
        print(f"Forward/reverse sweep, {length} cells: pathwidth {width}")
    for side in range(2, 4):
        row_major = list(range(side * side))
        col_major = [row * side + col for col in range(side) for row in range(side)]
        width = pathwidth(row_major + col_major)
        assert width >= side - 1
        print(f"Row/column scan, {side} by {side}: pathwidth {width}")


if __name__ == "__main__":
    main()
