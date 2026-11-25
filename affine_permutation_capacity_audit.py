"""Check affine dimensions in the physical binary array representation."""

from itertools import permutations


def pack(values, bits):
    return sum(value << (i * bits) for i, value in enumerate(values))


def exhaustive_capacity(q):
    # Relabeling input rows moves any affine family's base table to the identity.
    k = (q-1).bit_length()
    identity = pack(range(q), k)
    allowed = {pack(p, k) ^ identity for p in permutations(range(q))}
    layer = {frozenset({0})}
    counts = []
    while layer:
        counts.append(len(layer))
        extended = set()
        for space in layer:
            for offset in allowed.difference(space):
                coset = {x ^ offset for x in space}
                if min(coset) == offset and coset <= allowed:
                    extended.add(space.union(coset))
        layer = extended
    return counts


def blocks(q):
    start = 0
    for h in range(q.bit_length()-1, -1, -1):
        size = 1 << h
        if size & q:
            yield start, h
            start += size


def tree_directions(q):
    directions = []
    k = (q-1).bit_length()
    for start, height in blocks(q):
        for depth in range(height):
            chunk = 1 << (height-depth)
            for prefix in range(1 << depth):
                lo = start + prefix*chunk
                direction = sum((chunk//2) << (i*k) for i in range(lo, lo+chunk))
                directions.append(direction)
    return directions


def main():
    for q in range(1, 6):
        counts = exhaustive_capacity(q)
        assert len(counts)-1 == q-q.bit_count()
        print(f"q={q}: linear spaces through the identity by dimension {counts}")
    for q in range(1, 258):
        dirs = tree_directions(q)
        assert len(dirs) == q-q.bit_count()
        # Within a row each depth affects a different bit, and fixed-depth
        # prefixes affect disjoint rows. Every direction has a private output bit.
        used = 0
        for vector in dirs:
            assert vector and not vector & used
            used |= vector
        k = (q-1).bit_length()
        word_mask = (1 << k)-1
        base = pack(range(q), k)
        for sample in range(15):
            table = base
            for j, direction in enumerate(dirs):
                if (j*73 + sample*11) % 17 < sample:
                    table ^= direction
            assert sorted((table >> (i*k)) & word_mask for i in range(q)) == list(range(q))
    print("Dyadic construction through q=257 passed")


if __name__ == "__main__":
    main()
