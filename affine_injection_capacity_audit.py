"""Check exact affine injection capacities, the dyadic construction, and collision fibers."""
from itertools import combinations, permutations

from affine_permutation_capacity_audit import pack


def predicted(q, m):
    return sum((q // t).bit_length() - 1 for t in range(1, m+1))


def exhaust(q, m):
    width = (q-1).bit_length()
    allowed = {pack(x, width) for x in permutations(range(q), m)}
    maximum = 0
    for anchor in combinations(range(q), m):
        # All orders of any one anchor are equivalent by permuting the rows.
        translated = {v ^ pack(anchor, width) for v in allowed}
        layer = {frozenset({0})}
        dimension = -1
        while layer:
            dimension += 1
            extended = set()
            for space in layer:
                for v in translated - space:
                    coset = {v ^ x for x in space}
                    if v == min(coset) and coset <= translated:
                        extended.add(space | coset)
            layer = extended
        maximum = max(maximum, dimension)
    assert maximum == predicted(q, m)


def audit_tree(q, m):
    width = (q-1).bit_length()
    h = (q // m).bit_length() - 1
    blocks = q >> h
    selected = set(range(0, 2*(blocks//2), 2))
    for node in range(blocks):
        if len(selected) == m:
            break
        selected.add(node)
    marked = sorted(node << h for node in selected)
    assert len(marked) == m
    directions = []
    for j in range(1, q.bit_length()):
        level = {}
        for i, leaf in enumerate(marked):
            node = leaf >> j
            if node < q >> j:
                level[node] = level.get(node, 0) | (1 << (i * width + j-1))
        assert len(level) == min(m, q >> j)
        directions.extend(level.values())
    assert len(directions) == predicted(q, m)
    used = 0
    for d in directions:
        assert d and not d & used
        used |= d
    base = pack(marked, width)
    for sample in range(8):
        table = base
        for i, direction in enumerate(directions):
            if ((46*i + 53*sample) % 17) < 2*sample:
                table ^= direction
        values = [(table >> (width*i)) & ((1 << width)-1) for i in range(m)]
        assert len(set(values)) == m and all(v < q for v in values)


def test_collision_flats(m, bits):
    """All codimension 0, 1, 2 affine flats, via truth table masks for linear forms."""
    n = m * bits
    u = 1 << bits
    size = 1 << n
    full = (1 << size) - 1
    bad = 0
    for x in range(size):
        if len({x >> (i*bits) & (u-1) for i in range(m)}) < m:
            bad |= 1 << x
    one = [sum(1 << x for x in range(size) if (form & x).bit_count() & 1)
           for form in range(size)]
    tested = 0

    def verify(flat, codim):
        nonlocal tested
        count = flat.bit_count()
        assert count == size >> codim
        bound = m * (m-1)//2 + (1 << codim) - 1
        assert u * (flat & bad).bit_count() <= count * bound
        tested += 1

    verify(full, 0)
    for a in range(1, size):
        for h in (one[a], full ^ one[a]):
            verify(h, 1)
        for b in range(a+1, size):
            if b < (a ^ b):  # a,b are the two least nonzero vectors of their span
                for h in (one[a], full ^ one[a]):
                    verify(h & one[b], 2)
                    verify(h & (full ^ one[b]), 2)
    return tested


if __name__ == '__main__':
    for q in range(1, 6):
        for m in range(1, q+1):
            exhaust(q, m)
    for q in range(1, 82):
        for m in range(1, q+1):
            audit_tree(q, m)
    flats = sum(test_collision_flats(m,b) for m,b in [(2,2), (2,3), (3,3)])
    print('15 exact exhaustive capacities, 3321 dyadic constructions,',
          flats, 'affine-flat collision bounds')
