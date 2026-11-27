"""Extract and check a positive list missed by a matrix of odd-pair filters.

labels[i][j] (i < j) is the bit vector of the filters retaining pair (i,j).
The certificate is one dependent canonical matching or nine chosen canonical
blocks and two even three-bit masks. Basis elimination recovers outside pairs.
"""

from itertools import combinations, product
import random


def canonical_reducer(labels):
    """Decompose a syndrome against the ordered, disjoint matching labels."""
    pivots = {}

    def reduce_label(value):
        coefficients = 0
        for bit in sorted(pivots, reverse=True):
            if value & (1 << bit):
                vector, matching = pivots[bit]
                value ^= vector
                coefficients ^= matching
        return value, coefficients

    for block in range(len(labels) // 2):
        residual, coefficients = reduce_label(labels[2 * block][2 * block + 1])
        coefficients ^= 1 << block
        if residual == 0:
            return coefficients, reduce_label
        pivots[residual.bit_length() - 1] = residual, coefficients
    return 0, reduce_label


def complete_partition(row_count, triangles, matching):
    groups = list(triangles)
    groups.extend((2*i, 2*i+1) for i in range(row_count // 2) if matching & (1 << i))
    used = {v for group in groups for v in group}
    assert len(used) == sum(map(len, groups))
    groups.extend((i,) for i in range(row_count) if i not in used)
    return tuple(groups)


def missed_partition(labels, groups):
    assert sorted(i for group in groups for i in group) == list(range(len(labels)))
    syndrome = 0
    witnessed = False
    for group in groups:
        for a, b in combinations(sorted(group), 2):
            witnessed = True
            syndrome ^= labels[a][b]
    return witnessed and syndrome == 0


def extract(labels):
    """Return a checked missed partition, or None if this search found none."""
    n = len(labels)
    dependent, reduce_label = canonical_reducer(labels)
    if dependent:
        groups = complete_partition(n, [], dependent)
        assert missed_partition(labels, groups)
        return groups

    masks = (0, 3, 5, 6)
    for selected in combinations(range(n // 2), 9):
        occupied = sum(1 << i for i in selected)
        choices = []
        for plane in (0, 1):
            triangles = [tuple(2 * selected[u + offset] + plane for offset in (0, 3, 6))
                         for u in range(3)]
            syndrome = []
            for triangle in triangles:
                a, b, c = triangle
                syndrome.append(labels[a][b] ^ labels[a][c] ^ labels[b][c])
            table = {}
            for mask in masks:
                active = [u for u in range(3) if mask & (1 << u)]
                value = 0
                for u in active:
                    value ^= syndrome[u]
                table[mask] = value, [triangles[u] for u in active]
            choices.append(table)
        for a, b in product(masks, repeat=2):
            if not (a or b):
                continue
            va, ta = choices[0][a]
            vb, tb = choices[1][b]
            residual, outside = reduce_label(va ^ vb)
            if residual == 0 and outside & occupied == 0:
                groups = complete_partition(n, ta + tb, outside)
                assert missed_partition(labels, groups)
                return groups
    return None


def audit():
    rng = random.Random(20261126)
    # Realize the rectangular proof with arbitrary outside corrections,
    # variable endpoint coefficient tables, and distinct extra vectors.
    for _ in range(256):
        m, extra = 12, 8
        n = 2 * m
        labels = [[rng.getrandbits(m + extra) for _ in range(n)] for _ in range(n)]
        for i in range(m):
            labels[2*i][2*i+1] = 1 << i
        for plane in (0, 1):
            left = [rng.randrange(8) for _ in range(3)]
            right = [rng.randrange(8) for _ in range(3)]
            for i, j in combinations(range(3), 2):
                k = 3 - i - j
                common = (rng.getrandbits(extra) << m) | (rng.randrange(8) << (3*k))
                for u in range(3):
                    a, b = 2*(3*i+u)+plane, 2*(3*j+u)+plane
                    outside = rng.getrandbits(m-9) << 9
                    labels[a][b] = common ^ (left[u] << (3*i)) ^ (right[u] << (3*j)) ^ outside
        groups = extract(labels)
        assert groups and missed_partition(labels, groups)
        assert sum(len(g) == 3 for g in groups) in (2, 4)
        assert sum(len(g)*(len(g)-1)//2 for g in groups) <= m+3
        # An invertible linear change of filter coordinates preserves the proof.
        for a, b in combinations(range(n), 2):
            value = labels[a][b]
            labels[a][b] = value ^ ((value << 3) & ((1 << (m + extra)) - 1))
        assert missed_partition(labels, extract(labels))

    labels = [[0]*18 for _ in range(18)]
    for i, j in combinations(range(18), 2):
        labels[i][j] = 1 << j
    assert extract(labels) is None  # Earliest repeated right endpoint certifies every positive.
    labels[2][3] = labels[0][1]    # A dependent canonical matching.
    assert missed_partition(labels, extract(labels))
    print('512 rectangular instances, an independent endpoint control, and a dependent matching passed')


if __name__ == '__main__':
    audit()
