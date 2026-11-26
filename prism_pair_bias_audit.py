"""Exhaust the edge orientations of the pentagonal prism, using integer counts."""

from collections import Counter
from itertools import combinations


def main():
    side = 5
    vertices = range(2 * side)
    edges = [
        (layer * side + i, layer * side + (i + 1) % side)
        for layer in range(2)
        for i in range(side)
    ]
    edges.extend((i, side + i) for i in range(side))
    assert len(edges) == 15

    # Bit zero points away from the first endpoint, bit one from the second.
    # A clause contains the three literals saying its incident edges point out.
    zero_defects = 0
    witnesses = []
    defect_counts = Counter()
    for mask in range(1 << len(edges)):
        outdegree = [0] * len(vertices)
        for index, endpoints in enumerate(edges):
            tail = endpoints[(mask >> index) & 1]
            outdegree[tail] += 1
        defects = [v for v in vertices if outdegree[v] % 2 == 0]
        if not defects:
            zero_defects += 1
        if len(defects) == 1 and all(outdegree):
            witnesses.append(mask)
            defect_counts[defects[0]] += 1

    assert zero_defects == 0
    assert len(witnesses) == 480
    assert [defect_counts[v] for v in vertices] == [48] * len(vertices)

    # Use +1 for the bit-one orientation and -1 for the bit-zero orientation.
    signs = [
        [2 * ((mask >> index) & 1) - 1 for index in range(len(edges))]
        for mask in witnesses
    ]
    assert all(sum(column) == 0 for column in zip(*signs))
    pair_counts = Counter()
    for first, second in combinations(range(len(edges)), 2):
        cross_sum = sum(row[first] * row[second] for row in signs)
        common = set(edges[first]).intersection(edges[second])
        if common:
            (v,) = common
            first_literal = 1 if edges[first][1] == v else -1
            second_literal = 1 if edges[second][1] == v else -1
            assert first_literal * second_literal * cross_sum == -32
        else:
            assert cross_sum == 0
        pair_counts[bool(common)] += 1

    assert pair_counts == {True: 30, False: 75}
    print("32768 orientations, 0 with all parity rows satisfied")
    print("480 satisfying one-defect orientations, 48 at each of 10 vertices")
    print("15 zero singleton means")
    print("30 incident pairs with literal correlation -32/480 = -2/(3*10)")
    print("75 disjoint pairs with zero correlation")


if __name__ == "__main__":
    main()
