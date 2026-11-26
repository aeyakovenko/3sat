#!/usr/bin/env python3
"""Equal SAT clause scores on all affine assignment words, under every ordering.

The two files share anchors forcing x0=1,x1=0. With those anchors, F has
one failed private clause per remaining one, and G has one failed clause per
selected pair regardless of its bit. Outside the anchor pattern every private
clause passes. Score means the number of unsatisfied clauses. Both files have
the same number of clauses, so satisfied-clause scores agree as well.

All variables occur, in identical first-appearance order, and all clause
triples have three distinct variable names. Padding optional whitespace in
the paired private lines makes the byte lengths equal. This audit concerns
a restricted observation of a file, not the runtime of standard RAM solvers.
"""

from itertools import combinations, product


def serialize(v, rows, sizes=()):
    header = b"p cnf %d %d\n" % (v, len(rows))
    body = []
    for j, row in enumerate(rows):
        literals = b"%d %d %d" % row
        if sizes:
            literals = literals.ljust(sizes[j], b" ")
        body.append(literals + b" 0\n")
    return header + b"".join(body)


class Parsed:
    def __init__(self, raw):
        head, *lines = raw.splitlines()
        p, cnf, v, m = head.split()
        assert (p, cnf) == (b"p", b"cnf")
        self.v = int(v)
        assert len(lines) == int(m)
        self.rows = []
        order = {}
        unique = set()
        self.tests = []
        for line in lines:
            a, b, c, end = map(int, line.split())
            row = a, b, c
            names = tuple(abs(l) for l in row)
            assert end == 0 and all(1 <= x <= self.v for x in names) and len(set(names)) == 3
            key = tuple(sorted(row))
            assert key not in unique
            unique.add(key)
            order.update(dict.fromkeys(names))
            self.rows.append(row)
            active = sum(1 << (x - 1) for x in names)
            false_pattern = sum(1 << (abs(l) - 1) for l in row if l < 0)
            self.tests.append((active, false_pattern))
        self.order = tuple(order)
        assert set(order) == set(range(1, self.v + 1))

    def score(self, word):
        return sum(word & mask == pattern for mask, pattern in self.tests)


def pair(v):
    assert v >= 4 and v & (v - 1) == 0
    common = [(1, 2, i) for i in range(3, v + 1)]
    # Exclude each of 00,01,11 on the first two variables. A complementary
    # pair splits the binary clause on a third variable. The first positive
    # row of the 00 split is already in the introduction.
    for j, (a, b) in enumerate(((1, 2), (1, -2), (-1, -2))):
        i = 3 + j % (v - 2)
        for c in (i, -i):
            if (a, b, c) not in common:
                common.append((a, b, c))
    f = common + [(-1, 2, -i) for i in range(3, v + 1)]
    half = (v - 2) // 2
    g = common + [(-1, 2, lit) for i in range(3, 3 + half) for lit in (i, -i)]
    widths = [max(len(b"%d %d %d" % a), len(b"%d %d %d" % b)) for a, b in zip(f, g)]
    return serialize(v, f, widths), serialize(v, g, widths)


def affine_words(v):
    bits = max(1, (v - 1).bit_length())
    return {sum((bias ^ ((mask & j).bit_count() & 1)) << j for j in range(v))
            for mask in range(1 << bits) for bias in (0, 1)}


def permuted_affine_words(v):
    # This enumerates the entire orbit, not a sample of permutations. Every
    # subset with half the positions is an image of the first address bit.
    return {0, (1 << v) - 1} | {sum(1 << i for i in picked) for picked in combinations(range(v), v // 2)}


def force_word(v, word):
    """A proper dense formula with exactly the named assignment and unchanged order."""
    rows = [tuple(-i if pat & (1 << (i - 1)) else i for i in (1, 2, 3))
            for pat in range(8) if pat != (word & 7)]
    guard = [-i if word & (1 << (i - 1)) else i for i in (1, 2)]
    for i in range(4, v + 1):
        rows.append((*guard, i if word & (1 << (i - 1)) else -i))
    return serialize(v, rows)


def audit(v):
    f_raw, g_raw = pair(v)
    assert len(f_raw) == len(g_raw)
    f, g = Parsed(f_raw), Parsed(g_raw)
    assert f.order == g.order == tuple(range(1, v + 1))
    assert len(f.rows) == len(g.rows)
    fixed, orbit = affine_words(v), permuted_affine_words(v)
    assert fixed <= orbit
    models = [[], []]
    neighbors = set()
    for word in range(1 << v):
        sf, sg = f.score(word), g.score(word)
        # Check the signed score difference on the entire cube independently.
        target = word.bit_count() - v // 2 if (word & 3) == 1 else 0
        assert sf - sg == target
        if sf == 0:
            models[0].append(word)
        if sg == 0:
            models[1].append(word)
        if word in orbit:
            assert sf == sg
        if (word & 3) == 1 and word.bit_count() == v // 2:
            for j in range(2, v):
                neighbor = word ^ (1 << j)
                if neighbor not in neighbors:
                    assert abs(f.score(neighbor) - g.score(neighbor)) == 1
                    neighbors.add(neighbor)
    assert models == [[1], []] and neighbors
    print(f"v={v} bytes={len(f_raw)} clauses={len(f.rows)} fixed={len(fixed)} "
          f"all_orders={len(orbit)} distinct_separating_neighbors={len(neighbors)}")


def main():
    for v in (4, 8, 16):
        audit(v)
    # One balanced word at eight variables is nonlinear in standard order.
    # Moving its four ones to the odd ranks realizes the first-bit character.
    v = 8
    word = sum(1 << i for i in (0, 1, 2, 4))
    control = Parsed(force_word(v, word))
    assert control.order == tuple(range(1, v + 1))
    assert [x for x in range(1 << v) if control.score(x) == 0] == [word]
    assert word not in affine_words(v) and word in permuted_affine_words(v)
    ones = [i for i in range(v) if word & (1 << i)]
    zeros = [i for i in range(v) if not word & (1 << i)]
    new_order = [i for pair_of_ranks in zip(zeros, ones) for i in pair_of_ranks]
    assert [word >> i & 1 for i in new_order] == [j & 1 for j in range(v)]
    print("PASS: all 65,808 assignments; the balanced control needs an order change")


if __name__ == "__main__":
    main()
