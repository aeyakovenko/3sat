#!/usr/bin/env python3
"""Check filtered GF(2) ranks for systematic edge subdivisions.

Run `python3 audits/subdivision_rule_rank.py` from the repository root.
Default coverage is every labeled graph on two through six vertices with
edge {0,1} present, and the individual cycles on seven through nine vertices.
Every choice of a distinguished edge is equivalent to this one by relabeling.
Rows use independent-set bits, the complements of the vertex-cover bits.
"""

import argparse
from itertools import combinations


def assignment_column(n, support):
    """Rows at which the square-free monomial with this support equals one."""
    return sum(1 << row for row in range(1 << n) if row & support == support)


class Catalog:
    def __init__(self, n):
        self.n = n
        self.rows = (1 << (1 << n)) - 1
        self.columns = [assignment_column(n, s) for s in range(1 << n)]
        self.by_degree = [
            [col for s, col in enumerate(self.columns) if s.bit_count() == d]
            for d in range(n + 1)
        ]
        self.edges = [
            (1 << a) | (1 << b)
            for a, b in combinations(range(n), 2)
            if (a, b) != (0, 1)
        ]

        # Derive the local checks directly for the old graph and for both
        # insertions. All edges outside this operation are handled separately.
        self.old_local = 0
        self.new_local = [0, 0]
        for row in range(1 << n):
            a = row & 1
            b = (row >> 1) & 1
            if not (a and b):
                self.old_local |= 1 << row
            for z in (0, 1):
                if not ((a and z) or (z and b)):
                    self.new_local[z] |= 1 << row

    def ranks(self, forced):
        """Insert original monomial evaluation columns by degree over GF(2)."""
        pivots = [0] * (1 << self.n)
        increments = []
        for columns in self.by_degree:
            gained = 0
            for column in columns:
                column &= forced
                while column:
                    site = column.bit_length() - 1
                    if pivots[site]:
                        column ^= pivots[site]
                    else:
                        pivots[site] = column
                        gained += 1
                        break
            increments.append(gained)
        return increments

    def check(self, edge_code, independent):
        """independent contains the independent sets after removing {0,1}."""
        old = independent & self.old_local
        ok = [self.rows ^ (old ^ (independent & new)) for new in self.new_local]
        assert ok[0] | ok[1] == self.rows
        forced = ok[0] ^ ok[1]
        # On forced rows, choosing z = 1 + a + b preserves the old verdict.
        affine_base = self.rows ^ self.columns[1] ^ self.columns[2]
        assert forced & (affine_base ^ ok[1]) == 0

        predicted = [0] * (self.n + 1)
        for s in range(0, 1 << self.n, 4):  # arbitrary interior set; endpoints absent
            a = (independent >> (s | 1)) & 1
            b = (independent >> (s | 2)) & 1
            degree = s.bit_count()
            predicted[degree] += a | b
            predicted[degree + 1] += 2 * (a & b)
        observed = self.ranks(forced)
        assert observed == predicted, (self.n, edge_code, observed, predicted)

        present = {edge for j, edge in enumerate(self.edges) if edge_code >> j & 1}
        common = sum(
            (1 | (1 << v)) in present and (2 | (1 << v)) in present
            for v in range(2, self.n)
        )
        affine_nullity = 1 + self.n - sum(observed[:2])
        assert affine_nullity == common, (self.n, edge_code, affine_nullity, common)
        return observed

    def all_graphs(self):
        # Intersect the previous graph's independent row set with the rows
        # avoiding its one additional edge. The bit mask has binom(n,2)-1
        # optional-edge positions; {0,1} stays fixed.
        count = 1 << len(self.edges)
        independent = [self.rows] * count
        for code in range(count):
            if code:
                added = code & -code
                edge = self.edges[added.bit_length() - 1]
                independent[code] = independent[code ^ added] & ~self.columns[edge]
            self.check(code, independent[code])
        return count

    def cycle(self):
        edges = {(1 << i) | (1 << ((i + 1) % self.n)) for i in range(self.n)}
        code = 0
        independent = self.rows
        for j, edge in enumerate(self.edges):
            if edge in edges:
                code |= 1 << j
                independent &= ~self.columns[edge]
        return self.check(code, independent)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-graph-order', type=int, choices=range(2, 7), default=6)
    args = parser.parse_args()
    total = 0
    for n in range(2, args.max_graph_order + 1):
        count = Catalog(n).all_graphs()
        print(f'n={n}: {count} graphs, all degrees agree')
        total += count
    print(f'{total} labeled graphs with the distinguished edge')
    for n in (7, 8, 9):
        print(f'cycle n={n}, rank increments {Catalog(n).cycle()}')


if __name__ == '__main__':
    main()
