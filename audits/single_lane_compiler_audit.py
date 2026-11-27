"""Cross-check all small source orders on the emitted physical CNF using pycosat."""

import itertools

import pycosat

from one_point_strip_audit import anchor_audit, bad_edges
from simple_permutation_successor import coloring_dimacs, simple
from single_lane_sat import compile_lane, extend_coloring


def audit():
    anchor = anchor_audit()
    cnt = positive = negative = 0
    for n in range(7):
        for q in itertools.permutations(range(n)):
            result = compile_lane(q)
            if n <= 5:
                assert simple(result)
            physical = [
                tuple(map(int, row.split()[:-1]))
                for row in coloring_dimacs(result).splitlines()[1:]
            ]
            sat = pycosat.solve(physical) != "UNSAT"
            src = tuple(q)
            good = False
            for colors in itertools.product(range(3), repeat=n):
                if not bad_edges(src, colors):
                    assert not bad_edges(result, extend_coloring(src, colors, anchor))
                    good = True
                    cnt += 1
                    if n > 4:
                        break
            assert sat == good
            positive += sat
            negative += not sat
        print(n, positive, negative, cnt, flush=True)
    assert (positive, negative, cnt) == (828, 46, 1124)


if __name__ == "__main__":
    audit()
