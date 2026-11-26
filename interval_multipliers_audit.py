"""Check the full emitted path by frontier counting, with arbitrary vertex/sign pins."""

from collections import defaultdict
from itertools import pairwise, permutations
from math import lcm
from random import Random

from interval_witness_multipliers import (
    integer_blocks,
    maximal_prime_powers,
    proper_count_clauses,
    proper_count_dimacs,
    protect_counts,
)


def count_paths(order, literals):
    # Red scan keeps precisely the earlier tip colors needed by a later blue edge.
    # This calculation knows nothing about the block boundaries or transfer tables.
    n = len(order)
    colors = [[True] * 3 for _ in range(2 * n + 1)]
    signs = [[False, True, True] for _ in range(n)]
    for literal in literals:
        index = abs(literal) - 1
        if not 0 <= index < 7 * n + 6:
            raise ValueError("pin outside the variable range")
        if index < 6 * n + 3:
            vertex, color = divmod(index, 3)
            for c in range(3):
                if (c == color) != (literal > 0):
                    colors[vertex][c] = False
        elif index < 7 * n + 3:
            signs[index - 6 * n - 3][2 if literal > 0 else 1] = False
        elif literal > 0:
            return 0
    earlier = [[] for _ in range(n)]
    last_use = list(range(n))
    for u, v in pairwise(order):
        a, b = sorted((u, v))
        earlier[b].append(a)
        last_use[a] = max(last_use[a], b)
    frontier = []
    totals = {(0, ()): 1}
    for i in range(n):
        index = {v: j for j, v in enumerate(frontier)}
        new_frontier = [v for v in frontier if last_use[v] > i]
        surviving = [index[v] for v in new_frontier]
        old_neighbors = [index[v] for v in earlier[i]]
        keep = last_use[i] > i
        if keep:
            new_frontier.append(i)
        next_totals = defaultdict(int)
        for (base, live), mass in totals.items():
            if not colors[2 * i][base]:
                continue
            for step in (1, 2):
                tip = (base - step) % 3
                if not colors[2 * i + 1][tip]:
                    continue
                if not signs[i][step]:
                    continue
                if any(tip == live[j] for j in old_neighbors):
                    continue
                projected = tuple(live[j] for j in surviving)
                if keep:
                    projected += (tip,)
                next_totals[((base + step) % 3, projected)] += mass
        totals, frontier = next_totals, new_frontier
    return sum(mass for (base, _), mass in totals.items() if colors[-1][base])


def audit():
    from pycosat import itersolve, solve

    cases = 0
    lengths = {}
    rng = Random(1819)
    for n in range(1, 7):
        for perm in permutations(range(n)):
            clauses = proper_count_clauses(perm)
            encoded = proper_count_dimacs(perm)
            assert lengths.setdefault(n, len(encoded)) == len(encoded)
            header, *lines = encoded.splitlines()
            assert header.split() == [
                b"p",
                b"cnf",
                str(7 * n + 6).encode(),
                str(len(clauses)).encode(),
            ]
            parsed = [tuple(map(int, line.split())) for line in lines]
            assert [row[:-1] for row in parsed] == clauses and all(
                row[-1] == 0 for row in parsed
            )
            assert all(len(set(map(abs, clause))) == 3 for clause in clauses)
            assert sum(1 for _ in itersolve(clauses)) == count_paths(perm, ())
            pins = [rng.choice((-1, 1)) * v for v in rng.sample(range(1, 7 * n + 7), 3)]
            assert sum(
                1 for _ in itersolve(clauses + [(v,) for v in pins])
            ) == count_paths(perm, pins)
            cases += 1
    nonzero = 0
    tested = 0
    for source in ((0,), (1, 2, 0, 3), (1, 0, 3, 2), (0, 2, 1, 3, 5, 4)):
        for limit, budget in ((2, 1), (5, 2), (8, 2), (13, 1)):
            full = protect_counts(source, limit, budget)
            powers = tuple(maximal_prime_powers(limit))
            factor = 1
            for q in powers:
                # A single absolute sandwich has row sum 12^2 · 4^ell · q.
                factor *= (12**2 * 4 ** len(tuple(integer_blocks(q))) * q) ** (
                    budget + 1
                )
            baseline = count_paths(full, ())
            assert baseline == count_paths(source, ()) * factor
            cnf = proper_count_clauses(full)
            assert (solve(cnf) != "UNSAT") == (baseline > 0)
            for k in range(budget + 1):
                for _ in range(5):
                    pins = [
                        rng.choice((-1, 1)) * v
                        for v in rng.sample(range(1, 7 * len(full) + 7), k)
                    ]
                    count = count_paths(full, pins)
                    assert count % (lcm(*powers) ** (budget + 1 - k)) == 0
                    nonzero += count > 0
                    tested += 1
    print(
        f"All {cases} source permutations through six tips agree with exact proper-CNF counts."
    )
    print(
        f"Exact multipliers and {tested} raw flag restrictions verified, including {nonzero} nonzero counts."
    )


if __name__ == "__main__":
    audit()
