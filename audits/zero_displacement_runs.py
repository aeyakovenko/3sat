"""Decide anchored parity strips by enumerating the nonzero displacements."""

from itertools import pairwise, permutations, product
from random import Random

from one_lane_phase_decoder import prepare_lanes, solve_lanes


def two_sat(variables, clauses):
    """Decide Boolean clauses on literals 2*i and 2*i+1 using strong components."""
    nodes = 2 * variables
    graph = [[] for _ in range(nodes)]
    reverse = [[] for _ in range(nodes)]
    for a, b in clauses:
        for u, v in ((a ^ 1, b), (b ^ 1, a)):
            graph[u].append(v)
            reverse[v].append(u)
    seen = bytearray(nodes)
    order = []
    for root in range(nodes):
        if seen[root]:
            continue
        seen[root] = 1
        stack = [(root, 0)]
        while stack:
            u, i = stack[-1]
            if i == len(graph[u]):
                order.append(u)
                stack.pop()
                continue
            v = graph[u][i]
            stack[-1] = (u, i + 1)
            if not seen[v]:
                seen[v] = 1
                stack.append((v, 0))
    component = [-1] * nodes
    for root in reversed(order):
        if component[root] != -1:
            continue
        component[root] = root
        todo = [root]
        while todo:
            for v in reverse[todo.pop()]:
                if component[v] == -1:
                    component[v] = root
                    todo.append(v)
    return all(component[2 * i] != component[2 * i + 1] for i in range(variables))


def solve(odd, even):
    """Return (colorable, enumerated sign count, missing skip count)."""
    m = len(odd) + len(even)
    spans, _, checks, pins = prepare_lanes(odd, even)
    # A missing skip ending at vertex v separates the two gaps meeting at v-1.
    starts = [0] + [v - 1 for v in spans[1:]]
    lengths = [b - a for a, b in pairwise(starts + [m - 1])]
    position = [None] * m
    for r, (start, length) in enumerate(zip(starts, lengths)):
        for i in range(length):
            position[start + i] = (r, i % 3)
    position[-1] = (len(starts) - 1, lengths[-1] % 3)
    chords = [(position[u], position[v]) for block in checks for u, v in block]
    pins = [(position[u], c) for block in pins for u, c in block]

    active = [r for r, length in enumerate(lengths[:-1]) if length % 3]
    fixed = [None] * len(starts)
    variable = [None] * len(starts)
    for r in active:
        fixed[r] = 1
    count = 0
    for r in range(len(starts)):
        if fixed[r] is None:
            variable[r] = count
            count += 1

    def feasible(bases):
        def options(point):
            r, offset = point
            base = bases[r]
            if not offset or fixed[r] is not None:
                return [(None, (base + offset * (fixed[r] or 0)) % 3)]
            # Conditional colors under each of the two signs in this run.
            literal = 2 * variable[r]
            return [(literal, (base + offset) % 3), (literal + 1, (base - offset) % 3)]

        clauses = []
        consistent = True

        def forbid(a, b):
            nonlocal consistent
            if a is None and b is None:
                consistent = False
                return
            if a is None:
                a = b
            if b is None:
                b = a
            clauses.append((a ^ 1, b ^ 1))

        for u, v in chords:
            for a, c in options(u):
                for b, d in options(v):
                    if c == d:
                        forbid(a, b)
        for u, forbidden_color in pins:
            for a, c in options(u):
                if c == forbidden_color:
                    forbid(a, None)
        return consistent and two_sat(count, clauses)

    for signs in product((1, -1), repeat=len(active)):
        for r, sign in zip(active, signs):
            fixed[r] = sign
        for initial_color in range(3):
            bases = [initial_color]
            for r, length in enumerate(lengths[:-1]):
                bases.append((bases[-1] + length * (fixed[r] or 0)) % 3)

            if feasible(bases):
                return True, len(active), len(starts) - 1
    return False, len(active), len(starts) - 1


def audit():
    from contracted_lane_audit import kernel
    from single_lane_sat import TIPS

    matches = 0
    for m in range(2, 11):
        for odd in permutations(range(1, m + 1, 2)):
            for even in permutations(range(2, m + 1, 2)):
                value, _, breaks = solve(odd, even)
                assert (value, breaks) == solve_lanes(odd, even)
                matches += 1
    print(f"{matches} exhaustive lane pairs agree with the phase decoder.")

    rng = Random(138729)
    triples = 0
    for s in (2, 3, 4, 5, 11, 67, 183):
        odd = list(range(1, 6 * s + 1, 2))
        for _ in range(100):
            order = list(range(s))
            rng.shuffle(order)
            backward = [rng.choice((False, True)) for _ in order]
            even = [
                6 * i + j
                for i in order
                for j in ((6, 4, 2) if backward[i] else (2, 4, 6))
            ]
            value, active, breaks = solve(odd, even)
            assert active == 0 and value == backward[-1]
            short_odd, short_even, _, _ = kernel(odd, even)
            assert solve(short_odd, short_even) == (value, active, breaks)
            triples += 1
    print(
        f"{triples} ordered-triple tests agree with the last-triple rule before and after contraction."
    )
    natural = set(pairwise(range(7)))
    tile_edges = {tuple(sorted(edge)) for edge in pairwise(TIPS)}
    lost_tips = sorted(i for i, j in natural - tile_edges)
    assert lost_tips == [0, 1, 2, 4]
    assert all(2 * (b - a) % 3 for a, b in pairwise(lost_tips))


if __name__ == "__main__":
    audit()
