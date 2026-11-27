"""Check expander-edge routes using only consecutive visits of two tape heads."""

from collections import Counter, defaultdict
from itertools import combinations, pairwise, product


def monotone_matchings(n):
    """Generate every partial increasing matching between two ordered n-sets."""
    for size in range(n + 1):
        choices = list(combinations(range(n), size))
        for left, right in product(choices, repeat=2):
            yield tuple(zip(left, right))


def make_trace(n, matchings):
    """B's coordinates in forward order are L_0,…,L_(n−1),R_(n−1),…,R_0."""
    heads = []
    terminal = {}
    level = 0
    for phase, matching in enumerate(matchings):
        participants = {i for i, _ in matching} | {2*n-1-j for _, j in matching}
        order = range(2*n) if phase % 2 == 0 else reversed(range(2*n))
        for step, vertex in enumerate(order):
            if step < n:
                terminal[phase, vertex] = len(heads)
                heads.append((level, vertex))
                if vertex in participants:
                    level += 1
                heads.append((level, vertex))
            else:
                heads.append((level, vertex))
                if vertex in participants:
                    level -= 1
                terminal[phase, vertex] = len(heads)
                heads.append((level, vertex))
        assert level == 0
    return heads, terminal


def consecutive_visits(positions):
    visits = defaultdict(list)
    edges = set()
    for time, position in enumerate(positions):
        if visits[position]:
            edges.add((visits[position][-1], time))
        visits[position].append(time)
    return visits, edges


def reversals(positions):
    moves = [b-a for a, b in pairwise(positions) if a != b]
    assert all(abs(move) == 1 for move in moves)
    return sum(first != second for first, second in pairwise(moves))


def check(n, matchings):
    heads, terminal = make_trace(n, matchings)
    phases = len(matchings)
    assert len(heads) == 4*n*phases
    a, b = zip(*heads)
    nonempty = sum(bool(matching) for matching in matchings)
    assert min(a) == 0
    assert reversals(a) == max(0, 2*nonempty-1)
    assert reversals(b) == phases-1

    _, a_edges = consecutive_visits(a)
    folded = []
    sign = 1
    for phase, matching in enumerate(matchings):
        levels = a[4*n*phase:4*n*(phase+1)]
        folded.extend(n + sign*level for level in levels)
        if matching:
            sign = -sign
    # An initial forward walk brings a one-sided head from zero to the center.
    assert min(folded) >= 0 and reversals(list(range(n)) + folded) == nonempty
    _, folded_edges = consecutive_visits(folded)
    chains, b_edges = consecutive_visits(b)
    chain_index = {epoch: i for chain in chains.values()
                   for i, epoch in enumerate(chain)}
    assert len(chains) == 2*n
    assert set(chain_index) == set(range(len(heads)))
    for vertex, chain in chains.items():
        assert all(b[epoch] == vertex for epoch in chain)
        assert all(edge in b_edges for edge in pairwise(chain))

    paths_through = Counter()
    visit_edges = a_edges | b_edges
    for phase, matching in enumerate(matchings):
        for left, right_index in matching:
            right = 2*n-1-right_index
            left_end, right_end = terminal[phase, left], terminal[phase, right]
            crossing = tuple(sorted((left_end, right_end)))
            assert crossing in a_edges and crossing in folded_edges

            left_root, right_root = terminal[0, left], terminal[0, right]
            left_path = chains[left][chain_index[left_root]:chain_index[left_end]+1]
            right_path = chains[right][chain_index[right_root]:chain_index[right_end]+1]
            route = left_path + right_path[::-1]
            assert route[0] == left_root and route[-1] == right_root
            assert len(route) == len(set(route))
            assert all(tuple(sorted(edge)) in visit_edges for edge in pairwise(route))
            paths_through.update(route)
    congestion = max(paths_through.values(), default=0)
    assert congestion <= phases
    return congestion


def main():
    for n, phases in ((3, 3), (4, 2)):
        choices = list(monotone_matchings(n))
        count = 0
        worst = 0
        for matchings in product(choices, repeat=phases):
            worst = max(worst, check(n, matchings))
            count += 1
        print(f"n={n}, {phases} phases: {count} ordered families, "
              f"maximum vertex congestion {worst}.")


if __name__ == "__main__":
    main()
