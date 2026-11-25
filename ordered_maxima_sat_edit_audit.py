"""Finite checks for the ordered-maxima bounds and the native 3-SAT edits."""

from itertools import combinations, permutations, product
from math import comb


def chamber_bound(queries, labels):
    return sum(comb(queries, j) for j in range(min(queries, labels - 1) + 1))


def query_column(colors, orders):
    replies = []
    for order in orders:
        winner = next(a for a in reversed(order) if colors[a])
        actual = colors[winner]
        signed_sum = sum(colors[a] * (1 << rank) for rank, a in enumerate(order))
        assert signed_sum and (signed_sum > 0) == (actual == 1)
        replies.append(actual)
    return tuple(replies)


def audit_static():
    families = 0
    for u in range(1, 5):
        orders = list(permutations(range(u)))
        columns = {
            query_column(colors, orders)
            for colors in product((-1, 0, 1), repeat=u)
            if any(colors)
        }
        # Opposite query colors give the same partition of the order space.
        partitions = sorted({min(col, tuple(-x for x in col)) for col in columns})
        for m in range(1, min(len(partitions), u + 1) + 1):
            for family in combinations(partitions, m):
                assert len(set(zip(*family))) <= chamber_bound(m, u)
                families += 1
    for u in range(2, 8):
        profiles = {
            tuple(order.index(a) > order.index(0) for a in range(1, u))
            for order in permutations(range(u))
        }
        assert len(profiles) == 1 << (u - 1)
    return families


def search_transcript(positions, anchors, rounds):
    low = [0] * len(positions)
    high = [len(anchors) + 1] * len(positions)
    result = []
    for _ in range(rounds):
        batch = []
        for i, position in enumerate(positions):
            midpoint = (low[i] + high[i]) // 2
            above = position > anchors[midpoint - 1]
            batch.append(above)
            if above:
                low[i] = midpoint
            else:
                high[i] = midpoint
        result.extend(batch)
    assert all(h - l == 1 for l, h in zip(low, high))
    return tuple(result)


def audit_adaptive():
    checks = 0
    for u, rounds in ((3, 1), (5, 2), (6, 2), (7, 2), (8, 3)):
        anchor_count = (1 << rounds) - 1
        transcripts = set()
        for order in permutations(range(u)):
            ranks = {label: rank for rank, label in enumerate(order)}
            anchors = [ranks[a] for a in range(anchor_count)]
            if anchors != sorted(anchors):
                continue
            positions = [ranks[a] for a in range(anchor_count, u)]
            transcripts.add(search_transcript(positions, anchors, rounds))
            checks += 1
        assert len(transcripts) == 1 << (rounds * (u - anchor_count))
    return checks


def audit_bipartite_sample(k=3):
    edge_count = k * k
    all_edges = (1 << edge_count) - 1
    profiles = set()
    for order in permutations(range(2 * k)):
        ranks = {a: order.index(a) + 1 for a in order}
        models = [
            bits for bits in product((0, 1), repeat=2 * k)
            if all(bits[a] <= bits[b] for a, b in zip(order, order[1:]))
        ]
        profile = 0
        for i in range(k):
            for j in range(k):
                # The path contains the left spoke, connector and low right spoke.
                path_weights = (ranks[i], ranks[k + j], -1 - j)
                spoke_weights = (ranks[i], -1 - j)
                find = max(path_weights) <= max(spoke_weights)
                assert find == (ranks[i] > ranks[k + j])
                assert find == any(bits[i] and not bits[k + j] for bits in models)
                profile |= int(find) << (k * i + j)
        profiles.add(profile)

    disagreements = {x ^ y for x in profiles for y in profiles}
    worst = [
        max(d.bit_count() for d in disagreements if d & sample == 0)
        for sample in range(all_edges + 1)
    ]
    assert worst[0] == edge_count and worst[all_edges] == 0
    # Every single pair can be reversed by making its endpoints adjacent.
    assert all(1 << edge in disagreements for edge in range(edge_count))
    optimum = [
        min(s.bit_count() for s, ambiguity in enumerate(worst) if ambiguity <= cap)
        for cap in range(edge_count + 1)
    ]
    assert all(x >= y for x, y in zip(optimum, optimum[1:]))
    return len(profiles), optimum


def clause_value(clause, assignment):
    return any(sign == value for sign, value in zip(clause, assignment))


def audit_edits(m=9):
    assignments = tuple(product((0, 1), repeat=3))
    target = (1, 0, 1)
    forcing = [
        tuple(1 - value for value in assignment)
        for assignment in assignments
        if assignment != target
    ]

    def sat(clauses):
        return any(all(clause_value(c, a) for c in clauses) for a in assignments)

    checks = 0
    for x in product((0, 1), repeat=m):
        clauses = [(1, 1, bit) for bit in x]
        assert sat(forcing + clauses)
        for i in range(m):
            edited = clauses.copy()
            edited[i] = (0, 1, x[i])
            assert sat(forcing + edited) == bool(x[i])
            checks += 1
    return checks


if __name__ == "__main__":
    print("Static query families checked:", audit_static())
    print("Adaptive orders with ordered anchors checked:", audit_adaptive())
    print("Bipartite order profiles and optimal sample sizes by error:", audit_bipartite_sample())
    print("Single-bit 3-CNF edits checked:", audit_edits())
