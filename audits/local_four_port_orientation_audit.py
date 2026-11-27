"""Verify every terminal orientation profile of the local four-port compiler."""

from collections import Counter
from itertools import product

from threshold_port_coloring_audit import EDGES, TERMINALS


def fixture(copies):
    edges = []
    start, end = TERMINALS
    for i in range(copies):
        def name(v):
            if i and v == start:
                return (i - 1) * 12 + end
            return i * 12 + v

        edges.extend((name(u), name(v)) for u, v in EDGES)
    return edges, (start, (copies - 1) * 12 + end)


def balanced_heads(edges, terminals, profile):
    """Reduce the choice of an edge's head to matching with mandatory slots."""
    degree = Counter(v for edge in edges for v in edge)
    slots = {}
    optional = []
    outside = dict(zip(terminals, profile))
    for v, d in degree.items():
        incoming, outgoing = outside.get(v, (0, 0))
        total = d + incoming + outgoing
        lo = max(0, total // 2 - incoming)
        hi = min(d, (total + 1) // 2 - incoming)
        if lo > hi:
            return None
        slots[v] = [(v, i) for i in range(hi)]
        optional.extend(slots[v][lo:])
    choices = [slots[u] + slots[v] for u, v in edges]
    dummy_count = sum(map(len, slots.values())) - len(edges)
    if dummy_count < 0:
        return None
    choices.extend([optional] * dummy_count)
    owner = {}

    def augment(left, seen):
        for slot in choices[left]:
            if slot in seen:
                continue
            seen.add(slot)
            if slot not in owner or augment(owner[slot], seen):
                owner[slot] = left
                return True
        return False

    if not all(augment(left, set()) for left in range(len(choices))):
        return None
    heads = [None] * len(edges)
    for (v, _), left in owner.items():
        if left < len(edges):
            heads[left] = v
    assert all(v in edge for v, edge in zip(heads, edges))
    counts = Counter(heads)
    for v, d in degree.items():
        incoming, outgoing = outside.get(v, (0, 0))
        assert abs(2 * (counts[v] + incoming) - (d + incoming + outgoing)) <= 1
    return heads


def main():
    terminal_options = [(a, b) for a in range(3) for b in range(3 - a)]
    failures = []
    for copies in (1, 2):
        edges, terminals = fixture(copies)
        failed = {p for p in product(terminal_options, repeat=2) if balanced_heads(edges, terminals, p) is None}
        failures.append(failed)
        print(f"{copies} block(s), {len(edges)} internal edges: {36-len(failed)}/36 feasible profiles")
    assert failures == [{((2, 0), (2, 0)), ((0, 2), (0, 2))}, set()]


if __name__ == '__main__':
    main()
