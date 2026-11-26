"""Exact two-lane decoder for the 18-point anchor, parameterized by lost skip edges."""

from itertools import pairwise, permutations, product
from random import Random

from single_lane_sat import ANCHOR, BLUE_GAPS, RED_GAP, render_lists, site


def prepare_lanes(odd, even):
    """Lanes are ordered lists of one-based strip indices."""
    m = len(odd) + len(even)
    if m < 2 or len(odd) != (m + 1) // 2 or len(even) != m // 2:
        raise ValueError("expected both parity lanes at strip length at least two")
    seen = bytearray(m)
    skip = bytearray(m)
    chords = []
    for lane, parity in ((odd, 1), (even, 0)):
        last = -1
        for x in lane:
            if not 1 <= x <= m or x % 2 != parity or seen[x - 1]:
                raise ValueError(
                    "expected each strip point exactly once in its own parity lane"
                )
            seen[x - 1] = 1
            v = x - 1
            if last >= 0:
                lo, hi = min(last, v), max(last, v)
                if hi - lo == 2:
                    skip[hi] = 1
                else:
                    chords.append((lo, hi))
            last = v

    starts = [0] + [v for v in range(2, m) if not skip[v]]
    owner = [0] * m
    checks = [[] for _ in starts]
    pins = [[] for _ in starts]
    for depth, start in enumerate(starts):
        end = starts[depth + 1] if depth + 1 < len(starts) else m
        for v in range(start, end):
            owner[v] = depth
    for lo, hi in chords:
        checks[owner[hi]].append((lo, hi))
    # Opened anchor palette from its realizable coloring: 13,5,0 have color
    # 1; 14 has 0; 8 and 15 have 2. Every coloring has this signature up to
    # permuting the three colors. The last two symbols of the three gaps are
    # the red beginning and end, and the actual endpoints of each blue lane.
    for v, forbidden in (
        (0, 1),
        (m - 1, 0),
        (odd[0] - 1, 2),
        (odd[-1] - 1, 1),
        (even[0] - 1, 2),
        (even[-1] - 1, 1),
    ):
        pins[owner[v]].append((v, forbidden))
    return starts, owner, checks, pins


def solve_lanes(odd, even):
    """Return (is_3_colorable, number_of_missing_undirected_skip_edges)."""
    starts, owner, checks, pins = prepare_lanes(odd, even)
    b = len(starts) - 1
    palettes = [None] * len(starts)

    def color(v):
        depth = owner[v]
        return palettes[depth][(v - starts[depth]) % 3]

    # Each frame records a pair which fixes the period-three continuation of
    # its span. DFS never revisits an ancestor with a stale palette.
    stack = [(0, a, z) for a in range(3) for z in range(3) if a != z]
    while stack:
        depth, first, second = stack.pop()
        palettes[depth] = (first, second, 3 - first - second)
        if any(color(v) == c for v, c in pins[depth]):
            continue
        if any(color(lo) == color(hi) for lo, hi in checks[depth]):
            continue
        if depth == b:
            return True, b
        start = starts[depth + 1]
        prev, older = color(start - 1), color(start - 2)
        for choice in (older, 3 - older - prev):
            stack.append((depth + 1, choice, 3 - choice - prev))
    return False, b


def render_order(odd, even):
    m = len(odd) + len(even)
    return render_lists(m, map(site, odd), map(site, even))


def solve_order(order):
    """Recognize the canonical anchor in the actual array, validating both lanes."""
    m = len(order) - len(ANCHOR)
    if m < 2:
        raise ValueError("anchor requires at least two strip points")
    lanes = []
    pos = 0
    for u in ANCHOR:
        expected = u if u < RED_GAP[1] else u + m
        if order[pos] != expected:
            raise ValueError("incorrect anchor")
        pos += 1
        if u in (BLUE_GAPS[0][0], BLUE_GAPS[1][0]):
            length = (m + 1) // 2 if u == BLUE_GAPS[0][0] else m // 2
            lanes.append(
                tuple(value - RED_GAP[0] for value in order[pos : pos + length])
            )
            pos += length
    return solve_lanes(*lanes)


def direct_colorable(order):
    """Independent coloring search on all vertices, without using anchor colors."""
    adj = [set() for _ in order]
    for path in (range(len(order)), order):
        for a, b in pairwise(path):
            adj[a].add(b)
            adj[b].add(a)
    assigned = [-1] * len(order)
    assigned[0], assigned[1] = 0, 1

    def search(remaining):
        if not remaining:
            return True
        best = None
        options = [0, 1, 2, 3]
        for v in range(len(order)):
            if assigned[v] < 0:
                cs = {0, 1, 2} - {assigned[u] for u in adj[v]}
                if len(cs) < len(options):
                    best, options = v, cs
                    if not cs:
                        return False
        for c in options:
            assigned[best] = c
            if search(remaining - 1):
                return True
        assigned[best] = -1
        return False

    return search(len(order) - 2)


def audit():
    signs = [0, 0]
    for m in range(2, 10):
        for odd, even in product(
            permutations(range(1, m + 1, 2)), permutations(range(2, m + 1, 2))
        ):
            order = render_order(odd, even)
            value, b = solve_order(order)
            edges = {
                (min(u, v), max(u, v))
                for lane in (odd, even)
                for u, v in pairwise(lane)
            }
            assert b == sum((i, i + 2) not in edges for i in range(1, m - 1))
            assert value == direct_colorable(order)
            signs[value] += 1
    rng = Random(7813)
    for m in range(10, 22):
        for _ in range(12):
            odd, even = list(range(1, m + 1, 2)), list(range(2, m + 1, 2))
            rng.shuffle(odd)
            rng.shuffle(even)
            order = render_order(odd, even)
            assert solve_order(order)[0] == direct_colorable(order)
    for m in (1000, 1001, 10000):
        odd, even = list(range(1, m + 1, 2)), list(range(2, m + 1, 2))
        assert solve_order(render_order(odd, even)) == (False, 0)
        # Reversing either or both lanes also keeps every undirected skip edge.
        for y, z in ((odd[::-1], even), (odd, even[::-1]), (odd[::-1], even[::-1])):
            assert solve_order(render_order(y, z))[1] == 0
    print(
        f"Lengths 2–9: {signs[0]} negative and {signs[1]} positive lane pairs independently verified."
    )
    print(
        "144 additional shuffled pairs agree with full graph search; b=0 strips through 10,000 pass."
    )


if __name__ == "__main__":
    audit()
