"""Contract six positions at a time in unchanged parts of the anchored parity strip."""

from itertools import pairwise, permutations
from random import Random

from one_lane_phase_decoder import prepare_lanes, solve_lanes


def kernel(odd, even):
    """Return shortened lanes, retained one-based red indices, and the break count."""
    m = len(odd) + len(even)
    starts, _, _, _ = prepare_lanes(odd, even)
    marked = bytearray(m + 1)
    for point in (1, 2, m - 1, m):
        marked[point] = 1
    for right in starts[1:]:
        # prepare_lanes reports the zero-based right endpoint of the missing skip.
        marked[right - 1] = marked[right + 1] = 1

    kept = []
    start = 1
    while start <= m:
        if marked[start]:
            kept.append(start)
            start += 1
            continue
        end = start + 1
        while end <= m and not marked[end]:
            end += 1
        removed = max(0, (end - start - 4) // 6) * 6
        cut = min(start + 2, end)
        kept.extend(range(start, cut))
        kept.extend(range(cut + removed, end))
        start = end

    rank = [0] * (m + 1)
    for new, old in enumerate(kept, 1):
        rank[old] = new
    return (
        [rank[x] for x in odd if rank[x]],
        [rank[x] for x in even if rank[x]],
        kept,
        len(starts) - 1,
    )


def lane_edges(odd, even):
    return {tuple(sorted((x, y))) for lane in (odd, even) for x, y in pairwise(lane)}


def verify(odd, even):
    short_odd, short_even, kept, breaks = kernel(odd, even)
    rank = {x: i for i, x in enumerate(kept, 1)}
    old = lane_edges(odd, even)
    new = lane_edges(short_odd, short_even)
    m = len(odd) + len(even)
    k = len(kept)
    assert k <= 20 * breaks + 49 and k % 6 == m % 6
    assert all(i % 2 == x % 2 for i, x in enumerate(kept, 1))
    assert sum((i, i + 2) not in old for i in range(1, m - 1)) == breaks
    assert sum((i, i + 2) not in new for i in range(1, k - 1)) == breaks
    chords = {(rank[x], rank[y]) for x, y in old if y - x != 2}
    assert chords == {e for e in new if e[1] - e[0] != 2}
    for i, j in pairwise(kept):
        if j - i > 1:
            assert j - i >= 7 and (j - i) % 6 == 1
            assert all((x, x + 2) in old for x in range(i - 1, j))
    for lane, short in ((odd, short_odd), (even, short_even)):
        assert (rank[lane[0]], rank[lane[-1]]) == (short[0], short[-1])
    assert solve_lanes(odd, even) == solve_lanes(short_odd, short_even)
    return kept, short_odd, short_even


def colorings(odd, even):
    """Enumerate the strip alone, keeping every possible assignment at its six ports."""
    m = len(odd) + len(even)
    earlier = [[] for _ in range(m + 1)]
    for a, b in lane_edges(odd, even) | set(pairwise(range(1, m + 1))):
        earlier[b].append(a)
    rows = [(-1,)]
    for i in range(1, m + 1):
        rows = [
            row + (c,)
            for row in rows
            for c in range(3)
            if all(c != row[j] for j in earlier[i])
        ]
    return rows


def audit():
    rng = Random(121538)
    small = strict = long = bijections = 0
    for m in range(2, 10):
        for odd in permutations(range(1, m + 1, 2)):
            for even in permutations(range(2, m + 1, 2)):
                verify(odd, even)
                small += 1
    for m in (15, 21, 28, 52, 109, 254, 1001):
        for _ in range(150):
            lanes = [list(range(start, m + 1, 2)) for start in (1, 2)]
            for lane in lanes:
                if rng.randrange(2):
                    lane.reverse()
                for _ in range(rng.randrange(4)):
                    a, b = sorted(rng.sample(range(len(lane)), 2))
                    if rng.randrange(2):
                        lane[a], lane[b] = lane[b], lane[a]
                    else:
                        lane[a : b + 1] = reversed(lane[a : b + 1])
            kept, short_odd, short_even = verify(*lanes)
            long += 1
            if len(kept) < m:
                strict += 1
                if m <= 28:
                    old = colorings(*lanes)
                    short = colorings(short_odd, short_even)
                    restricted = {(-1,) + tuple(row[x] for x in kept) for row in old}
                    assert len(restricted) == len(old) and restricted == set(short)
                    bijections += 1
    print(
        f"{small} small lane pairs, {long} longer pairs, {strict} strict contractions."
    )
    print(
        f"All strip colorings restrict bijectively in {bijections} strict contractions."
    )


if __name__ == "__main__":
    audit()
