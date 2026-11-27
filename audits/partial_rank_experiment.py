"""Check conditional binary-matrix rank laws by enumerating every completion."""

from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import product


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            bit = row.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = row
                break
            row ^= pivots[bit]
    return len(pivots)


@cache
def uniform_ranks(height, width):
    """Adding a uniform row preserves rank j with probability 2**(j-width)."""
    assert height >= 0 and width >= 0
    counts = Counter({0: 1})
    for _ in range(height):
        following = Counter()
        for j, count in counts.items():
            following[j] += count * (1 << j)
            if j < width:
                following[j + 1] += count * ((1 << width) - (1 << j))
        counts = following
    return {j: Fraction(v, 1 << (height * width)) for j, v in counts.items()}


def predicted(rows, width, completed_rows, left_cols, next_mask):
    """rows has zero in unknown entries. The next row has known mask next_mask."""
    left_mask = (1 << left_cols) - 1
    top = rows[:completed_rows]
    current = rows[completed_rows]
    u = rank(top)
    projected = [row & next_mask for row in top]
    projected_rank = rank(projected)
    keep = Fraction(0)
    if rank([*projected, current & next_mask]) == projected_rank:
        keep = Fraction(1 << (u - projected_rank), 1 << (width - next_mask.bit_count()))

    a = completed_rows + 1
    p = rank(row & left_mask for row in rows[:a])
    v = rank(row & left_mask for row in rows)
    result = Counter()
    for top_rank, probability in [(u, keep), (u + 1, 1 - keep)]:
        if probability:
            base = top_rank + v - p
            corner = uniform_ranks(len(rows) - a - v + p, width - left_cols - top_rank + p)
            for j, mass in corner.items():
                result[base + j] += probability * mass
    return result


def all_cases(height, width):
    full = (1 << width) - 1
    matrices = [(rows, rank(rows)) for rows in product(range(full + 1), repeat=height)]
    checked = 0
    for a in range(height):
        for b in range(width + 1):
            left = (1 << b) - 1
            for extra in range(1 << (width - b)):
                next_mask = left | (extra << b)
                masks = [full] * a + [next_mask] + [left] * (height - a - 1)
                histograms = defaultdict(Counter)
                for rows, matrix_rank in matrices:
                    known = tuple(row & mask for row, mask in zip(rows, masks))
                    histograms[known][matrix_rank] += 1
                for known, histogram in histograms.items():
                    total = sum(histogram.values())
                    exact = {j: Fraction(count, total) for j, count in histogram.items()}
                    assert predicted(known, width, a, b, next_mask) == exact
                    checked += 1
    return checked


if __name__ == "__main__":
    dimensions = [(h, w) for h in range(1, 4) for w in range(1, 4)]
    total = sum(all_cases(h, w) for h, w in dimensions)
    print(f"Checked {total:,} partial assignments across {len(dimensions)} matrix dimensions.")
