"""Exhaust all affine codes of length <= 4 and all candidate majority-closed leaves."""

from functools import lru_cache
from itertools import combinations


def words(mask):
    return [i for i in range(mask.bit_length()) if (mask >> i) & 1]


def shift(mask, offset):
    return sum(1 << (x ^ offset) for x in words(mask))


def subspaces(n):
    seen = {1}
    pending = [1]
    while pending:
        space = pending.pop()
        for generator in range(1 << n):
            if (space >> generator) & 1:
                continue
            bigger = space | shift(space, generator)
            if bigger not in seen:
                seen.add(bigger)
                pending.append(bigger)
    return seen


def packing(space, n):
    vectors = words(space)[1:]

    @lru_cache(maxsize=None)
    def search(available):
        return max([0] + [1 + search(available ^ v) for v in vectors if (v & available) == v])

    return search((1 << n) - 1)


@lru_cache(maxsize=None)
def median_closed(mask):
    for a, b, c in combinations(words(mask), 3):
        if not (mask >> ((a & b) | (b & c) | (a & c))) & 1:
            return False
    return True


def largest_leaf(code):
    best = 0
    subset = code
    while subset:
        if subset.bit_count() > best and median_closed(subset):
            best = subset.bit_count()
        subset = (subset - 1) & code
    return best


def main():
    total = 0
    for n in range(5):
        for space in subspaces(n):
            expected = 1 << packing(space, n)
            for code in {shift(space, offset) for offset in range(1 << n)}:
                assert largest_leaf(code) == expected
                total += 1
    print(f"Verified the exact largest 2-CNF leaf size on all {total} nonempty affine codes through length four.")
    for n in range(2, 11):
        even = sum(1 << x for x in range(1 << n) if x.bit_count() % 2 == 0)
        assert packing(even, n) == n // 2
    print("Even-cycle packing verified through ten edges.")


if __name__ == '__main__':
    main()
