"""Exact decision game with partial answers to pairs of existential tests."""

from functools import lru_cache
from itertools import combinations_with_replacement


def solver(points, max_witnesses):
    full = (1 << points) - 1
    possibilities = [w for w in range(1, full + 1) if w.bit_count() <= max_witnesses]
    all_worlds = (1 << len(possibilities)) - 1
    misses = [sum(1 << i for i, w in enumerate(possibilities) if not w & a)
              for a in range(full + 1)]
    point_negatives = [misses[1 << i] for i in range(points)]
    pairs = set()
    for a, b in combinations_with_replacement(range(full + 1), 2):
        no_a, no_b = misses[a], misses[b]
        equal = all_worlds ^ (no_a ^ no_b)
        # Both NOs is dominated by either individual NO. A timely YES ends
        # the decision immediately. These three replies exhaust the hard cases.
        pairs.add(tuple(sorted(set((no_a, no_b, equal)))))

    @lru_cache(None)
    def wins(possible, q, u):
        if not possible:
            return True
        if u and any(wins(possible & negative, q, u - 1)
                     for negative in point_negatives):
            return True
        return bool(q and any(all(wins(possible & legal, q - 1, u) for legal in replies)
                              for replies in pairs))

    return lambda q, u: wins(all_worlds, q, u)


def main():
    checked = 0
    largest = 0
    for unique in (False, True):
        radix = 3 if unique else 2
        for m in range(1, 9 if unique else 6):
            can_win = solver(m, 1 if unique else m)
            for q in range(4):
                for u in range(m + 1):
                    actual = can_win(q, u)
                    assert actual == (m <= radix**q * u), (m, unique, q, u)
                    checked += 1
            largest = max(largest, m)
    sparse = 0
    for m in range(1, 6):
        for q in range(4):
            can_win = solver(m, q+1)
            for u in range(m+1):
                assert can_win(q, u) == (m <= 2**q * u), (m, q, u)
                sparse += 1
    for m in range(1, 13):
        equalities = [(1 << i, 1 << (i+1)) for i in range(m-1)]
        compatible = [w for w in range(1, 1 << m)
                      if all(bool(w & a) == bool(w & b) for a, b in equalities)]
        assert compatible == [(1 << m)-1]
    print(f'{sparse} exact budgets on the at-most-q+1 promise; 12 tight pruning chains')
    print(f'{checked} exact minimax query/verification budgets; '
          f'all witness sets through 5 points, singleton promises through {largest}')


if __name__ == '__main__':
    main()
