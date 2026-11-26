"""Exhaust the empty/singleton selector game and check the upper strategy."""

from functools import cache
from itertools import product


@cache
def can_decide(negative, positive, queries, checks):
    """The two masks are surviving hidden points for each possible verdict."""
    if not negative or not positive:
        return True
    if checks:
        for i in range(positive.bit_length()):
            point = 1 << i
            if positive & point:
                # A positive membership settles the verdict immediately.
                if can_decide(negative, positive ^ point, queries, checks - 1):
                    return True
    if queries:
        live = negative | positive
        # Every nonconstant question to the singleton adviser is some split.
        part = (live - 1) & live
        while part:
            left = can_decide(negative & part, positive & part, queries - 1, checks)
            right = can_decide(negative & ~part, positive & ~part, queries - 1, checks)
            if left and right:
                return True
            part = (part - 1) & live
    return False


def selector(pool, queries, capacity, answers, marked):
    for _ in range(queries):
        if len(pool) < 2:
            break
        split = len(pool) // 2
        left = pool[:split]
        pool = left if answers(left) else pool[split:]
    assert len(pool) <= capacity
    return any(marked & (1 << i) for i in pool)


def main():
    games = truthful = dishonest = 0
    for size in range(1, 8):
        domain = tuple(range(size))
        full = (1 << size) - 1
        for queries in range(4):
            for checks in range(size + 1):
                feasible = checks * (1 << queries) >= size
                assert can_decide(full, full, queries, checks) == feasible
                games += 1
                if not feasible:
                    continue
                for marked in range(1, full + 1):
                    def intersects(pool):
                        return any(marked & (1 << i) for i in pool)
                    assert selector(domain, queries, checks, intersects, marked)
                    truthful += 1
                for bits in product((False, True), repeat=queries):
                    replies = iter(bits)
                    assert not selector(domain, queries, checks, lambda _: next(replies), 0)
                    dishonest += 1
    print(f"{games} minimax games, {truthful} nonempty truth-table runs, "
          f"{dishonest} empty-input adviser transcripts")


if __name__ == "__main__":
    main()
