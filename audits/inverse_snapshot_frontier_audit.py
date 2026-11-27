"""Check the two inverse-recovery cases and the sharp two-walk bound."""
from itertools import permutations


def directory(perm, span):
    seen = set()
    previous = {}
    for start in range(len(perm)):
        if start in seen:
            continue
        cycle = []
        x = start
        while x not in seen:
            seen.add(x)
            cycle.append(x)
            x = perm[x]
        if len(cycle) > span:
            marks = cycle[::span]
            previous.update((mark, marks[i-1]) for i, mark in enumerate(marks))
    return previous


def recover(perm, y, previous, span):
    probes = 0
    x = y
    while x not in previous:
        z = perm[x]
        probes += 1
        if z == y:
            assert probes <= span
            return x
        x = z
    x = previous[x]
    for _ in range(span):
        z = perm[x]
        probes += 1
        if z == y:
            assert probes <= 2 * span
            return x
        x = z
    raise AssertionError("the previous marked arc must contain the target")


if __name__ == "__main__":
    trials = 0
    for m in range(1, 8):
        for perm in permutations(range(m)):
            for span in range(1, m+1):
                prev = directory(perm, span)
                assert span * len(prev) <= 2 * m
                for y in range(m):
                    assert perm[recover(perm, y, prev, span)] == y
                    trials += 1
    print(f"{trials} inverse lookups passed")
