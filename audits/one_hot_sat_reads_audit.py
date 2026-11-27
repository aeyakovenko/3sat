"""Check physical dictionary replies and resets on small batched unit formulas."""
from collections import Counter
from itertools import permutations, product


def run(formulas, echo_repetitions):
    zero, one = object(), object()
    memory = {}
    changes = Counter()
    writes = []
    replies = []

    def write(key, value):
        changes[key] += memory.get(key, 0) != value
        memory[key] = value
        writes.append(value)

    def read(key):
        replies.append(memory.get(key, 0))
        return replies[-1]

    write(one, 1)
    for i, (positive, _) in enumerate(formulas):
        for u in positive:
            write((i, u), 1)
    clean = True
    for i, (_, negative) in enumerate(formulas):
        for u in negative:
            if read((i, u) if clean else zero):
                clean = False
    read(one if clean else zero)
    for marker in (clean, not clean):
        for _ in range(echo_repetitions):
            read(one if marker else zero)
    for i, (positive, _) in enumerate(formulas):
        for u in positive:
            write((i, u), 0)
    write(one, 0)
    assert not any(memory.values()) and max(changes.values()) <= 2
    return clean, replies, writes


def check(formulas, r):
    clean, reads, writes = run(formulas, r)
    n = sum(len(b) for _, b in formulas)
    assert clean == all(set(a).isdisjoint(b) for a, b in formulas)
    expected_writes = 1 + sum(len(a) for a, _ in formulas)
    assert writes == [1]*expected_writes + [0]*expected_writes
    assert len(reads) == n+1+2*r and sum(reads[:n+1]) == 1 and sum(reads) == r+1
    target = [0]*n + [1] + [1]*r + [0]*r
    distance = sum(x != y for x, y in zip(target, reads))
    assert distance == (0 if clean else 2*r+2)
    return int(clean)


if __name__ == '__main__':
    names = range(5)
    lists = list(permutations(names, 2))
    cases = [(a,b) for a, b in product(lists, repeat=2)]
    tests = [[f] for f in cases]
    # Independent names across two batches; all 3-symbol one-entry cases.
    singles = [((a,), (b,)) for a, b in product(range(3), repeat=2)]
    tests.extend(product(singles, repeat=2))
    # Include repeated positives and repeated negatives outside the promise.
    tests.extend([[((0,0,1),(2,2,3))], [((1,1),(1,1))]])
    yes = sum(check(f, 7) for f in tests)
    print(f'{len(tests)} runs, {yes} satisfiable; exact replies, writes, distances and resets verified')
