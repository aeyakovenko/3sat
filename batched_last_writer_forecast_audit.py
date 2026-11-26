"""Finite checks for batched-last-writers-and-public-forward-probes.md."""

from itertools import combinations, permutations, product
from fractions import Fraction
from functools import cache
from math import perm


def restricted_family(m, targets, hidden):
    """Fix the forward table outside hidden, then place targets injectively."""
    outside = sorted(set(range(m)).difference(hidden))
    early_fixed = sorted(set(range(m // 2)).difference(targets))
    late = list(range(m // 2, m))
    count = len(outside) - len(early_fixed)
    assert 0 <= count <= len(late)
    fixed = dict(zip(outside, early_fixed + late[:count], strict=True))
    for positions in permutations(hidden, len(targets)):
        remaining = sorted(set(hidden).difference(positions))
        table = dict(fixed)
        table.update(zip(positions, targets, strict=True))
        table.update(zip(remaining, late[count:], strict=True))
        yield tuple(table[i] for i in range(m))


def scatter_reads(table):
    """Use zero-based labels and one-based writer time and reply."""
    heap = {}
    for time, address in enumerate(table, 1):
        heap[address] = (time, time)
    return tuple(heap[address] for address in range(len(table)))


def check_families():
    families = members = pairs = 0
    for m, k in ((4, 1), (4, 2), (6, 1), (8, 1), (8, 2), (8, 4)):
        h = m // (2 * k)
        for length in range(1, h + 1):
            for selected in combinations(range(h), length):
                targets = tuple(i for j in selected for i in range(j*k, (j+1)*k))
                for v in range(len(targets), m // 2 + 1):
                    for hidden in combinations(range(m), v):
                        families += 1
                        tables = list(restricted_family(m, targets, hidden))
                        assert len(tables) == len(set(tables)) == perm(v, len(targets))
                        members += len(tables)
                        public = [i for i in range(m) if i not in hidden]
                        raw = {tuple(table[i] for i in public) for table in tables}
                        assert len(raw) == 1
                        streams = []
                        for table in tables:
                            reads = scatter_reads(table)
                            assert all(time == value == table.index(i) + 1
                                       for i, (time, value) in enumerate(reads))
                            streams.append(tuple(tuple(reads[j*k:(j+1)*k]) for j in range(h)))
                        for a, b in combinations(streams, 2):
                            pairs += 1
                            assert all(a[j] == b[j] for j in range(h) if j not in selected)
                            first = next(j for j in range(h) if a[j] != b[j])
                            assert first in selected and a[:first] == b[:first]
    return families, members, pairs


def landmarks(table, gap):
    seen = set()
    previous = {}
    for start in range(len(table)):
        if start in seen:
            continue
        cycle = []
        pos = start
        while pos not in seen:
            seen.add(pos)
            cycle.append(pos)
            pos = table[pos]
        if len(cycle) > gap:
            marked = cycle[::gap]
            previous.update((point, marked[i - 1]) for i, point in enumerate(marked))
    return previous


def query(table, previous, target):
    pos = target
    probes = 0
    while pos not in previous:
        child = table[pos]
        probes += 1
        if child == target:
            return pos, probes
        pos = child
    pos = previous[pos]
    while True:
        child = table[pos]
        probes += 1
        if child == target:
            return pos, probes
        pos = child


def check_landmarks():
    tables = queries = 0
    for m in range(1, 8):
        for table in permutations(range(m)):
            tables += 1
            for gap in range(1, m + 1):
                previous = landmarks(table, gap)
                assert len(previous) * gap <= 2 * m
                for target in range(m):
                    i, probes = query(table, previous, target)
                    assert table[i] == target and probes <= 2 * gap
                    queries += 1
    return tables, queries


def parity_table(m, targets, even, odd, bits):
    positions = [iter(even), iter(odd)]
    inside = [next(positions[bit]) for bit in bits]
    reserved = {*even, *odd}
    outside = sorted(set(range(m)).difference(reserved))
    early = sorted(set(range(m // 2)).difference(targets))
    late = list(range(m // 2, m))
    used = len(outside) - len(early)
    assert 0 <= used <= len(late)
    table = dict(zip(outside, early + late[:used], strict=True))
    table.update(zip(inside, targets, strict=True))
    table.update(zip(sorted(reserved.difference(inside)), late[used:], strict=True))
    return tuple(table[i] for i in range(m))


def check_parity_families():
    families = pairs = 0
    for m, k in ((4, 1), (6, 1), (8, 1), (8, 2)):
        half_blocks = m // (2*k)
        for length in range(1, m // (4*k) + 1):
            s = length * k
            for blocks in combinations(range(half_blocks), length):
                targets = tuple(i for j in blocks for i in range(j*k, (j+1)*k))
                for even in combinations(range(0, m, 2), s):
                    for odd in combinations(range(1, m, 2), s):
                        families += 1
                        streams = []
                        outside = sorted(set(range(m)).difference(even, odd))
                        public = set()
                        for bits in product(range(2), repeat=s):
                            forward = parity_table(m, targets, even, odd, bits)
                            public.add(tuple(forward[i] for i in outside))
                            inverse = tuple(forward.index(i) for i in range(m // 2))
                            assert tuple(inverse[i] % 2 for i in targets) == bits
                            streams.append((bits, inverse))
                        assert len(public) == 1
                        for (bits, a), (other, b) in combinations(streams, 2):
                            first = next(i for i in targets if a[i] % 2 != b[i] % 2)
                            assert a[:first] == b[:first]
                            pairs += 1
    return families, pairs


def proper_unit(literal, a, b):
    return [(literal, sa*a, sb*b) for sa, sb in product((-1, 1), repeat=2)]


def check_pinned_sat():
    instances = 0
    for m in range(2, 5):
        a, b, c = m+1, m+2, m+3
        for table in permutations(range(m)):
            core = []
            for i, name in enumerate(table):
                literal = (name + 1) * (-1 if i % 2 else 1)
                core.extend(proper_unit(literal, a, b))
            for y in range(m):
                instances += 1
                cnf = core + proper_unit(y+1, a, c)
                assert len(set(cnf)) == len(cnf)
                assert all(len({abs(x) for x in clause}) == 3 for clause in cnf)
                count = 0
                for values in product((False, True), repeat=m+3):
                    if all(any(values[abs(x)-1] == (x > 0) for x in clause)
                           for clause in cnf):
                        count += 1
                assert count == (8 if table.index(y) % 2 == 0 else 0)
    return instances


@cache
def best_first_query(even, odd, probes):
    size = even + odd
    if not even or not odd:
        return Fraction(1)
    if not probes:
        return Fraction(max(even, odd), size)
    best_miss = max(best_first_query(even-1, odd, probes-1),
                    best_first_query(even, odd-1, probes-1))
    return (1 + (size-1)*best_miss) / size


def check_no_advice():
    cases = 0
    for m in range(2, 41, 2):
        for q in range(m + 1):
            exact = min(Fraction(1), Fraction(1, 2) + Fraction(q, m))
            assert best_first_query(m//2, m//2, q) == exact
            cases += 1
    return cases


if __name__ == "__main__":
    print("families, assignments, first-divergence pairs:", *check_families())
    print("landmark permutations, inverse queries:", *check_landmarks())
    print("parity families, full-prefix pairs:", *check_parity_families())
    print("proper 3CNF pins with exact model count:", check_pinned_sat())
    print("optimal no-advice single-pin success cases:", check_no_advice())
