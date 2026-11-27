"""Exact comparison-tree capacities after the five-step indirect-read prefix."""
from itertools import combinations, product


ALL_FILES = list(product(range(16), repeat=4))
TARGETS = [(p, q, 15-p, 15-q) for p in range(4, 12) for q in range(4, 12)]


def sat(f):
    p, q, m, n = f
    return (p & m) == 0 and (q & n) == 0 and (m, n) != (15, 15)


def registers(f):
    _, q, m, n = f
    j = q & n
    return q, m, n, j, f[j] if j < 4 else 0


def signed(word):
    return word if word < 8 else word-16


def three_rows(f):
    _, m, _, j, x = registers(f)
    if m > 9:
        return m == 11 and x == 4
    return x == (6 if signed(m) < signed(j) else 8)


def pair(f, a):
    _, m, _, j, x = registers(f)
    if m == 15-(a+1):
        return j == 0 and x == a+1
    return m == 15-a and x == a


def replay():
    terminals = [three_rows] + [lambda f, a=a: pair(f, a) for a in (4, 6, 8, 10)]
    for code in terminals:
        assert all(not code(f) or sat(f) for f in ALL_FILES)
    for f in TARGETS:
        p = f[0]
        assert three_rows(f) == (p in (4, 6, 8))
        assert [pair(f, a) for a in (4, 6, 8, 10)] == [a <= p <= a+1 for a in (4, 6, 8, 10)]
    counts = [sum(code(f) for f in ALL_FILES) for code in terminals]
    return counts


def pack(values):
    """Make an integer bitset without reallocating it after each inserted bit."""
    out = bytearray((len(values)+7)//8)
    for pos, v in enumerate(values):
        out[pos//8] |= v << (pos % 8)
    return int.from_bytes(out, 'little')


def condition_tables(files):
    """Every equality, unsigned and signed order of two register/literal values."""
    full = (1 << len(files)) - 1
    values = list(zip(*(registers(f) for f in files)))
    planes = [tuple(pack([(v >> k) & 1 for v in vals]) for k in range(4)) for vals in values]
    planes += [tuple(full if (i >> k) & 1 else 0 for k in range(4)) for i in range(16)]
    tables = []
    for i, j in combinations(range(len(planes)), 2):
        if i >= 5:
            continue
        u, v = planes[i], planes[j]
        eq, lt = full, 0
        for a, b in zip(u, v):
            diff = a ^ b
            eq &= ~diff
            lt = (b & diff) | (lt & ~diff)
        slt = lt ^ (u[3] ^ v[3])
        for cmp in (eq, lt, slt, full ^ (lt | eq), full ^ (slt | eq)):
            tables.append(cmp)
    return tables


def sharp_capacities():
    negatives = [f for f in ALL_FILES if not sat(f)]
    # A short preliminary counterexample vector accelerates the exact check.
    # Every surviving terminal is also tested against all 58,976 negative files.
    quick = [(0, 0, 15, 15)] + [f for f in negatives if all(4 <= x <= 11 for x in f)]
    panels = [TARGETS, quick, negatives]
    full_target, full_quick, full_neg = [(1 << len(s)) - 1 for s in panels]
    all_full = (full_target, full_quick, full_neg)
    guards = set()
    for outcome in zip(*(condition_tables(fs) for fs in panels)):
        other = tuple(universe ^ mask for universe, mask in zip(all_full, outcome))
        # A comparison and its reversed outcomes generate the same partition.
        guards.add(min(outcome, other))
    guards.discard((0, 0, 0))
    guards = sorted(guards)
    oriented = [s for g in guards for s in (g, tuple(u^a for u, a in zip(all_full, g))) if s[0]]
    odd_mask = sum(1 << i for i, f in enumerate(TARGETS) if f[0] % 2)

    def best_final(t, q, n):
        if not t or not n:
            return t.bit_count(), (t & odd_mask).bit_count()
        best, odd = 0, 0
        for gt, gq, gn in oriented:
            v = t & gt
            if v and not (q & gq) and not (n & gn):
                best = max(best, v.bit_count())
                odd = max(odd, (v & odd_mask).bit_count())
        return best, odd

    def best(depth, t, q, n):
        if depth == 1:
            return best_final(t, q, n)
        if not t or not n:
            return t.bit_count(), (t & odd_mask).bit_count()
        best_all, best_odd = 0, 0
        for gt, gq, gn in guards:
            st, sq, sn = t & gt, q & gq, n & gn
            left = best(depth-1, st, sq, sn)
            right = best(depth-1, t ^ st, q ^ sq, n ^ sn)
            best_all = max(best_all, left[0] + right[0])
            best_odd = max(best_odd, left[1] + right[1])
        return best_all, best_odd

    return len(negatives), len(quick), len(guards), best(3, *all_full)


if __name__ == '__main__':
    print("Globally accepted file counts", replay(), flush=True)
    n, q, g, answer = sharp_capacities()
    print("Negatives, prefilter size, distinct nonconstant raw guard partitions", n, q, g)
    print("Maximum total and odd-row targets", answer)
    assert n == 58976 and answer == (24, 8)
