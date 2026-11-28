"""Check terminal conflicts, the dormant product, and the packed shared table."""

from itertools import combinations, product
from random import Random


def holds(clauses, assignment):
    return all(any(bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0)
                   for lit in clause) for clause in clauses)


def reachable_columns(n, base):
    # Literal 2*i is positive, 2*i+1 is its complement.
    reach = [1 << i for i in range(2 * n)]
    for clause in base:
        if not clause:
            return None
        a, b = [2 * (abs(v) - 1) + (v < 0) for v in
                (clause if len(clause) == 2 else 2 * clause)]
        reach[a ^ 1] |= 1 << b
        reach[b ^ 1] |= 1 << a
    for k in range(2 * n):
        for i, row in enumerate(reach):
            if row & (1 << k):
                reach[i] |= reach[k]
    if any(reach[i] & (1 << (i ^ 1)) and reach[i ^ 1] & (1 << i)
           for i in range(0, 2 * n, 2)):
        return None
    return reach


def check_binary(n, base):
    assignments = [m for m in range(1 << n) if holds(base, m)]
    reach = reachable_columns(n, base)
    assert (reach is None) == (not assignments)
    if reach is None:
        return
    for partial in product((-1, 0, 1), repeat=n):
        selected = [2 * i + (value == 0) for i, value in enumerate(partial)
                    if value >= 0]
        consistent = all(not (reach[i] & (1 << (j ^ 1)))
                         for i in selected for j in selected)
        extends = any(all(value < 0 or (assignment >> i) & 1 == value
                          for i, value in enumerate(partial))
                      for assignment in assignments)
        assert consistent == extends


def pair_masks(p):
    return [(1 << i) | (1 << j) for i in range(p) for j in range(i, p)]


def matrix_of_set(vertex_set, pairs):
    return sum(1 << i for i, pair in enumerate(pairs)
               if vertex_set & pair == pair)


def packed_table(p, triples, width=8):
    pairs = pair_masks(p)
    q = len(pairs)
    entries = 1 << q
    blocks = [0] * ((entries + width - 1) // width)
    for s in range(1 << p):
        if all(s & t for t in triples):
            index = (entries - 1) ^ matrix_of_set(s, pairs)
            blocks[index // width] |= 1 << (index % width)
    for i in range(q):
        stride = 1 << i
        if stride < width:
            low = sum(1 << j for j in range(width) if not j & stride)
            for j, row in enumerate(blocks):
                blocks[j] |= (row >> stride) & low
        else:
            delta = stride // width
            for j in range(len(blocks)):
                if not j & delta:
                    blocks[j] |= blocks[j | delta]
    return [bool(blocks[i // width] & (1 << (i % width))) for i in range(entries)]


def check_tables():
    p = 4
    pairs = pair_masks(p)
    candidates = [sum(1 << i for i in triple) for triple in combinations(range(p), 3)]
    options = [matrix_of_set(s, pairs) for s in range(1 << p)]
    checked = 0
    for mask in range(1 << len(candidates)):
        triples = [t for j, t in enumerate(candidates) if mask & (1 << j)]
        result = packed_table(p, triples)
        compatible = [options[s] for s in range(1 << p) if all(s & t for t in triples)]
        for index, answer in enumerate(result):
            assert answer == any(index & forbidden == 0 for forbidden in compatible)
            checked += 1
    return checked


def check_reverse():
    for code in range(512):
        base = []
        for a in range(3):
            for b in range(3):
                if code & (1 << (3 * a + b)):
                    base.append((a + 1, 4 + b))
        # Impose at most one zero per triple in the active slice.
        for first in (1, 4):
            base += list(combinations(range(first, first + 3), 2))
        gates = [(-7, *clause) for clause in base]
        dormant = [(-1, -2, -3), (-4, -5, -6)]
        count_off = sum(holds(gates + dormant, z) for z in range(64))
        count_on = sum(holds(gates + dormant, z | 64) for z in range(64))
        assert count_off == 49 and count_on == 9 - code.bit_count()


def check_control_groups():
    rng = Random(1707)
    p, g = 5, 4
    pairs = pair_masks(p)
    for _ in range(45):
        triples = [tuple(-x for x in t) for t in combinations(range(1, p + 1), 3)
                   if rng.randrange(3) == 0]
        group_clauses = []
        for _ in range(17):
            negative = -(p + 1 + rng.randrange(g))
            others = rng.sample([i for i in range(1, p + g + 1) if i != -negative], 2)
            group_clauses.append((negative, *(v if rng.getrandbits(1) else -v
                                               for v in others)))
        groups = [[] for _ in range(g)]
        for cl in group_clauses:
            negative_controls = [-x for x in cl if x < -p]
            if len(negative_controls) == 1:
                groups[negative_controls[0] - p - 1].append(tuple(x for x in cl if abs(x) <= p))
        hits = [sum(1 << (-v - 1) for v in cl) for cl in triples]
        table = packed_table(p, hits)
        for j, base in enumerate(groups):
            reach = reachable_columns(p, base)
            if reach is None:
                predicted = False
            else:
                matrix = 0
                for i, pair in enumerate(pairs):
                    a = (pair & -pair).bit_length() - 1
                    b = pair.bit_length() - 1
                    if reach[2 * a + 1] & (1 << (2 * b)):
                        matrix |= 1 << i
                predicted = table[matrix]
            control = 1 << (p + j)
            assert predicted == any(holds(triples + group_clauses, z | control)
                                    for z in range(1 << p))


def main():
    n = 2
    choices = [(1,), (-1,), (2,), (-2,), (1, 2), (1, -2), (-1, 2), (-1, -2)]
    for code in range(1 << len(choices)):
        check_binary(n, [cl for i, cl in enumerate(choices) if code & (1 << i)])
    rng = Random(731)
    for _ in range(64):
        cl = []
        for _ in range(rng.randrange(14)):
            a, b = rng.sample(range(1, 5), 2)
            cl.append((a if rng.getrandbits(1) else -a, b if rng.getrandbits(1) else -b))
        check_binary(4, cl)
    check_reverse()
    checked = check_tables()
    check_control_groups()
    print(f'320 binary bases, 512 reverse CSPs, {checked} table entries, 180 control queries passed')


if __name__ == '__main__':
    main()
