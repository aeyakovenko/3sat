"""Check complete forbidden-triple seeds and degree-bounded polynomial calculus."""
from collections import Counter
from itertools import combinations
from random import Random


SIX_PATTERNS = (4, 2, 4, 1, 4, 0, 1, 1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7)


def supports(n, k):
    return [sum(1 << i for i in group) for group in combinations(range(n), k)]


def expand_pattern(mask, pattern):
    value = 0
    while mask:
        bit = mask & -mask
        if pattern & 1:
            value |= bit
        pattern >>= 1
        mask ^= bit
    return value


def models(n, clauses):
    return [a for a in range(1 << n) if all(a & s != b for s, b in clauses)]


def small_cover_check():
    masks = supports(5, 3)
    faces = [[sum(1 << a for a in range(32) if a & s == x & s)
              for x in range(32)] for s in masks]
    calls = 0

    def search(live, available):
        nonlocal calls
        calls += 1
        if not live:
            return True
        if live.bit_count() > 4 * available.bit_count():
            return False
        x = (live & -live).bit_length() - 1
        choices = available
        while choices:
            d = choices & -choices
            choices ^= d
            face = faces[d.bit_length() - 1][x]
            if search(live & ~face, available ^ d):
                return True
        return False

    # XOR-translate the first support's falsified pattern to all zeros.
    assert not search(((1 << 32)-1) ^ faces[0][0], (1 << 10)-2)
    return calls


def subsets(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            return
        sub = (sub - 1) & mask


def pc_refutes(n, clauses, degree):
    """Multilinear GF(2) rows. Only multiply a row of degree < degree."""
    mons = sorted((s for s in range(1 << n) if s.bit_count() <= degree),
                  key=lambda s: (s.bit_count(), s))
    coords = {s: i for i, s in enumerate(mons)}
    basis = {}
    queue = []

    def insert(p):
        while p:
            lead = p.bit_length() - 1
            if lead not in basis:
                basis[lead] = p
                if mons[lead].bit_count() < degree:
                    queue.append(p)
                return
            p ^= basis[lead]

    for mask, forbidden in clauses:
        if mask.bit_count() <= degree:
            # The blocker is x^forbidden times product of (1-x_i) for remaining i.
            insert(sum(1 << coords[forbidden | t] for t in subsets(mask ^ forbidden)))
    while queue and 0 not in basis:
        p = queue.pop()
        for i in range(n):
            q = 0
            bits = p
            while bits:
                b = bits & -bits
                bits ^= b
                s = mons[b.bit_length() - 1] | (1 << i)
                q ^= 1 << coords[s]
            insert(q)
    return 0 in basis


def main():
    calls = small_cover_check()
    six = [(s, expand_pattern(s, p)) for s, p in zip(supports(6, 3), SIX_PATTERNS)]
    assert not models(6, six)
    indispensable = {i for i in range(len(six)) if models(6, six[:i] + six[i+1:])}
    assert len(indispensable) == 11
    rng = Random(271126)
    audited = Counter()
    for k in [2, 3]:
        for n in range(k, 9):
            masks = supports(n, k)
            for _ in range(14):
                f = [(s, expand_pattern(s, rng.randrange(1 << k))) for s in masks]
                actual_unsat = not models(n, f)
                assert not pc_refutes(n, f, k)
                assert pc_refutes(n, f, k+1) == actual_unsat
                audited[k, actual_unsat] += 1
    lifts = []
    for n in range(6, 10):
        f = list(six)
        old_masks = {s for s, _ in f}
        f.extend((s, expand_pattern(s, rng.randrange(8)))
                 for s in supports(n, 3) if s not in old_masks)
        assert not models(n, f) and not pc_refutes(n, f, 3) and pc_refutes(n, f, 4)
        lifts.append((n, len(f)))
    print(f'Five-variable exhaustive search: {calls:,} nodes; six-variable seed: {len(six)} clauses, {len(indispensable)} individually necessary.')
    print(f'GF(2) bounded-degree closures checked against truth tables: {dict(sorted(audited.items()))}.')
    print(f'Complete extensions preserving degree four (variables, clauses): {lifts}.')


if __name__ == '__main__':
    main()
