"""Check the row census, signed 3-clause encodings and inclusion-exclusion on small instances."""
from collections import Counter
from itertools import combinations, product
from random import Random

from minimal_eight_bit_executed_suite import DELETIONS


def relation(mask, bits):
    positive = mask & 15
    negative = mask >> 4
    return bool(bits and (bits & positive) == positive and (bits & negative) == 0)


def residual(mask):
    positive = mask & 15
    negative = mask >> 4
    if positive & negative or negative == 15:
        return "empty", 0, 0
    if positive:
        return "box", positive, negative
    if negative.bit_count() == 3:
        return "box", 15 ^ negative, negative
    return str(4 - negative.bit_count()), 0, negative


def residual_holds(mask, bits):
    kind, positive, negative = residual(mask)
    if kind == "empty" or bits & negative or (bits & positive) != positive:
        return False
    return kind == "box" or bool(bits & (15 ^ negative))


def value(assignment, lit):
    return bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0)


def holds(assignment, mask, ports):
    bits = sum(int(value(assignment, lit)) << i for i, lit in enumerate(ports))
    return relation(mask, bits)


def direct(clause):
    # 1..4 are source variables, 5 is the public false port.
    return clause[0], clause[1], 5, clause[2]


def paired(clause):
    # 2i-1 and 2i represent i and its negation. 9 is the public false port.
    names = [2*abs(lit) - (lit > 0) for lit in clause]
    return names[0], names[1], 9, names[2]


def check_census():
    for mask in range(256):
        for bits in range(16):
            assert relation(mask, bits) == residual_holds(mask, bits)
    counts = Counter(residual(mask)[0] for mask in range(256))
    assert counts == {"empty": 176, "box": 69, "2": 6, "3": 4, "4": 1}
    cert = list(map(int, DELETIONS))
    assert Counter(residual(mask)[0] for mask in cert) == {"empty": 10, "box": 8, "3": 1}
    assert [mask for mask in cert if residual(mask)[0] == "3"] == [64]


def check_encoding():
    clauses = [tuple(s*i for s, i in zip(signs, ids))
               for ids in combinations(range(1, 5), 3)
               for signs in product((-1, 1), repeat=3)]
    guards = []
    for i in range(1, 5):
        u, v = 2*i - 1, 2*i
        guards.extend([(u, v, 9, 10), (-u, -v, 9, 10)])
    guards.append((11, 12, 10, 13))
    for ports in guards + [paired(clause) for clause in clauses]:
        assert sum(lit < 0 for lit in ports) <= 2
        assert len(set(map(abs, ports))) == 4
    # Get all representative configurations extendible to the 5 auxiliary bits.
    extendible = {bits & 255 for bits in range(1 << 13)
                  if all(holds(bits, 64, ports) for ports in guards)}
    assert len(extendible) == 16
    checked = 0
    for a in range(16):
        reps = sum((1 if a >> i & 1 else 2) << (2*i) for i in range(4))
        assert reps in extendible
        for c1, c2 in product(clauses, repeat=2):
            expected = all(any(value(a, lit) for lit in c) for c in (c1, c2))
            assert expected == all(holds(a, 64, direct(c)) for c in (c1, c2))
            assert expected == all(holds(reps, 64, paired(c)) for c in (c1, c2))
            checked += 1
    return checked


def gray_count(clauses, variables):
    counts = [[0, 0] for _ in range(variables)]
    included = [False] * len(clauses)
    fixed = conflicts = parity = result = 0

    def toggle(index):
        nonlocal fixed, conflicts, parity
        delta = -1 if included[index] else 1
        included[index] = not included[index]
        parity ^= 1
        for lit in clauses[index]:
            row = counts[abs(lit)-1]
            fixed -= int(any(row))
            conflicts -= int(all(row))
            row[int(lit < 0)] += delta
            fixed += int(any(row))
            conflicts += int(all(row))

    def gray(level):
        nonlocal result
        if level == 0:
            if conflicts == 0:
                weight = 1 << (variables-fixed)
                result += -weight if parity else weight
            return
        gray(level-1)
        toggle(level-1)
        gray(level-1)

    gray(len(clauses))
    return result


def check_counts():
    rng = Random(251126)
    for _ in range(300):
        n = rng.randrange(1, 8)
        clauses = [tuple(rng.choice((1, -1)) * rng.randrange(1, n+1)
                         for _ in range(rng.randrange(4)))
                   for _ in range(rng.randrange(9))]
        expected = sum(all(any(value(a, lit) for lit in clause) for clause in clauses)
                       for a in range(1 << n))
        assert gray_count(clauses, n) == expected


if __name__ == "__main__":
    check_census()
    pairs = check_encoding()
    check_counts()
    print(f"4096 row assignments and {pairs} two-clause instances with fixed assignments checked.")
    print("Both row-64 encodings passed, including all auxiliary assignments for the guards.")
    print("300 signed clause networks counted by both Gray traversal and complete assignment search.")
