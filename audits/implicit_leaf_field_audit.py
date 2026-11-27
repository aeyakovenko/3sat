"""Check the promised bad-leaf construction and its four-element-field tests."""

from itertools import combinations, product
from math import comb


def multiply(a, b):
    # Bit encoding of F2[X]/(X^2+X+1), with omega represented by 2.
    twice = (a << 1) ^ (7 if a & 2 else 0)
    return (a if b & 1 else 0) ^ (twice if b & 2 else 0)


def singleton_weight(point, assignment):
    value = 1
    for z, bit in zip(point, assignment):
        value = multiply(value, z if bit else 1 ^ z)
    return value


def check_points(v):
    cube = list(product(range(2), repeat=v))
    pairs = list(combinations(range(len(cube)), 2))
    row_masks = []
    upper_masks = []
    random_cancellations = [0] * len(pairs)
    upper = {(2,) * v}
    for i in range(v - 1):
        upper.add(tuple(3 if j == i else 2 for j in range(v)))
    for point in product(range(4), repeat=v):
        weights = [singleton_weight(point, a) for a in cube]
        cancellations = 0
        interior = all(z >= 2 for z in point)
        for i, (a, b) in enumerate(pairs):
            if weights[a] == weights[b]:
                cancellations |= 1 << i
                random_cancellations[i] += int(interior)
        if interior:
            assert all(weights)
        if point in upper:
            upper_masks.append(cancellations)
        row_masks.append(cancellations)

    all_pairs = (1 << len(pairs)) - 1
    undetected = all_pairs
    for mask in upper_masks:
        undetected &= mask
    assert len(upper_masks) == v and undetected == 0
    assert max(random_cancellations) <= 2 ** (v - 1)

    # An all-zero adaptive path is an ordinary list of points. Repeated
    # queries add no information, so full-size subsets suffice for the audit.
    for masks in combinations(row_masks, v - 1):
        unseen = all_pairs
        for mask in masks:
            unseen &= mask
        assert unseen
    return comb(4**v, v - 1)


def proper_expansion(clause, v):
    missing = [i for i in range(1, v + 1) if i not in map(abs, clause)][:3-len(clause)]
    return [tuple(clause) + tuple(s * i for i, s in zip(missing, signs))
            for signs in product((-1, 1), repeat=len(missing))]


def formula_for(models):
    first = models[0]
    second = models[-1]
    clauses = []
    pivot = None
    for i, (a, b) in enumerate(zip(first, second), 1):
        if a == b:
            clauses.append([i if a else -i])
        elif pivot is None:
            pivot = i
        else:
            # Positive pivot forces the value agreeing with the two rows.
            target = i if first[pivot - 1] == a else -i
            clauses.extend([[-pivot, target], [pivot, -target]])
    return [row for clause in clauses for row in proper_expansion(clause, len(first))]


def evaluate(clauses, a):
    return all(any(a[abs(lit)-1] == (lit > 0) for lit in clause) for clause in clauses)


def check_actual_leaves(v):
    cube = list(product(range(2), repeat=v))
    count = 0
    for size in (1, 2):
        for models in combinations(cube, size):
            clauses = formula_for(models)
            assert all(len(row) == len(set(map(abs, row))) == 3 for row in clauses)
            faults = []
            for a in cube:
                pointer = (a[0] ^ evaluate(clauses, a), a[1], a[2])
                axiom = {-(i+1) if bit else i+1 for i, bit in enumerate(pointer)}
                leaf = {-(i+1) if bit else i+1 for i, bit in enumerate(a)}
                if not axiom <= leaf:
                    faults.append(a)
            assert tuple(faults) == models
            count += 1
    return count


if __name__ == '__main__':
    for v in range(1, 5):
        print(f'v={v}: {check_points(v):,} insufficient F4 query sets; '
              'spanning upper tests and randomized pair bound passed')
    print(f'{sum(check_actual_leaves(v) for v in range(3, 7)):,} proper sources '
          'with their exact one- or two-element sets of invalid weakenings')
