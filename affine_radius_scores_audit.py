"""Exact radius-one threshold for affine Max-3SAT profiles in dense ID order.

The score has Walsh characters supported on at most three variables.
Transforming over the affine centers groups equal (size parity, ID XOR).
Within a group, flipping a mask J weights a support S by (-1)^|S ∩ J|.
Thus the ranks below are over the rationals, even though the variable IDs
and the assignment masks use binary arithmetic.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product


def mask_of(indices):
    return sum(1 << i for i in indices)


def flip_masks(n, radius):
    return [mask_of(subset) for k in range(radius + 1)
            for subset in combinations(range(n), k)]


def exact_rank(rows):
    echelon = {}
    for row in rows:
        vector = list(map(Fraction, row))
        for pivot in sorted(echelon):
            if vector[pivot]:
                ratio = vector[pivot]
                vector = [x - ratio * y for x, y in zip(vector, echelon[pivot])]
        pivot = next((i for i, x in enumerate(vector) if x), None)
        if pivot is not None:
            scale = vector[pivot]
            echelon[pivot] = [x / scale for x in vector]
    return len(echelon)


def character_ranks(n, radius):
    groups = defaultdict(list)
    for size in range(4):
        for subset in combinations(range(n), size):
            label = 0
            for i in subset:
                label ^= i
            groups[size % 2, label].append(mask_of(subset))
    ranks = {}
    masks = flip_masks(n, radius)
    for key, supports in groups.items():
        rows = ([(-1) ** ((flip & support).bit_count() % 2) for support in supports]
                for flip in masks)
        ranks[key] = exact_rank(rows), len(supports)
    return ranks


def forbid(triple, values):
    return tuple(-(i + 1) if value else i + 1 for i, value in zip(triple, values))


def pin_clauses(assignment, n):
    # Establish dense first-occurrence order before either parity gadget.
    anchor = tuple((assignment >> i) & 1 for i in range(3))
    clauses = [forbid((0, 1, 2), values) for values in product(range(2), repeat=3)
               if values != anchor]
    for i in range(3, n):
        bad_bit = 1 ^ ((assignment >> i) & 1)
        clauses.append(forbid((0, 1, i), (anchor[0], anchor[1], bad_bit)))
    return clauses


def even_checks(triples):
    return [forbid(triple, values) for triple in triples
            for values in product(range(2), repeat=3) if sum(values) % 2 == 1]


def dimacs(clauses, n):
    header = f"p cnf {n} {len(clauses)}\n"
    return (header + "".join(" ".join(map(str, clause)) + " 0\n"
                             for clause in clauses)).encode("ascii")


def read_dense(data):
    rows = data.decode("ascii").splitlines()
    header = rows[0].split()
    assert header[:2] == ["p", "cnf"]
    n, count = map(int, header[2:])
    assert count == len(rows) - 1
    ids = {}
    clauses = []
    namesets = set()
    for row in rows[1:]:
        i, j, k, stop = map(int, row.split())
        literals = (i, j, k)
        names = tuple(map(abs, literals))
        assert stop == 0 and all(1 <= name <= n for name in names)
        assert len(set(names)) == 3
        assert frozenset(literals) not in namesets
        namesets.add(frozenset(literals))
        for name in names:
            ids.setdefault(name, len(ids))
        variables = mask_of(ids[name] for name in names)
        forbidden_bits = mask_of(ids[abs(lit)] for lit in literals if lit < 0)
        clauses.append((variables, forbidden_bits))
    assert list(ids) == list(range(1, n + 1))
    return clauses


def score(clauses, assignment):
    return sum((assignment & variables) == bad for variables, bad in clauses)


def affine_centers(n):
    return {mask_of(i for i in range(n) if ((i & u).bit_count() + offset) % 2)
            for u in range(1 << (n - 1).bit_length()) for offset in (0, 1)}


def check_pair():
    n = 10
    left = [(0, 2, 8), (1, 3, 8), (4, 7, 9), (5, 6, 9)]
    right = [(0, 3, 9), (1, 2, 9), (4, 6, 8), (5, 7, 8)]
    assert all(i ^ j ^ k == 10 for i, j, k in left + right)
    assert Counter(i for triple in left for i in triple) == Counter(
        i for triple in right for i in triple)
    planted = mask_of([0, 2])
    pins = pin_clauses(planted, n)
    files = [dimacs(pins + even_checks(triples), n) for triples in (left, right)]
    assert len(files[0]) == len(files[1])
    a, b = map(read_dense, files)
    assert len(a) == len(b) == 30
    assert [x for x in range(1 << n) if score(a, x) == 0] == [planted]
    assert all(score(b, x) > 0 for x in range(1 << n))
    centers = affine_centers(n)
    one_ball = {center ^ flip for center in centers for flip in flip_masks(n, 1)}
    assert all(score(a, x) == score(b, x) for x in one_ball)
    # The zero affine center and flips 0,2 give the planted model itself.
    assert 0 in centers and score(a, planted) == 0 and score(b, planted) == 2
    return len(files[0]), len(centers), len(one_ball)


def main():
    print("names  degree<=3 terms  radius-1 rank  radius-2 rank")
    for n in range(4, 11):
        one = character_ranks(n, 1)
        two = character_ranks(n, 2)
        terms = sum(size for _, size in one.values())
        rank_one = sum(rank for rank, _ in one.values())
        rank_two = sum(rank for rank, _ in two.values())
        assert (rank_one == terms) == (n <= 9)
        assert rank_two == terms
        if n == 10:
            deficient = {key: counts for key, counts in one.items() if counts[0] < counts[1]}
            assert deficient == {(1, label): (7, 8) for label in range(10, 16)}
        print(f"{n:5}  {terms:15}  {rank_one:13}  {rank_two:13}")
    length, centers, neighbors = check_pair()
    print(f"opposite verdicts on two {length}-byte proper files; "
          f"identical scores at {centers} centers and all {neighbors} "
          "distinct assignments within one flip")


if __name__ == "__main__":
    main()
