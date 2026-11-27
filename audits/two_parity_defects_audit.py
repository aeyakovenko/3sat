"""Compare the batched two-defect 3-SAT test with direct witness enumeration."""

from collections import defaultdict
from itertools import combinations, product
from random import Random


def signed_triples(n):
    return [
        tuple(v * s for v, s in zip(variables, signs))
        for variables in combinations(range(1, n + 1), 3)
        for signs in product((1, -1), repeat=3)
    ]


def reduced_rows(rows, n):
    """Return reduced echelon rows, the row transformation, and the pivot columns."""
    rows = rows.copy()
    transform = [1 << i for i in range(len(rows))]
    pivots = []
    for v in range(n):
        target = len(pivots)
        source = next((r for r in range(target, len(rows)) if rows[r] >> v & 1), None)
        if source is None:
            continue
        rows[target], rows[source] = rows[source], rows[target]
        transform[target], transform[source] = transform[source], transform[target]
        for r in range(len(rows)):
            if r != target and rows[r] >> v & 1:
                rows[r] ^= rows[target]
                transform[r] ^= transform[target]
        pivots.append(v)
    return rows, transform, pivots


def intern(strings):
    """Assign identical identifiers precisely to equal row or column strings."""
    ids = {}
    return [ids.setdefault(s, len(ids)) for s in strings]


class BatchedTest:
    def __init__(self, clauses, n):
        self.m = len(clauses)
        rows = []
        rhs = 0
        for i, clause in enumerate(clauses):
            assert len({abs(lit) for lit in clause}) == len(clause) == 3
            rows.append(sum(1 << (abs(lit) - 1) for lit in clause))
            rhs |= ((1 + sum(lit < 0 for lit in clause)) % 2) << i

        reduced, transform, pivots = reduced_rows(rows, n)
        rank = len(pivots)
        for actual, recipe in zip(reduced, transform):
            expected = 0
            for i, row in enumerate(rows):
                if recipe >> i & 1:
                    expected ^= row
            assert actual == expected

        h = [(recipe & rhs).bit_count() % 2 for recipe in transform]
        # Each column represents flipping one *original clause*. The sentinel
        # column m is zero, for the first or second defect being absent.
        columns = [tuple(row >> i & 1 for row in transform) for i in range(self.m)]
        columns.append((0,) * self.m)
        normals = [col[rank:] for col in columns]
        translated = [tuple(u ^ v for u, v in zip(s, h[rank:])) for s in normals]
        ids = intern(normals + translated)
        self.normal, self.translated = ids[: self.m + 1], ids[self.m + 1 :]

        row_of = {v: r for r, v in enumerate(pivots)}
        free_mask = sum(1 << v for v in range(n) if v not in row_of)
        forms = [
            reduced[row_of[v]] & free_mask if v in row_of else 1 << v
            for v in range(n)
        ]
        self.zero, *self.form = intern([0, *forms])
        self.base = [h[row_of[v]] if v in row_of else 0 for v in range(n)]
        self.delta = [
            [col[row_of[v]] if v in row_of else 0 for col in columns]
            for v in range(n)
        ]

    def consistent(self, i, j):
        return self.normal[i] == self.translated[j]

    def can_pin(self, i, j, literals):
        constraints = {}
        for lit in literals:
            v = abs(lit) - 1
            value = int(lit > 0) ^ self.base[v] ^ self.delta[v][i] ^ self.delta[v][j]
            form = self.form[v]
            if (form == self.zero and value) or constraints.setdefault(form, value) != value:
                return False
        return True


def true_literal(word, lit):
    return ((word >> (abs(lit) - 1)) & 1) == (lit > 0)


def check(clauses, n):
    # Direct enumeration uses only ordinary clause evaluations and integer counts.
    parity_fibers = defaultdict(list)
    satisfying = set()
    for word in range(1 << n):
        counts = [sum(true_literal(word, lit) for lit in c) for c in clauses]
        defects = tuple(i for i, count in enumerate(counts) if count % 2 == 0)
        if len(defects) <= 2:
            parity_fibers[defects].append(word)
            if all(counts):
                satisfying.add(defects)

    table = BatchedTest(clauses, n)
    accepted = set()
    for size in range(3):
        for defects in combinations(range(len(clauses)), size):
            i, j = (defects + (table.m, table.m))[:2]
            feasible = table.consistent(i, j)
            assert feasible == table.consistent(j, i)
            assert feasible == bool(parity_fibers[defects]), (clauses, defects)
            if feasible:
                for pins in product(*(clauses[d] for d in defects)):
                    possible = table.can_pin(i, j, pins)
                    brute = any(
                        all(true_literal(word, lit) for lit in pins)
                        for word in parity_fibers[defects]
                    )
                    assert possible == brute, (clauses, defects, pins)
                    if possible:
                        accepted.add(defects)
    assert accepted == satisfying, (clauses, accepted, satisfying)


def suite(n):
    rows = signed_triples(n)
    yield []
    yield [rows[0]]  # Free variables and full row rank.
    yield [rows[0], rows[0], rows[1], rows[2]]  # Duplicate and conflicting rows.
    yield rows[:8]
    yield rows
    # A full-rank three-term system on four coordinates fixes all four.
    # For n=5, the fifth coordinate remains free unless it is also pinned.
    base = [tuple(t) for t in combinations(range(1, 5), 3)]
    yield base
    yield list(reversed(base)) + [base[1]]
    if n == 5:
        yield [(-4, 3, 5), *base]
    rng = Random(1021 + n)
    for count in range(1, 19):
        for _ in range(5):
            selected = []
            for _ in range(count):
                row = list(rng.choice(rows))
                rng.shuffle(row)
                selected.append(tuple(row))
            yield selected


def main():
    check([], 0)
    triples = signed_triples(3)
    for mask in range(1 << len(triples)):
        check([row for i, row in enumerate(triples) if mask >> i & 1], 3)
    print("All 256 three-variable clause subfamilies matched exhaustive witnesses.")
    for n in (4, 5):
        count = 0
        for clauses in suite(n):
            check(clauses, n)
            count += 1
        print(f"All {count} deterministic {n}-variable cases matched, including each pin choice.")


if __name__ == "__main__":
    main()
