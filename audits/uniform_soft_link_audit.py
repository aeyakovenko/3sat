"""Exhaust the ternary soft-link CNF and its conditional moments."""

from itertools import combinations, product


BITS = (0, 1)
ODD = ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1))
# DIMACS numbering: l=1, y=2, z=3, A=4, B=5, C=6, D=7, E=8, F=9.
TRIPLES = (
    ((1, 2, 3), ((0, 1, 0), (0, 0, 1))),
    ((1, 8, 9), ODD),
    ((2, 5, 7), ODD),
    ((3, 6, 7), ODD),
    ((4, 5, 9), ((0, 1, 0), (0, 0, 1), (1, 1, 1))),
    ((4, 6, 8), ((1, 0, 0), (0, 0, 1), (1, 1, 1))),
)


def make_clauses():
    return [
        tuple(-v if bit else v for v, bit in zip(triple, forbidden))
        for triple, patterns in TRIPLES
        for forbidden in patterns
    ]


def satisfies(bits, clauses):
    return all(
        any(bits[abs(literal) - 1] == (literal > 0) for literal in clause)
        for clause in clauses
    )


def sign(bit):
    return 1 - 2 * bit


def gadget_audit():
    clauses = make_clauses()
    assert len(set(clauses)) == 20
    assert all(len({abs(lit) for lit in clause}) == 3 for clause in clauses)
    fibers = {old: [] for old in product(BITS, repeat=3)}
    for bits in product(BITS, repeat=9):
        if satisfies(bits, clauses):
            fibers[bits[:3]].append(bits[3:])
    for (lit, y, z), rows in fibers.items():
        if lit == y ^ z:
            expected = {
                (b ^ e ^ lit, b, b ^ lit, b ^ y, e, e ^ lit)
                for b, e in product(BITS, repeat=2)
            }
        elif lit:
            expected = {(1, 0, 0, y, 1, 0), (0, 1, 1, 1 ^ y, 0, 1)}
        else:
            expected = set()
        assert set(rows) == expected
        assert all(sum(sign(row[i]) for row in rows) == 0 for i in range(6))

    good = [key for key in fibers if key[0] == key[1] ^ key[2]]
    # Each pair has the same moment function across all four good inputs.
    characters = {tuple(4 * sign(key[i]) for key in good) for i in range(3)}
    characters.add((0,) * 4)
    for i, j in combinations(range(6), 2):
        signature = tuple(
            sum(sign(row[i] ^ row[j]) for row in fibers[key]) for key in good
        )
        assert signature in characters
    print("20 proper ternary clauses, 512 assignments, 20 models")
    print("4 extensions per matched edge, 2 per omission, 0 per prohibited edge")
    print("6 conditionally unbiased auxiliaries and 15 good-fiber pair identities")
    return clauses


if __name__ == "__main__":
    import sys

    clauses = gadget_audit()
    if "--clauses" in sys.argv:
        print("p cnf 9 20")
        for clause in clauses:
            print(*clause, 0)
