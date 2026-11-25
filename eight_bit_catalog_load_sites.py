"""Pairwise indistinguishability for read-only comparison programs on 8-bit selectors."""

from itertools import combinations_with_replacement, product
from operator import eq, lt


def signed(x):
    return (x + 4) % 8 - 4


OPS = (eq, lt, lambda x, y: signed(x) < signed(y))


def satisfiable(words):
    a, b, c = words
    p, m = a + 8*(b % 2), b//2 + 4*c
    return not (p & m) and m != 15


def read(words, address):
    return words[address] if address < 3 else 0


def main():
    inputs = list(product(range(8), range(8), range(4)))
    positive = [row for row in inputs if satisfiable(row)]
    negative = [row for row in inputs if not satisfiable(row)]
    assert (4,4,2) in positive
    assert all(row in negative for row in [(6,4,2), (4,5,2), (4,4,3)])

    unary = set()
    for literal in range(8):
        for op in OPS:
            for first in (True, False):
                values = tuple(op(x, literal) if first else op(literal, x) for x in range(8))
                unary.add(tuple(v != values[0] for v in values))
    unary = sorted(unary)
    preserved = set()
    for a, b in product(positive, negative):
        relation = {(0,0), *zip(a,b)}
        while True:
            reads = {(read(a, x), read(b, y)) for x, y in relation}
            if reads <= relation:
                break
            relation.update(reads)
        keep = [i for i, test in enumerate(unary) if all(test[x] == test[y] for x, y in relation)]
        keep += [len(unary)+i for i, cmp in enumerate(OPS)
                 if all(cmp(x, u) == cmp(y, v) for x,y in relation for u,v in relation)]
        preserved.add(sum(1 << i for i in keep))
    assert len(positive) == 80 and len(negative) == 176
    assert len(unary) == 18 and len(preserved) == 427
    for predicates in combinations_with_replacement(range(len(unary)+len(OPS)), 4):
        required = sum(1 << i for i in set(predicates))
        assert any(c & required == required for c in preserved)
    print("80 SAT, 176 UNSAT; 427 closure signatures defeat all four-predicate selections.")


if __name__ == '__main__':
    main()
