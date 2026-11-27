"""Finite checks for adaptive compatible leaves and the weighted NOR filter."""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import comb, isqrt, prod
from random import Random


@dataclass
class Node:
    kind: str
    index: int
    forecast: int
    children: tuple


def make_tree(rng, bits, words, bit_budget, word_budget):
    if bit_budget + word_budget == 0 or rng.randrange(18) == 0:
        return rng.choice((-1, 0, 1))
    use_bit = bit_budget > 0 and (word_budget == 0 or rng.randrange(3) == 0)
    if use_bit:
        i = rng.choice(bits)
        return Node("bit", i, 0, tuple(
            make_tree(rng, [b for b in bits if b != i], words, bit_budget-1, word_budget)
            for _ in range(2)))
    a = rng.choice(words)
    return Node("work", a, rng.randrange(3), tuple(
        make_tree(rng, bits, [w for w in words if w != a], bit_budget, word_budget-1)
        for _ in range(3)))


def compatible_leaves(tree, bits, words, cap, tokens=()):
    if isinstance(tree, int):
        if tree:
            yield tokens, tree
        return
    if tree.kind == "bit":
        yield from compatible_leaves(tree.children[bits[tree.index]], bits, words, cap, tokens)
        return
    actual = words[tree.index]
    forecast = tree.forecast
    if actual == forecast:
        yield from compatible_leaves(tree.children[actual], bits, words, cap, tokens)
        return
    yield from compatible_leaves(tree.children[forecast], bits, words, cap, tokens + (0,))
    if cap:
        yield from compatible_leaves(tree.children[actual], bits, words, cap-1, tokens + (1,))


def true_output(tree, bits, words, cap):
    while isinstance(tree, Node):
        if tree.kind == "bit":
            val = bits[tree.index]
        else:
            val = words[tree.index]
            cap -= val != tree.forecast
            if cap < 0:
                return 0
        tree = tree.children[val]
    return tree


def signed_leaf_terms(tree, cap, bits=(), exact=(), defaults=()):
    if isinstance(tree, int):
        if tree:
            yield tree, bits, exact, defaults
        return
    for val, child in enumerate(tree.children):
        test = (tree.index, val)
        if tree.kind == "bit":
            yield from signed_leaf_terms(child, cap, bits+(test,), exact, defaults)
        elif val == tree.forecast:
            yield from signed_leaf_terms(child, cap, bits, exact, defaults+(test,))
        elif cap:
            yield from signed_leaf_terms(child, cap-1, bits, exact+(test,), defaults)


def check_trees():
    rng = Random(487)
    cases = 0
    for _ in range(10):
        tree = make_tree(rng, list(range(3)), list(range(4)), 2, 3)
        for cap in (0, 1, 2):
            terms = list(signed_leaf_terms(tree, cap))
            for x in product(range(2), repeat=3):
                for z in product(range(3), repeat=4):
                    leaves = list(compatible_leaves(tree, x, z, cap))
                    codes = [word for word, _ in leaves]
                    assert len(set(codes)) == len(codes)
                    assert all(w[:j] not in codes for w in codes for j in range(len(w)))
                    assert len(codes) <= sum(comb(3, j) for j in range(cap+1))
                    tally = Counter((word.count(0), word.count(1)) for word in codes)
                    assert all(count <= comb(e+j, j) for (e, j), count in tally.items())
                    path_scores = Counter((w.count(0), sign) for w, sign in leaves)
                    scores = Counter()
                    for sign, bit_tests, positives, defaults in terms:
                        if (all(x[a] == v for a, v in bit_tests)
                                and all(z[a] == v for a, v in positives)):
                            scores[sum(z[a] != v for a, v in defaults), sign] += 1
                    assert scores == path_scores
                    assert scores[0, 1] - scores[0, -1] == true_output(tree, x, z, cap)
                    cases += 1
    return cases


def chebyshev(n, x):
    old, val = Fraction(1), x
    if not n:
        return old
    for _ in range(1, n):
        old, val = val, 2*x*val-old
    return val


def make_filter(q, k, precision):
    # eta = 2^(-precision), h = k + log2(2/eta) + 1.
    h = k + precision + 2
    root_count = min(h, q) if 2*h < q else q
    factors = []
    if 2*h < q:
        b = h
        while b < q:
            n = isqrt((64*h*h*q)//b)
            n += n*n*b < 64*h*h*q
            scale = chebyshev(n, Fraction(q+b, q-b))
            factors.append((b, n, scale))
            b *= 2

    def value(e):
        if 1 <= e <= root_count:
            return Fraction(0)
        result = prod((Fraction(i-e, i) for i in range(1, root_count+1)), start=Fraction(1))
        for b, n, scale in factors:
            result *= chebyshev(n, Fraction(q+b-2*e, q-b)) / scale
        return result
    return value


def check_filters():
    cases = [(0, 0, 1), (7, 2, 3), (16, 0, 1), (32, 1, 3),
             (37, 3, 2), (64, 2, 1), (72, 4, 2)]
    for q, k, precision in cases:
        val = make_filter(q, k, precision)
        assert val(0) == 1
        error = sum(comb(e+k+1, k)*abs(val(e)) for e in range(1, q+1))
        assert error <= Fraction(1, 2**precision)
    return len(cases)


if __name__ == "__main__":
    print(f"{check_trees()} adaptive tree/input/cap cases and {check_filters()} exact rational filters passed")
