"""Exact finite checks of adaptive exposure and correlated clean dips."""

from fractions import Fraction
from itertools import product
from math import lcm, prod
from random import Random


def side_tree(rng, alphabet, available, depth):
    if depth == 0:
        return rng.sample(range(alphabet), alphabet)
    address = rng.choice(available)
    remaining = [other for other in available if other != address]
    return address, [side_tree(rng, alphabet, remaining, depth - 1)
                     for _ in range(alphabet)]


def local_score(tree, row, own):
    while isinstance(tree, tuple):
        address, branches = tree
        tree = branches[row[address]]
    return tree[row[own]]


def check_exposure(seed, alphabet=4, depths=(0, 1, 2, 2, 3)):
    rng = Random(seed)
    k = len(depths)
    trees = [side_tree(rng, alphabet, [j for j in range(k) if j != i], depths[i])
             for i in range(k)]
    total = sum(prod(local_score(tree, row, i) for i, tree in enumerate(trees))
                for row in product(range(alphabet), repeat=k))
    # Each leaf permutes the scores 0,...,alphabet-1. Normalize the (d_i+1)-th
    # powers by their common fiber means. Clearing exponents avoids floating point.
    powers = [d + 1 for d in depths]
    common = lcm(*powers)
    means = [Fraction(sum(s ** h for s in range(alphabet)), alphabet) for h in powers]
    assert Fraction(total, alphabet ** k) ** common <= prod(
        mean ** (common // h) for mean, h in zip(means, powers))


def clean_dip(z, values, t):
    last = next((y for y in range(z - 1, -1, -1) if values[y] <= values[z]), -1)
    return z - last >= t * (values[z] + 1)


def check_correlated_pairs(alphabet=8, t=2):
    # Two independent groups of two coordinates, with target group sum zero.
    k, h = 4, 2
    hit_count = 0
    for row in product(range(alphabet), repeat=k):
        hits = []
        for i, symbol in enumerate(row):
            partner = row[i ^ 1]
            values = [0 if (s + partner) % t == 0 else alphabet for s in range(alphabet)]
            hit = clean_dip(symbol, values, t)
            if symbol >= t - 1:
                assert hit == ((symbol + partner) % t == 0)
            hits.append(hit)
        hit_count += all(hits)
    rate = Fraction(hit_count, alphabet ** k)
    upper = Fraction(1, t ** (k // h))
    assert upper * (1 - Fraction(k * (t - 1), alphabet)) <= rate <= upper
    return rate


if __name__ == "__main__":
    for seed in range(40):
        check_exposure(seed)
    print("40 adaptive tree families passed the exact product bound")
    print(f"All-four-hit fraction for two pairs: {check_correlated_pairs()}")
