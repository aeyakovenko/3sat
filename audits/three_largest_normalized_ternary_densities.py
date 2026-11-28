#!/usr/bin/env python3
"""Compute exact exposure bounds for connected subfamilies of ternary supports."""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations


Q = Fraction(7, 8)
CUTOFF = Fraction(13, 14)
PAIR = Fraction(46, 49)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask -= bit


@lru_cache(None)
def exposure(edges):
    if not edges:
        return Fraction(1)
    if 0 in edges:
        return Fraction(0)
    names = 0
    for edge in edges:
        names |= edge
    choices = []
    for bit in bits(names):
        hit = tuple(edge for edge in edges if not edge & bit)
        shortened = tuple(sorted({edge & ~bit for edge in edges}))
        choices.append((exposure(hit) / Q + exposure(shortened)) / 2)
    return min(choices)


def key(edges):
    """Columns of the incidence matrix up to permutations of both axes."""
    names = set().union(*map(set, edges))
    return min(tuple(sorted(sum((v in edge) << i for i, edge in enumerate(order))
                            for v in names)) for order in permutations(edges))


def grow(edges):
    fresh = 1 + max(max(edge) for edge in edges)
    for known in range(1, 4):
        for old in combinations(range(fresh), known):
            edge = old + tuple(range(fresh, fresh + 3 - known))
            if edge not in edges:
                yield edges + (edge,)


def supports(edges):
    return tuple(sorted(sum(1 << v for v in edge) for edge in edges))


def component_data(edges):
    n = 1 + max(max(edge) for edge in edges)
    masks = supports(edges)
    tau = min(p.bit_count() for p in range(1 << n) if all(p & e for e in masks))
    return n, tau


def main():
    first = ((0, 1, 2),)
    good = {key(first): first}
    expected = [(2, 2), (9, 2), (26, 0)]
    for num_edges, counts in enumerate(expected, start=2):
        next_types = {key(new): new for edges in good.values() for new in grow(edges)}
        good = {ident: edges for ident, edges in next_types.items()
                if exposure(supports(edges)) > CUTOFF}
        assert (len(next_types), len(good)) == counts
        for component in good.values():
            n, tau = component_data(component)
            assert (tau == 1 and n <= 5) or (tau == 2 and n <= 6)
            # Every assignment to the actual names contributes one unit on this grid.
            possible = {Fraction(a, 1 << n) / Q**tau for a in range((1 << n) + 1)}
            assert all(value == PAIR for value in possible if CUTOFF < value <= PAIR)
        print(f"{num_edges} distinct supports: {len(next_types)} connected extensions, "
              f"{len(good)} above {CUTOFF}")
    for edges, density in [(((0, 1, 2), (0, 1, 3)), CUTOFF),
                           (((0, 1, 2), (0, 1, 3), (2, 3, 4)), PAIR)]:
        n, tau = component_data(edges)
        masks = supports(edges)
        models = sum(all(row & edge for edge in masks) for row in range(1 << n))
        assert Fraction(models, 1 << n) / Q**tau == density
    k = Fraction(4, 7)**4
    assert Fraction(4, 7)*CUTOFF == 5*k - Fraction(6, 2401)
    assert Fraction(4, 7)*PAIR == 5*k + Fraction(8, 2401)
    print("Largest three normalized densities and the five-edit slice gap verified.")


if __name__ == "__main__":
    main()
