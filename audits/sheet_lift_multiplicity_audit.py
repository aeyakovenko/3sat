"""Exhaust labeled small matchings and check fiber sizes from the original local clauses."""

from itertools import permutations, product
from math import prod


def partners(perm):
    matching = [0] * (2 * len(perm))
    for i, j in enumerate(perm):
        u, v = 2 * i, 2 * j + 1
        matching[u], matching[v] = v, u
    return tuple(matching)


def local_weight(intact, x, a, b):
    mixed = set(product(range(2), repeat=3)) - {(0, 0, 0), (1, 1, 1)}
    forbidden = mixed if intact else mixed - {(0, 0, 1), (1, 0, 0)}
    return sum(
        (x, y, z) not in forbidden and bool(a or y or z) and not (b and y and z)
        for y, z in product(range(2), repeat=2)
    )


WEIGHT = {(i, x, a, b): local_weight(i, x, a, b)
          for i, x, a, b in product(range(2), repeat=4)}


def fibers(maps):
    first_pos, first_neg, second_pos, second_neg = maps
    size = len(first_pos)
    anchors = [u == second_pos[u] for u in range(size)]
    assert sum(anchors) == 2
    output = {}
    for bits in product(range(2), repeat=size):
        weights = (WEIGHT[1, bits[u], bits[first_pos[u]], bits[first_neg[u]]] *
                   WEIGHT[anchors[u], bits[u], bits[second_pos[u]], bits[second_neg[u]]]
                   for u in range(size))
        choices = prod(weights)
        if choices:
            cuts = sum(bits[u] != bits[second_neg[u]] for u in range(0, size, 2))
            assert 2 <= cuts <= size // 2
            assert cuts % 2 == (size // 2) % 2
            assert choices == 1 << (cuts - 2)
            output[bits] = choices
    return output


def cut_presentation(first_neg, second_pos, second_neg):
    n = len(first_neg)
    pos = list(partners(second_pos))
    other_anchor = pos[0]
    pos[0], pos[other_anchor] = 0, other_anchor
    return (partners(range(n)), partners(first_neg), tuple(pos), partners(second_neg))


def lift(maps, u):
    size = len(maps[0])
    same, other = size + u % 2, size + 1 - u % 2
    first_pos, first_neg, second_pos, second_neg = [list(m) + [-1, -1] for m in maps]
    assert u != second_pos[u]

    def match(m, i, j):
        m[i], m[j] = j, i

    match(first_pos, same, other)
    old = first_neg[u]
    match(first_neg, u, other)
    match(first_neg, same, old)
    for m in (second_pos, second_neg):
        partner = m[u]
        match(m, same, partner)
        match(m, u, other)
    return (first_pos, first_neg, second_pos, second_neg)


def calibrated_double_lift(maps):
    size = len(maps[0])
    anchors = [u for u, v in enumerate(maps[2]) if u == v]
    first_pos, first_neg, second_pos, second_neg = [list(m) + [-1] * 4 for m in maps]
    for k, u in enumerate(anchors):
        same, other = size + 2 * k + u % 2, size + 2 * k + 1 - u % 2
        first_pos[same], first_pos[other] = other, same
        old = first_neg[u]
        first_neg[u], first_neg[other] = other, u
        first_neg[same], first_neg[old] = old, same
    for m in (second_pos, second_neg):
        for i, j in ((size, size + 3), (size + 1, size + 2)):
            m[i], m[j] = j, i
    return (first_pos, first_neg, second_pos, second_neg)


def components(maps):
    unseen = set(range(len(maps[0])))
    count = 0
    while unseen:
        count += 1
        stack = [unseen.pop()]
        while stack:
            v = stack.pop()
            for m in maps:
                u = m[v]
                if u in unseen:
                    unseen.remove(u)
                    stack.append(u)
    return count


def main():
    for n in (1, 2, 3):
        perms = list(permutations(range(n)))
        presentations = models = lifts = satisfiable = odd_counts = 0
        for first_neg, second_pos, second_neg in product(perms, repeat=3):
            maps = cut_presentation(first_neg, second_pos, second_neg)
            weights = fibers(maps)
            count = sum(weights.values())
            presentations += 1
            models += count
            satisfiable += bool(count)
            odd_counts += count % 2
            # The left anchor is vertex zero, so the right anchor is listed second.
            double = calibrated_double_lift(maps)
            assert fibers(double) == {bits + (1, 0, 0, 1): value
                                      for bits, value in weights.items()}
            assert components(double) <= components(maps)
            for u, v in enumerate(maps[2]):
                if u == v:
                    continue
                extended = lift(maps, u)
                for layer_map in extended:
                    assert all(layer_map[mate] == i for i, mate in enumerate(layer_map))
                assert components(extended) == components(maps)
                left = u % 2 == 0
                expected = {
                    bits + ((bits[u], 1 - bits[u]) if left else (1 - bits[u], bits[u])):
                    2 * completions for bits, completions in weights.items()
                }
                assert fibers(extended) == expected
                lifts += 1
        print(f"size {n}: {presentations} presentations, {satisfiable} SAT, "
              f"{models} full models, {odd_counts} odd counts, {lifts} connected lifts")


if __name__ == "__main__":
    main()
