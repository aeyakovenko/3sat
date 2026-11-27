"""Finite checks for the fixed-mask determinant arguments in determinant-tests.md."""

from collections import defaultdict
from itertools import combinations, permutations, product
from math import factorial


def permutation_data(order):
    data = []
    for perm in permutations(range(order)):
        inversions = sum(a > b for a, b in combinations(perm, 2))
        edges = sum(1 << (order * i + j) for i, j in enumerate(perm))
        data.append((edges, (-1) ** inversions))
    return data


def check_union_coefficients(order):
    groups = defaultdict(list)
    data = permutation_data(order)
    for edges, sign in data:
        for other, other_sign in data:
            groups[edges | other].append((edges & other, sign * other_sign))

    for support, members in groups.items():
        # The Boolean union determines both the doubled edges and the relative sign.
        assert len(set(members)) == 1
        doubles, relative_sign = members[0]
        if support == doubles:
            assert len(members) == 1 and relative_sign == 1
        else:
            assert len(members) >= 2 and (len(members) & (len(members) - 1)) == 0
    print(f'order {order}: {len(groups)} Boolean supports from {factorial(order) ** 2} ordered pairs')


def normalized_signings(order):
    # Row and column flips fix the first row and column at +1.
    for negative_bits in range(1 << (order - 1) ** 2):
        yield sum(((negative_bits >> ((i - 1) * (order - 1) + j - 1)) & 1)
                  << (order * i + j) for i in range(1, order) for j in range(1, order))


def check_three_by_three():
    data = permutation_data(3)
    masks = list(normalized_signings(3))
    characters = {tuple((-1) ** ((s & (e ^ f)).bit_count()) for s in masks)
                  for e, _ in data for f, _ in data}
    assert len(characters) == 16
    assert all(sum(a * b for a, b in zip(x, y)) == 0
               for x, y in combinations(characters, 2))
    for host in range(512):
        allowed = [(e, sign) for e, sign in data if e & host == e]
        dets = [sum(sign * (-1) ** ((s & e).bit_count()) for e, sign in allowed)
                for s in masks]
        assert sum(det ** 2 for det in dets) == len(masks) * len(allowed)
    print('order 3: full 16-character system and exact mean on all 512 binary hosts')


def check_boxes():
    pairs = [(0, 1), (1, 2), (2, 0)]
    one_block = {tuple(i for i, (a, b) in enumerate(pairs) if ratios[a] != ratios[b])
                 for ratios in product((-1, 1), repeat=3)}
    assert one_block == {(), (0, 1), (0, 2), (1, 2)}
    for blocks in range(1, 5):
        hosts = set(product(range(3), repeat=blocks))
        sizes = {len(set(product(*choices)) & hosts)
                 for choices in product(one_block, repeat=blocks)}
        assert sizes == {0, 2 ** blocks}
    print('one through four blocks: all nonempty signing supports have exactly 2^b hosts')


if __name__ == '__main__':
    for order in range(2, 6):
        check_union_coefficients(order)
    check_three_by_three()
    check_boxes()
