"""Check the common-bit lookup and replacement of the terminal selector profile."""

from fractions import Fraction as F
from itertools import product
from random import Random


def wires(size, offset):
    ans = [0]
    for mask in range(1, 1 << size):
        low = (mask & -mask).bit_length() - 1
        ans.append(ans[mask & (mask - 1)] ^ int(low == offset))
    return ans


def select(rows, width, g, j):
    table = wires(g, j % g)
    result = []
    for column in range(len(rows[0])):
        value = 0
        for lane in range(width):
            bit = 0
            for base in range(0, len(rows), g):
                packed = sum(((row[column] >> lane) & 1) << k
                             for k, row in enumerate(rows[base:base + g]))
                bit |= (base // g == j // g) & table[packed]
            value |= bit << lane
        result.append(value)
    return result


def selector_checks(rng):
    count = 0
    for g in (1, 2, 4, 8):
        for d in range(g):
            for mask, bit in enumerate(wires(g, d)):
                assert bit == (mask >> d) & 1
                count += 1
        for p, s, w in ((7, 3, 4), (17, 4, 8), (33, 2, 11)):
            arr = [[rng.randrange(1 << w) for _ in range(s)] for _ in range(p)]
            for j in range(p):
                assert select(arr, w, g, j) == arr[j]
                count += 1
    return count


def cost(c, rho, seq):
    pre, terms, ordinary, list_floor = F(0), F(1), F(0), None
    for work, base_input, own_list in seq:
        ordinary = max(ordinary, base_input + pre)
        v = own_list + pre
        list_floor = v - c if list_floor is None else max(list_floor, v - c)
        terms += v - c
        pre += work
    return max((terms + pre) / (len(seq) + 1), list_floor, pre - rho - c), ordinary


def compare():
    trials = replacements = 0
    for c, rho in ((F(2, 3), F(2, 3)), (F(2873, 4000), F(2, 3)),
                   (F(83, 100), F(3, 4)), (F(49, 50), F(9, 10))):
        star = (1 - c / 2, 0, 0)
        special = (F(1), 0, rho - 1)
        alternatives = (special, star, (F(1, 3), F(1, 5), F(1, 5)),
                        (F(1, 17), F(3, 5), F(3, 5)), (F(1, 29), c, c))
        for k in range(1, 6):
            for seq in product(alternatives, repeat=k):
                d, floor = cost(c, rho, seq)
                if special in seq and (d < 0 or floor < c):
                    assert seq[-1] == special and special not in seq[:-1]
                    new, newfloor = cost(c, rho, seq[:-1] + (star,))
                    assert newfloor == floor
                    assert new <= d if d >= 0 else new < 0
                    replacements += 1
                trials += 1
    return trials, replacements


if __name__ == "__main__":
    n = selector_checks(Random(107749))
    trials, used = compare()
    print(f"{n} shared-selector checks; {trials} rational profile tuples, "
          f"{used} useful terminal replacements")
