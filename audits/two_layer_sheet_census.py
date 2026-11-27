"""Count all labeled homogeneous two-layer port permutations after normalizing one matching."""

from collections import Counter
from itertools import permutations, product
from math import factorial


def count_presentations(side):
    """The first positive matching is identity. Cut the second positive edge at left 0."""
    perms = list(permutations(range(side)))
    assignments = 1 << side
    all_assignments = (1 << assignments) - 1
    ones = [sum(1 << state for state in range(assignments) if state >> j & 1)
            for j in range(side)]
    zeros = [all_assignments ^ word for word in ones]
    partitions = Counter()
    for perm in perms:
        allowed = all_assignments
        for i, target in enumerate(perm):
            allowed &= all_assignments ^ (ones[i] ^ ones[target])
        partitions[allowed] += 1
    inverses = {perm: [perm.index(i) for i in range(side)] for perm in perms}

    second_masks = Counter()
    for pos in perms:
        anchor = pos[0]
        if not anchor:
            second_masks[0] += len(perms)
            continue
        pos_inverse = inverses[pos]
        for neg in perms:
            neg_inverse = inverses[neg]
            # Two intact positive-self pins: the centers are physically one,
            # and their respective physical negative-port neighbors are zero.
            keep = ones[0] & zeros[anchor] & ones[neg[0]] & zeros[neg_inverse[anchor]]
            for i in range(1, side):
                keep &= zeros[i] | zeros[pos[i]] | ones[neg[i]]
            for j in range(side):
                if j != anchor:
                    keep &= ones[j] | ones[pos_inverse[j]] | zeros[neg_inverse[j]]
            second_masks[keep] += 1
    satisfiable = sum(
        frequency * sum(count for mask, count in partitions.items() if mask & second)
        for second, frequency in second_masks.items()
    )
    total = factorial(side) ** 3
    assert sum(second_masks.values()) * sum(partitions.values()) == total
    return satisfiable, total - satisfiable


def local_possible(center, shared):
    x, a, b, intact = center
    for y, z in product(range(2), repeat=2):
        triple = shared[x], y, z
        allowed = shared[x] == y == z or (not intact and triple in {(0, 0, 1), (1, 0, 0)})
        if allowed and (shared[a] or y or z) and not (shared[b] and y and z):
            return True
    return False



def direct_small_count(side):
    """Solve the original local OR clauses, without contracting a first-layer cycle."""
    perms = list(permutations(range(side)))
    identity = tuple(range(side))
    flags = [0, 0]
    for first_neg, second_pos, second_neg in product(perms, repeat=3):
        centers = []
        cut_right = second_pos[0]
        for layer, (pos, neg) in enumerate(((identity, first_neg), (second_pos, second_neg))):
            for left in range(side):
                cut = layer == 1 and left == 0
                centers.append((left, left if cut else side + pos[left], side + neg[left],
                                layer == 0 or cut))
            for right in range(side):
                cut = layer == 1 and right == cut_right
                centers.append((side + right, side + right if cut else pos.index(right),
                                neg.index(right), layer == 0 or cut))
        satisfiable = False
        for shared in product(range(2), repeat=2 * side):
            if all(local_possible(center, shared) for center in centers):
                satisfiable = True
                break
        flags[satisfiable] += 1
    return flags[1], flags[0]


def brute_one_pair_defects():
    """Count full assignments on a neutral pair, including private witnesses."""
    full = 0
    for bits in range(1 << 10):
        x, other = (bits >> i & 1 for i in range(2))
        valid = True
        for layer in range(2):
            for sheet, (center, neighbor) in enumerate(((x, other), (other, x))):
                offset = 2 + 4 * layer + 2 * sheet
                y, z = bits >> offset & 1, bits >> (offset + 1) & 1
                guard = center == y == z or (layer == 1 and (center, y, z) in {(0, 0, 1), (1, 0, 0)})
                valid &= guard and (neighbor or y or z) and not (neighbor and y and z)
        full += bool(valid)
    assert full == 4


if __name__ == "__main__":
    brute_one_pair_defects()
    for size in range(1, 7):
        yes, no = count_presentations(size)
        if size <= 3:
            assert (yes, no) == direct_small_count(size)
        print(f"{size:2d} sheets per side: {yes:>10} SAT  {no:>10} UNSAT")
