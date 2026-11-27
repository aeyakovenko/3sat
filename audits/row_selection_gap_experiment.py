"""Exact finite checks for the balanced-triple invariant. Uses only the standard library."""

from functools import cache
from itertools import combinations
from random import Random


def make_instance(variables, layer_count, seed):
    assert variables % 3 == 0 and layer_count % 2 == 0
    rng = Random(seed)
    layers = []
    for _ in range(layer_count):
        layer = list(range(variables))
        rng.shuffle(layer)
        layers.append(layer)
    row_count = variables * layer_count // 3
    charges = []
    for pair in range(row_count // 2):
        charge = rng.randrange(2)
        charges.extend([charge, charge ^ (pair == row_count // 2 - 1)])
    return layers, charges


def public_checks(layers, charges):
    variables = len(layers[0])
    for layer in layers:
        if any(not 0 <= address < variables for address in layer):
            return False
        if any(a == b for a, b in combinations(layer, 2)):
            return False
    return all(
        (charges[i] ^ charges[i + 1]) == (i == len(charges) - 2)
        for i in range(0, len(charges), 2)
    )


def row_masks(layers):
    return [
        sum(1 << address for address in layer[start:start + 3])
        for layer in layers
        for start in range(0, len(layer), 3)
    ]


def exhaustive_gap(variables, rows, charges):
    # A Gray-code step flips one variable and therefore precisely its incident rows.
    incident = [0] * variables
    for index, mask in enumerate(rows):
        for address in range(variables):
            if mask & (1 << address):
                incident[address] |= 1 << index
    failed = sum(charge << i for i, charge in enumerate(charges))
    minimum = failed.bit_count()
    for i in range(1, 1 << variables):
        flip = (i & -i).bit_length() - 1
        failed ^= incident[flip]
        count = failed.bit_count()
        assert count % 2 == 1
        minimum = min(minimum, count)
    return minimum


def exact_search_depth(variables, rows, charges):
    # At a leaf an equation fails on every completion iff all its bits have
    # been read and their parity is wrong. Search both replies to each query.
    @cache
    def solve(known, values):
        if any(mask & known == mask and (mask & values).bit_count() % 2 != charge
               for mask, charge in zip(rows, charges)):
            return 0
        choices = [1 << i for i in range(variables) if not (known >> i) & 1]
        return 1 + min(
            max(solve(known | bit, values), solve(known | bit, values | bit))
            for bit in choices
        )

    return solve(0, 0)


def augmented_selector(tree, first_leaf, actual_failed):
    """Return an initial row or an auxiliary equation violated by this assignment."""
    if tree[1] != 1:
        return "root", 1
    i = 1
    while i < first_leaf:
        left = 2 * i
        if tree[i] != (tree[left] ^ tree[left + 1]):
            return "node", i
        i = left if tree[left] else left + 1
    row = i - first_leaf
    if row >= len(actual_failed) or not actual_failed[row]:
        return "leaf", row
    return "row", row


def check_augmented_selector():
    # Four row residuals of odd parity; include every corrupted auxiliary tree.
    checked = 0
    for leaves in range(16):
        if leaves.bit_count() % 2 == 0:
            continue
        failed = [(leaves >> i) & 1 for i in range(4)]
        for bits in range(128):
            tree = [0] + [(bits >> i) & 1 for i in range(7)]
            kind, i = augmented_selector(tree, 4, failed)
            if kind == "row":
                assert failed[i]
            elif kind == "leaf":
                assert tree[4 + i] != failed[i]
            elif kind == "node":
                assert tree[i] != (tree[2 * i] ^ tree[2 * i + 1])
            else:
                assert kind == "root" and tree[1] != 1
            checked += 1
    return checked


def main():
    for variables, layer_count, seed in [(9, 4, 12), (12, 4, 37), (18, 48, 41)]:
        layers, charges = make_instance(variables, layer_count, seed)
        assert public_checks(layers, charges)
        broken = [list(layer) for layer in layers]
        broken[0][1] = broken[0][0]
        assert not public_checks(broken, charges)
        assert not public_checks(layers, [1 - charges[0], *charges[1:]])
        rows = row_masks(layers)
        minimum = exhaustive_gap(variables, rows, charges)
        assert minimum > 0
        depth = exact_search_depth(variables, rows, charges) if variables <= 12 else None
        print(f"variables={variables} layers={layer_count} min_failed={minimum}/{len(rows)}"
              f" exact_depth={depth if depth is not None else 'not computed'}")
    print(f"augmented selector checked on {check_augmented_selector()} auxiliary states")


if __name__ == "__main__":
    main()
