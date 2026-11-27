"""Exact XOR–AND gate exhaustion for the four bits of a 2-by-2 binary product.

Run with Python 3.10+. The default checks all 255 input hyperplanes directly.
--representatives checks six specified hyperplanes, useful for a quick replay.
"""

import argparse
from collections import Counter
from itertools import combinations


def product(left, right):
    """Return the four row-major bits of the product over GF(2)."""
    result = 0
    for row in range(2):
        for col in range(2):
            bit = 0
            for inner in range(2):
                bit ^= (left >> (2 * row + inner)) & (right >> (2 * inner + col)) & 1
            result |= bit << (2 * row + col)
    return result


def strassen(left, right):
    a, b, c, d = [(left >> i) & 1 for i in range(4)]
    e, f, g, h = [(right >> i) & 1 for i in range(4)]
    p = (a ^ d) & (e ^ h)
    q = (c ^ d) & e
    r = a & (f ^ h)
    s = d & (g ^ e)
    t = (a ^ b) & h
    u = (c ^ a) & (e ^ f)
    v = (b ^ d) & (g ^ h)
    return (p ^ s ^ t ^ v) | ((r ^ t) << 1) | ((q ^ s) << 2) | ((p ^ q ^ r ^ u) << 3)


def independent(vectors):
    pivots = {}
    for value in vectors:
        while value:
            i = value.bit_length() - 1
            if i not in pivots:
                pivots[i] = value
                break
            value ^= pivots[i]
    return list(pivots.values())


def span(basis):
    items = [0]
    for item in basis:
        items += [v ^ item for v in items]
    return items


def closure(free_basis, ambient_basis):
    """Return a basis and all elements of the least reachable space in the ambient."""
    basis = list(free_basis)
    available = set(span(basis))
    ambient = set(span(independent(ambient_basis)))
    while True:
        for x, y in combinations(available, 2):
            z = x & y
            if z in ambient and z not in available:
                break
        else:
            return basis, available
        basis.append(z)
        available.update([item ^ z for item in available])


def restriction(table, mask):
    """Restrict to the marked points and subtract the value at the first point."""
    first = mask & -mask
    return (table & mask) ^ (mask if table & first else 0)


def one_extra(free_basis, outputs, domain):
    """Decide the rank-plus-one budget. Return decision and sieve statistics."""
    target_basis = independent(free_basis + outputs)
    target = set(span(target_basis))
    prefix_basis, prefix = closure(free_basis, target_basis)
    if all(value in prefix for value in outputs):
        return True, 0, 0

    viable = set()
    for factor in prefix - {0}:
        for fiber in (factor, domain ^ factor):
            assert fiber
            restricted_free = independent([restriction(v, fiber) for v in prefix_basis])
            restricted_outputs = [restriction(v, fiber) for v in outputs]
            _, reachable = closure(restricted_free, restricted_free + restricted_outputs)
            if any(v not in reachable for v in restricted_outputs):
                break
        else:
            viable.add(factor)

    cosets = set()
    for left, right in combinations(sorted(viable), 2):
        third = left ^ right
        if third <= right or third not in viable:
            continue
        hidden = left & right
        if hidden in target:
            continue
        representative = min(hidden ^ v for v in target)
        if representative in cosets:
            continue
        cosets.add(representative)
        _, reachable = closure(free_basis, target_basis + [representative])
        if all(value in reachable for value in outputs):
            return True, len(viable), len(cosets)
    return False, len(viable), len(cosets)


def on_hyperplane(normal):
    points = [x for x in range(256) if (normal & x).bit_count() % 2 == 0]
    assert len(points) == 128 and points[0] == 0
    inputs = [sum(((x >> i) & 1) << j for j, x in enumerate(points)) for i in range(8)]
    answers = [product(x & 15, x >> 4) for x in points]
    outputs = [sum(((y >> i) & 1) << j for j, y in enumerate(answers)) for i in range(4)]
    free = independent(inputs)
    assert len(free) == 7 and len(independent(free + outputs)) == 11
    return one_extra(free, outputs, (1 << 128) - 1)


def three_bit_crosscheck():
    """Compare to breadth-first enumeration of every reachable span on three bits."""
    inputs = [sum(((x >> i) & 1) << x for x in range(8)) for i in range(3)]
    start = frozenset(span(inputs))
    frontier = {start}
    reached = set()
    while frontier:
        following = set()
        for space in frontier:
            for a, b in combinations(space, 2):
                h = a & b
                if h not in space:
                    following.add(space | {v ^ h for v in space})
        reached.update(frontier)
        frontier = following - reached

    # All subspaces between the input space and the full normalized truth tables.
    spaces = {start}
    for table in range(0, 256, 2):
        spaces.update([space | {v ^ table for v in space} for space in spaces])
    assert len(spaces) == 67
    for target in spaces:
        actual = any(target <= space and len(space) <= 2 * len(target) for space in reached)
        reported, _, _ = one_extra(inputs, independent(target), 255)
        assert reported == actual
    return len(spaces)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--representatives", action="store_true")
    args = parser.parse_args()
    for a in range(16):
        for b in range(16):
            assert product(a, b) == strassen(a, b)
    print("Strassen on 256 inputs; three-bit cross-check on", three_bit_crosscheck(), "spaces", flush=True)
    representatives = [1, 6, 17, 18, 22, 102]
    normals = representatives if args.representatives else range(1, 256)
    counts = Counter()
    for normal in normals:
        feasible, factors, cosets = on_hyperplane(normal)
        assert not feasible, f"Five ANDs suffice on normal {normal}"
        counts[factors, cosets] += 1
        if normal in representatives:
            print(f"normal {normal:3}: {factors} surviving factors, {cosets} exterior cosets", flush=True)
    expected = {(5, 2): 1, (3, 0): 1, (0, 0): 4}
    if not args.representatives:
        expected = {(5, 2): 18, (3, 0): 12, (0, 0): 225}
    assert counts == expected
    print(f"Five gates excluded on {sum(counts.values())} hyperplanes.")


if __name__ == "__main__":
    main()
