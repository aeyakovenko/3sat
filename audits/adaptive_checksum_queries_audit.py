"""Finite tests for product-field and adaptive SAT checksum identities."""

from fractions import Fraction
from math import prod
from itertools import permutations, product
from random import Random

from checksum_pair_certificates_audit import combination_for_constant
from checksum_selector_distance_audit import BinaryField


def parity(word):
    return word.bit_count() & 1


def paired_field_automorphisms(field):
    """Enumerate all invertible binary linear maps of F4 x F4."""
    def mul(a, b):
        return field.mul[a & 3][b & 3] | (field.mul[a >> 2][b >> 2] << 2)

    one = 5
    automorphisms = set()
    linear_maps = 0
    for basis in permutations(range(1, 16), 4):
        images = [0]
        for column in basis:
            if column in images:
                break
            images += [x ^ column for x in images]
        if len(images) != 16:
            continue
        linear_maps += 1
        if images[one] != one:
            continue
        if all(images[mul(1 << i, 1 << j)] == mul(basis[i], basis[j])
               for i in range(4) for j in range(4)):
            automorphisms.add(tuple(images))
    expected = set()
    for swap, square_a, square_b in product(range(2), repeat=3):
        images = []
        for x in range(16):
            a, b = x & 3, x >> 2
            if square_a:
                a = field.square(a)
            if square_b:
                b = field.square(b)
            images.append((b | (a << 2)) if swap else (a | (b << 2)))
        expected.add(tuple(images))
    assert linear_maps == 20160 and len(expected) == 8
    assert automorphisms == expected
    return linear_maps


def all_words(field, dimension):
    # Generate the binary trace digits by linearity in the mask.
    words = {}
    for point in product(range(field.q), repeat=dimension):
        factors = field.factors(point)
        columns = [sum(field.trace[field.mul[1 << k][z]] << i
                       for i, z in enumerate(factors)) for k in range(field.s)]
        masks = [0]
        for column in columns:
            masks += [w ^ column for w in masks]
        for mask, word in enumerate(masks):
            words.setdefault(word, []).append((point, mask))
    return words


def orbit(field, desc):
    point, mask = desc
    return {(point, mask), (tuple(map(field.square, point)), field.square(mask))}


def split_query(field, point, mask, coord):
    left, right = list(point), list(point)
    left[coord], right[coord] = 0, 1
    u = field.word(left, field.mul[mask][point[coord] ^ 1])
    v = field.word(right, field.mul[mask][point[coord]])
    assert field.word(point, mask) == u ^ v
    return u, v


def bounded_tree_distance(target, first, words, all_bits):
    """Optimal second query and optimal Boolean leaf labels on each root branch."""
    def branch_cost(block):
        desired = target & block
        size = block.bit_count()
        cost = min(desired.bit_count(), size - desired.bit_count())
        for second in words:
            split = block & second
            other = block ^ split
            ones_s = (desired & split).bit_count()
            ones_o = (desired & other).bit_count()
            error = min(ones_s, split.bit_count()-ones_s) + min(ones_o, other.bit_count()-ones_o)
            cost = min(cost, error)
            if cost == 0:
                break
        return cost

    return branch_cost(first) + branch_cost(all_bits ^ first)


def audit_formula_queries(field):
    rng = Random(85179)
    dimension = 6
    words = all_words(field, dimension)
    all_bits = (1 << (1 << dimension)) - 1
    interior = [desc[0] for desc in words.values()
                if desc[0][1] and all(x >= 2 for x in desc[0][0])]
    classified = 0
    tree_costs = []
    for trial in range(80):
        one, two = rng.sample(interior, 2)
        a, b = (field.word(*z) for z in (one, two))
        target = a ^ b
        # Exact search over all (including all boundary and zero-mask)
        # descriptor pairs by one pass and an exact complement lookup.
        representations = {w for w in words if (target ^ w) in words}
        assert {a, b} <= representations
        if representations != {a, b}:
            continue
        assert set(words[a]) == orbit(field, one) and set(words[b]) == orbit(field, two)
        classified += 1
        u, v = split_query(field, *one, trial % dimension)
        assert u ^ v ^ b == target
        assert u not in (a, b) and v not in (a, b)
        if classified <= 4:
            # Each root is chosen outside the two true selectors. The second
            # query is optimized freely and independently on both branches.
            wrong_roots = rng.sample(sorted(set(words) - {a, b}), 10)
            for first in wrong_roots:
                cost = bounded_tree_distance(target, first, words, all_bits)
                assert cost >= 0
                tree_costs.append(cost)
            assert bounded_tree_distance(target, a, words, all_bits) == 0
    assert classified >= 15 and tree_costs and max(tree_costs) > 0
    return len(words), classified, tree_costs


def check_leaf_expansions():
    # All four depth-two leaf outputs, all assignments of the three node
    # replies, and all fixed old reply bits for the re-labeling calculation.
    count = 0
    for leaf_values in product((-1, 1), repeat=4):
        for u in product((-1, 1), repeat=3):
            for old in product((-1, 1), repeat=3):
                replies = tuple(x*y for x, y in zip(u, old))
                branch = int(replies[0] < 0)
                answer = leaf_values[2*branch + int(replies[1+branch] < 0)]
                scaled = 0
                for branch in range(2):
                    for child in range(2):
                        a = (1-2*branch) * replies[0]
                        b = (1-2*child) * replies[1+branch]
                        scaled += leaf_values[2*branch+child] * (1 + a + b + a*b)
                assert scaled == 4*answer
                count += 1
    return count



def block_grid_check(field):
    """Exact vanishing fractions and signed certificates over small direction grids."""
    rng = Random(69865)

    def monomials(caps, point):
        vec = [1]
        for cap, t in zip(caps, point):
            column = [1]
            for _ in range(cap):
                column.append(field.mul[column[-1]][t])
            vec = [field.mul[z][p] for z in vec for p in column]
        return vec

    def grid(caps):
        points = product(range(1, field.q), repeat=len(caps))
        evaluations = [monomials(caps, point) for point in points]
        largest = 0
        for tail in product(range(field.q), repeat=len(evaluations[0])-1):
            zero = 0
            for vals in evaluations:
                value = 1
                for c, v in zip(tail, vals[1:]):
                    value ^= field.mul[c][v]
                zero += value == 0
            largest = max(largest, zero)
        zero_bound = 1 - prod(Fraction(field.q-1-k, field.q-1) for k in caps)
        assert Fraction(largest, len(evaluations)) == zero_bound
        mask_rows = []
        for vals, mask in product(evaluations, range(field.q)):
            value = field.trace[mask]
            shift = 1
            for z in vals[1:]:
                for e in range(field.s):
                    value |= field.trace[field.mul[field.mul[mask][z]][1 << e]] << shift
                    shift += 1
            mask_rows.append(value)
        return zero_bound, mask_rows, len(evaluations[0])

    checked = 0
    for block_sizes in ((2,), (1, 1)):
        caps_by_direction = []
        for direction in product(range(field.q), repeat=2):
            offset = 0
            caps = []
            for size in block_sizes:
                caps.append(sum(a != 0 for a in direction[offset:offset+size]))
                offset += size
            caps_by_direction.append(tuple(caps))
        grid_data = {caps: grid(caps) for caps in set(caps_by_direction)}
        z = [grid_data[caps][0] for caps in caps_by_direction]
        mean = 1-prod(1-Fraction(size, field.q) for size in block_sizes)
        assert sum(z)/len(z) == mean
        pair_average = sum((1+v*w)/2 for v, w in product(z, repeat=2))/(len(z)**2)
        assert pair_average == (1+mean**2)/2
        for acaps, bcaps in product(grid_data, repeat=2):
            za, left, a_cols = grid_data[acaps]
            zb, right, b_cols = grid_data[bcaps]
            shift = field.s*(a_cols-1)
            rows = [a ^ (b & 1) ^ ((b & ~1) << shift) for a, b in product(left, right)]
            threshold_count = len(rows)*(1+za*zb)/2
            assert threshold_count.denominator == 1
            chosen = rng.sample(rows, int(threshold_count)+1)
            certificate = combination_for_constant(chosen)
            assert 0 < certificate.bit_count() <= 1+field.s*(a_cols+b_cols-2)
            combined = 0
            for i, row in enumerate(chosen):
                if certificate & (1 << i):
                    combined ^= row
            assert combined == 1
            checked += 1
    return checked


if __name__ == '__main__':
    field = BinaryField(4, 0b111)
    maps = paired_field_automorphisms(field)
    words, classified, tree_costs = audit_formula_queries(field)
    expansions = check_leaf_expansions()
    print(f'{maps} invertible maps checked with exactly 8 product-field automorphisms.')
    print(f'{words} distinct selectors searched against 80 pairs; {classified} had only the original decomposition.')
    print(f'{len(tree_costs)} alternative roots with optimal adaptive continuations on flips, errors {min(tree_costs)} to {max(tree_costs)} of 64.')
    print(f'{expansions} leaf and reply assignments reproduced the signed tree expansion.')
    print(f'{block_grid_check(field)} pairs of degree grids certified the constant with exact direction-average thresholds.')
