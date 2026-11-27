"""Finite checks for the masked parity identity, sharpness and the F4 readout."""

from itertools import combinations, product
from math import comb
from random import Random


def subsets(width, max_size):
    for size in range(max_size + 1):
        for indices in combinations(range(width), size):
            yield sum(1 << i for i in indices)


def product_low(a, b, width):
    """Multiply modulo t^width in F2[t], using binary coefficient strings."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
    return result & ((1 << width) - 1)


def masked_sum(terms, width, budget):
    result = 0
    for mask in subsets(width, budget):
        at_one = 0
        low = 0
        for exponents in terms:
            if any(e and mask & (1 << i) for i, e in enumerate(exponents)):
                continue
            at_one ^= 1
            monomial = 1
            for e in exponents:
                monomial = product_low(monomial, 1 << e, width)
            low ^= monomial
        result ^= at_one ^ (low.bit_count() & 1)
    return result


def cube_sum(terms, width):
    result = 0
    for assignment in range(1 << width):
        for exponents in terms:
            result ^= all(not e or assignment & (1 << i)
                          for i, e in enumerate(exponents))
    return result


def check_monomials():
    checked = 0
    for v in range(1, 7):
        for exponents in product(range(4), repeat=v):
            zeros = exponents.count(0)
            for budget in range(v + 1):
                if sum(exponents) >= v and zeros > budget:
                    continue
                support = sum(1 << i for i, e in enumerate(exponents) if e)
                multiplicity = sum(mask & support == 0 for mask in subsets(v, budget))
                value = sum(exponents) >= v and multiplicity % 2 == 1
                assert value == (zeros == 0)
                checked += 1
    return checked


def check_polynomials():
    rng = Random(64911)
    checked = 0
    for v in range(1, 7):
        for b in range(v + 1):
            for _ in range(7):
                terms = []
                for _ in range(8):
                    term = tuple(rng.choice((0, 0, 1, 2, 5, 35)) for _ in range(v))
                    if sum(term) < v or term.count(0) <= b:
                        terms.append(term)
                    else:
                        # The formal condition is imposed after cancellation.
                        terms.extend([term, term])
                # Include a full monomial of arbitrarily high intermediate degree.
                terms.append((91,) + (1,) * (v - 1))
                assert masked_sum(terms, v, b) == cube_sum(terms, v)
                checked += 1
    return checked


def check_invisible_polynomials():
    identities = 0
    for v in range(1, 9):
        full = (1 << v) - 1
        for hidden in range(full):
            anchors = [i for i in range(v) if not hidden & (1 << i)]
            factors = [i for i in range(v) if hidden & (1 << i)]
            # Distinct anchors whenever there are enough outside coordinates.
            for mask in range(full + 1):
                values = full ^ mask
                active = (values & (full ^ hidden)) == (full ^ hidden)
                for index, i in enumerate(factors):
                    anchor = anchors[index % len(anchors)]
                    active &= bool(((values >> i) ^ (values >> anchor)) & 1)
                assert active == (mask == hidden)
                identities += 1
    return identities


def check_moment_matrices():
    entries = 0
    for v in range(1, 9):
        full = (1 << v) - 1
        for budget in range(v + 1):
            levels = list(subsets(v, budget))
            for i, a in enumerate(levels):
                for j, b in enumerate(levels):
                    support = a | (full ^ b)
                    assert v - support.bit_count() <= budget
                    assert (support == full) == ((a & b) == b)
                    if j >= i:
                        assert (support == full) == (i == j)
                    entries += 1

            total_rank = 0
            for size in range(v + 1):
                core = (1 << max(0, size - budget)) - 1
                family = [a for a in range(full + 1)
                          if a.bit_count() == size and a & core == core]
                for a in family:
                    for b in family:
                        support = a | (full ^ b)
                        assert v - support.bit_count() <= budget
                        assert (support == full) == (a == b)
                        entries += 1
                total_rank += len(family)
            assert total_rank == sum(comb(v, i) for i in range(min(v, budget + 1) + 1))
    return entries


def f4mul(a, b):
    raw = (a if b & 1 else 0) ^ (a << 1 if b & 2 else 0)
    return raw ^ (0b111 if raw & 4 else 0)


def diagonal_weight(point, width):
    weight = 1
    for i in range(width):
        weight = f4mul(weight, 2 if point & (1 << i) else 3)
    return weight


def check_fixed_point():
    checked = 0
    for m in range(4):
        full = (1 << m) - 1
        weights = [diagonal_weight(z, 2 * m) for z in range(1 << (2 * m))]
        for predicate in range(1 << (1 << m)):
            canonical = 0
            for z, weight in enumerate(weights):
                x, y = z & full, z >> m
                hole = y == (full ^ x) and predicate & (1 << x)
                if not hole:
                    canonical ^= weight
            assert canonical == (1 ^ (predicate.bit_count() % 2))
            checked += 1
    return checked


def field_mul(a, b, modulus):
    top = 1 << (modulus.bit_length() - 1)
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & top:
            a ^= modulus
    return result


def field_pow(a, exponent, modulus):
    result = 1
    while exponent:
        if exponent & 1:
            result = field_mul(result, a, modulus)
        a = field_mul(a, a, modulus)
        exponent >>= 1
    return result


def hole_weights(t, v, modulus):
    return [field_mul(field_pow(t, h, modulus), field_pow(1 ^ t, v - h, modulus),
                      modulus) for h in range(v + 1)]


def check_unmodified_point():
    modulus = 0b11111
    u = 2
    t = field_mul(u, field_pow(1 ^ u, 14, modulus), modulus)
    roots = {field_pow(u, i, modulus) for i in range(5)}
    assert roots == {y for y in range(16) if field_pow(y, 5, modulus) == 1}
    pairs = {a ^ b for a, b in combinations(roots, 2)}
    assert pairs == set(range(1, 16)) - roots
    checked = 0
    for v in range(1, 38):
        weights = hole_weights(t, v, modulus)
        scale = field_pow(field_pow(1 ^ t, 14, modulus), v, modulus)
        for h, weight in enumerate(weights):
            normalized = field_mul(scale, weight, modulus)
            assert normalized == field_pow(u, h, modulus)
            assert field_pow(normalized, 5, modulus) == 1
            for other in weights:
                pair = field_mul(scale, weight ^ other, modulus)
                assert field_pow(pair, 5, modulus) != 1
                checked += 1

    for size, mod in ((2, 0b11), (4, 0b111), (8, 0b1011)):
        for v in range(max(2, size - 2), 38):
            for scalar in range(size):
                weights = hole_weights(scalar, v, mod)
                antipodal = {w ^ weights[v - h] for h, w in enumerate(weights)}
                assert set(weights) & antipodal
                checked += 1
    return checked


if __name__ == "__main__":
    print(f"{check_monomials()} filtered monomial identities")
    print(f"{check_polynomials()} full polynomial checks with cancellation and high powers")
    print(f"{check_invisible_polynomials()} masked-line lower-bound checks")
    print(f"{check_moment_matrices()} complementary subset moment entries")
    print(f"{check_fixed_point()} complete F4 diagonal checks on balanced Boolean predicates")
    print(f"{check_unmodified_point()} unmodified F16 and smaller-field checks")
