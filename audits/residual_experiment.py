"""Exhaust the interpolation family on full Boolean cubes and test a field jump."""

from math import comb, prod


def evaluate_polynomial(monomials, seed):
    return sum((seed & term) == term for term in monomials) % 2


def check_interpolation(bits, degree):
    cube = range(1 << bits)
    small = [mask for mask in cube if mask.bit_count() <= degree]
    assert len(small) == sum(comb(bits, j) for j in range(degree + 1))
    parity = [0] * len(cube)
    for index in small:
        terms = [term for term in small if term & index == index]
        assert max(term.bit_count() for term in terms) <= degree
        for seed in cube:
            value = evaluate_polynomial(terms, seed)
            parity[seed] ^= value
            if seed.bit_count() <= degree:
                assert value == int(seed == index)
    assert all(parity)
    return len(small)


def equality_extension(seed, point, prime):
    factors = (coordinate if seed & (1 << i) else 1 - coordinate
               for i, coordinate in enumerate(point))
    return prod(factors) % prime


def check_field_point(bits):
    # 2 is outside the Boolean domain even in the field with three elements.
    for seed in range(1 << bits):
        for index in range(1 << bits):
            point = [(index >> i) & 1 for i in range(bits)]
            assert equality_extension(seed, point, 3) == int(seed == index)
        assert equality_extension(seed, [2] * bits, 3) != 0


if __name__ == "__main__":
    for bits in range(9):
        counts = [check_interpolation(bits, r) for r in range(bits + 1)]
        print(f"bits={bits} indispensable tests by degree={counts}")
    check_field_point(7)
    print("Equality on seven bits: one extension point covers all 128 seeds.")
