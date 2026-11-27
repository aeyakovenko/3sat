"""Exhaust the degree-two Boolean response space for one public challenge."""

from boolean_history_catalog_audit import BinaryField, bits


def reduced_field_exponent(exponent, size):
    return 1 + (exponent - 1) % (size - 1) if exponent else 0


def orbit_gap(width):
    size = 1 << width
    remaining = {n for n in range(size) if n.bit_count() <= 2}
    maxima = []
    while remaining:
        n = min(remaining)
        orbit = set()
        while n not in orbit:
            orbit.add(n)
            n = reduced_field_exponent(2 * n, size)
        remaining.difference_update(orbit)
        maxima.append(max(orbit))
    expected = [0, size // 2]
    expected.extend(size // 2 + (1 << (width - 1 - k))
                    for k in range(width // 2, 0, -1))
    assert sorted(maxima) == expected
    gap = 1 << ((width + 1) // 2 - 1)
    assert all(y - x >= gap for x, y in zip(expected, expected[1:]))
    return gap


def check_certificate(field, slot_monomials, relation):
    slots = [[] for _ in range(1 + (relation.bit_length() - 1) // len(slot_monomials))]
    for column in bits(relation):
        index, choice = divmod(column, len(slot_monomials))
        slots[index].append(slot_monomials[choice])

    wrong = 0
    for a in range(field.size):
        word = 0
        for j, expressions in enumerate(slots):
            value = sum((a & m) == m for m in expressions) % 2
            word |= value << j
        assert field.evaluate(word, a) == 0
        wrong += bool(word)
    assert wrong >= field.size // 4
    return wrong


def first_relation(field, monic_degree=None):
    w, q = field.width, field.size
    monomials = [n for n in range(q) if n.bit_count() <= 2]
    # A row is one of the w binary coordinates of the field value at one a.
    # A column is a bit-coordinate monomial of degree at most two in one slot.
    row_masks = [sum((q - 1) << (w * a) for a in range(q) if (a & m) == m)
                 for m in monomials]
    pivots = {}
    for j in range(q):
        packed_powers = sum(field.power(a, j) << (w * a) for a in range(q))
        for i, mask in enumerate(row_masks):
            column = packed_powers & mask
            certificate = 1 << (j * len(monomials) + i)
            if j == monic_degree and i > 0:
                raise AssertionError("target monic word was unavailable")
            while column:
                leading = column.bit_length() - 1
                if leading not in pivots:
                    pivots[leading] = (column, certificate)
                    break
                other, provenance = pivots[leading]
                column ^= other
                certificate ^= provenance
            else:
                if monic_degree is None or j == monic_degree:
                    return j + 1, check_certificate(field, monomials, certificate)
    raise AssertionError("dimension upper bound supplied no dependence")


def even_width_example(field):
    w, q = field.width, field.size
    polynomial = sum(1 << (1 << (2 * i)) for i in range(w // 2))
    assert polynomial.bit_length() == q // 4 + 1
    traces = [field.evaluate(polynomial, a) for a in range(q)]
    image = set(traces)
    assert len(image) == 4
    assert all(field.power(x, 4) == x for x in image)
    flags = [int(t == 0) for t in traces]
    assert sum(flags) == q // 4
    # In-place Boolean Möbius transform converts a truth table to its ANF.
    coefficients = flags.copy()
    for i in range(w):
        for a in range(q):
            if a & (1 << i):
                coefficients[a] ^= coefficients[a ^ (1 << i)]
    assert max(a.bit_count() for a in range(q) if coefficients[a]) == 2
    assert all(field.evaluate(polynomial if flags[a] else 0, a) == 0
               for a in range(q))


if __name__ == "__main__":
    moduli = [7, 11, 19, 37, 67, 131, 285, 529]
    expected = [2, 3, 5, 8, 13, 24, 35, 70]
    for w, modulus, first in zip(range(2, 10), moduli, expected):
        field = BinaryField(w, modulus)
        gap = orbit_gap(w)
        length, wrong = first_relation(field)
        assert gap < length == first
        if wrong == field.size:
            everywhere = length
        else:
            everywhere, count = first_relation(field, monic_degree=w)
            assert field.minimal_polynomial(2).bit_length() == w + 1
            assert everywhere == w + 1 and count == field.size
        if w % 2 == 0:
            even_width_example(field)
            assert length <= field.size // 4 + 1
        print(f"w={w}: guaranteed injective through {gap}, first kernel at {length},"
              f" recovered false word on {wrong}/{field.size} challenges; first everywhere false at {everywhere}")
