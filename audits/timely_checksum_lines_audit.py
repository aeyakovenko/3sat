"""Exhaustive small-field checks for the timely checksum line bound."""

from itertools import product


def multiply(x, y, modulus):
    top_bit = 1 << (modulus.bit_length() - 1)
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x & top_bit:
            x ^= modulus
    return result


def audit_every_line_erasure():
    # GF(4), a full line, degree one. By translation take the true word zero.
    field = range(4)
    modulus = 0b111
    words = []
    for slope, intercept in product(field, repeat=2):
        values = [multiply(slope, z, modulus) ^ intercept for z in field]
        nonzero_checksums = sum(
            ((t & value).bit_count() % 2) << (4 * z + t)
            for z, value in enumerate(values)
            for t in field
        )
        root_mask = sum((value == 0) << z for z, value in enumerate(values))
        words.append((nonzero_checksums, root_mask))

    tight_nontrivial = 0
    for timely in range(1 << 16):
        surviving = [roots for support, roots in words if not (support & timely)]
        count = len(surviving)
        # theta <= 1/count + (1 - 1/count) D/Q; D=1, Q=4.
        lhs = timely.bit_count() * count
        rhs = 16 + 4 * (count - 1)
        assert lhs <= rhs
        if lhs == rhs and count > 1:
            tight_nontrivial += 1
        ambiguous_anchors = 0
        for roots in surviving:
            if roots != 0b1111:
                ambiguous_anchors |= roots
        assert ambiguous_anchors.bit_count() <= count - 1
    assert tight_nontrivial > 0
    return tight_nontrivial


def audit_hidden_grid_bits():
    # GF(8), a 4x4 Boolean message, two forced zero slices per coordinate.
    modulus = 0b1011
    field = range(8)
    grid = range(4)
    remaining = list(product((2, 3), repeat=2))
    inverse = {a: next(b for b in field if multiply(a, b, modulus) == 1)
               for a in range(1, 8)}
    basis = {}
    for a, z in product(grid, field):
        value = 1
        for other in grid:
            if other != a:
                factor = multiply(z ^ other, inverse[a ^ other], modulus)
                value = multiply(value, factor, modulus)
        basis[a, z] = value

    forced = {(x, y) for x, y in product(field, repeat=2) if x < 2 or y < 2}
    assert len(forced) == 8**2 - (8 - 2)**2
    restrictions = set()
    for bits in product((0, 1), repeat=len(remaining)):
        word = {}
        for x, y in product(field, repeat=2):
            value = 0
            for bit, (a, b) in zip(bits, remaining):
                if bit:
                    value ^= multiply(basis[a, x], basis[b, y], modulus)
            word[x, y] = value
        assert all(word[z] == 0 for z in forced)
        assert tuple(word[z] for z in remaining) == bits
        restrictions.add(tuple(word[z] for z in product(grid, repeat=2)))
    assert len(restrictions) == 16
    return len(forced), len(restrictions)


if __name__ == "__main__":
    tight = audit_every_line_erasure()
    point_count, message_count = audit_hidden_grid_bits()
    print(f"65536 exact erasure patterns checked; {tight} attain equality with multiple candidates")
    print(f"{message_count} distinct messages share all checksum answers on {point_count}/64 points")
