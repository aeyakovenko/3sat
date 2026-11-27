"""Finite checks of the edit span and purely inseparable coefficient arguments."""

from itertools import product


def matrix(d, positions):
    return sum(1 << (i * d + j) for i, j in positions)


def multiply(d, left, right):
    out = 0
    row_mask = (1 << d) - 1
    for i, h in product(range(d), repeat=2):
        if (left >> (i * d + h)) & 1:
            out ^= ((right >> (h * d)) & row_mask) << (i * d)
    return out


def small_edits(d):
    identity = matrix(d, ((i, i) for i in range(d)))
    transvections = [identity ^ matrix(d, [(i, j)]) for i, j in product(range(d), repeat=2)
                     if i != j]
    elementary = [identity, *transvections]
    return sorted({multiply(d, p, q) for p, q in product(elementary, repeat=2)})


def independent(words):
    pivots = {}
    basis = []
    for word in words:
        value = word
        while value:
            k = value.bit_length() - 1
            if k not in pivots:
                pivots[k] = value
                basis.append(word)
                break
            value ^= pivots[k]
    return basis


def coefficients(d, p, q, r):
    bits = []
    for i, a, b, k, c, j in product(range(d), repeat=6):
        if p >> (i * d + a) & q >> (b * d + k) & r >> (c * d + j) & 1:
            bits.append(1 << (((a * d + b) * d * d + k * d + c) * d * d + i * d + j))
    return sum(bits)


def edit_span(d):
    edits = small_edits(d)
    basis = independent(edits)
    assert len(basis) == d ** 2
    # At side two test every short edit. At side three all triples of a
    # selected basis of actual edits already attain full row rank.
    triples = list(product(edits if d == 2 else basis, repeat=3))
    rows = [coefficients(d, *triple) for triple in triples]
    assert len(independent(rows)) == d ** 6
    if d == 2:
        for score, (p, q, r) in zip(rows, triples):
            for a, b, z in product(range(d * d), repeat=3):
                left = multiply(d, multiply(d, p, 1 << a), q)
                right = multiply(d, 1 << b, r)
                direct = multiply(d, left, right) >> z & 1
                shift = (a * d * d + b) * d * d + z
                assert (score >> shift & 1) == direct
    print(f"side {d}: {len(edits)} short edits, {len(rows)} coefficient rows, "
          f"binary rank {d ** 6}")


def primitive_generators(n, q):
    def residues(exponents):
        base, *others = exponents
        result = []
        for bank in range(3):
            part = others[bank * (n - 1):(bank + 1) * (n - 1)]
            result.extend([(base - sum(part)) % q, *part])
        return tuple(result)
    dimension = 3 * n - 2
    recorded = {residues(xs) for xs in product(range(q), repeat=dimension)}
    assert len(recorded) == q ** dimension
    for i, j, k in product(range(n), repeat=3):
        value = tuple(int(pos == chosen) for chosen in (i, j, k) for pos in range(n))
        assert value in recorded
    return len(recorded)


def main():
    edit_span(2)
    edit_span(3)
    count = sum(primitive_generators(n, q) for n, q in [(1, 2), (2, 4), (3, 2), (4, 2)])
    print(f"{count} distinct residue vectors checked across field-generator tests")


if __name__ == "__main__":
    main()
