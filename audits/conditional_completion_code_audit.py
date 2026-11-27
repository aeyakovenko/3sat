"""Check translated input laws, RS completion queries, and a nonlocal native query."""

from collections import Counter
from itertools import combinations, product


def mul(a, b, modulus=0b1011):
    high = 1 << (modulus.bit_length() - 1)
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & high:
            a ^= modulus
        b >>= 1
    return result


def translated_laws():
    field = range(4)
    code = [tuple(a ^ mul(b, i, 0b111) for i in field) for a, b in product(field, repeat=2)]
    rows = [x + y for x, y in product(code, product(field, repeat=4))]
    pairs = list(combinations(range(8), 2))
    comparisons = 0
    for i, j in pairs:
        counts = Counter((r[i], r[j]) for r in rows)
        for a, b in product(field, repeat=2):
            assert all(counts[x ^ a, y ^ b] == len(rows) // 16 for x, y in product(field, repeat=2))
            comparisons += 1
    differences = Counter(tuple(x ^ y for x, y in zip(r[:4], r[4:])) for r in rows)
    assert len(differences) == 256 and set(differences.values()) == {16}
    return comparisons


def evaluate(coeffs, a):
    value = 0
    for coeff in reversed(coeffs):
        value = mul(a, value) ^ coeff
    return value


def completed_calls(code):
    zero = (0,) * 8
    offsets = [zero, code[18], tuple((3 * i + 2) % 8 for i in range(8))]
    replacements = [zero, code[21], tuple((5 * i + 1) % 8 for i in range(8))]
    code_set = set(code)
    checked = 0
    for mask in range(256):
        t = [i for i in range(8) if mask & (1 << i)]
        kept = [i for i in range(8) if not mask & (1 << i)]
        for e, v in product(offsets, replacements):
            known, free, values = (kept, t, e) if len(kept) >= 2 else (t, kept, v)
            compatible = [word for word in code if all(word[i] == values[i] for i in known)]
            assert len(compatible) <= 1
            for x in code:
                actual = tuple(v[i] if i in t else x[i] ^ e[i] for i in range(8)) in code_set
                if not compatible:
                    predicted = False
                else:
                    other = v if len(kept) >= 2 else e
                    predicted = all(x[i] == compatible[0][i] ^ other[i] for i in free)
                assert actual == predicted
                checked += 1
    return checked


def frobenius(value, times):
    for _ in range(times % 3):
        value = mul(value, value)
    return value


def trace(value):
    result = value ^ frobenius(value, 1) ^ frobenius(value, 2)
    assert result in (0, 1)
    return result


def trace_queries(code):
    code_set = set(code)
    checked = 0
    for (a0, a1), word in zip(product(range(8), repeat=2), code):
        for j, coeff in enumerate((a0, a1)):
            # For the lower coefficient we have already recovered the higher one.
            remaining = (a0,) if j == 0 else (a0, a1)
            known = tuple(evaluate(remaining, a) for a in range(8))
            for beta in range(1, 8):
                transformed = []
                for a in range(8):
                    value = 0
                    for r in range(3):
                        value ^= mul(frobenius(beta, r), frobenius(known[frobenius(a, -r)], r))
                    multiplier = mul(a, a) if j == 0 else a
                    transformed.append(mul(multiplier, value))
                assert (tuple(transformed) not in code_set) == bool(trace(mul(beta, coeff)))
                checked += 1
        assert word == tuple(evaluate((a0, a1), a) for a in range(8))
    return checked


if __name__ == '__main__':
    rs_code = [tuple(evaluate(coeffs, a) for a in range(8)) for coeffs in product(range(8), repeat=2)]
    print(f'{translated_laws()} translated two-symbol marginals checked over GF(4)')
    print(f'{completed_calls(rs_code)} adaptive-oracle building blocks checked over GF(8)')
    print(f'{trace_queries(rs_code)} transformed coefficient-bit decisions checked over GF(8)')
