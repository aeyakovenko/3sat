"""Check conditional seed counts, model recovery and one-bit queries on small files."""

from functools import cache
from itertools import combinations, product


def multiply(a, b, modulus):
    degree = modulus.bit_length() - 1
    value = 0
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        if a >> degree:
            a ^= modulus
        b >>= 1
    return value


def hash_value(name, seed, modulus):
    width = modulus.bit_length() - 1
    mask = (1 << width) - 1
    a, b, c = seed >> (2 * width), (seed >> width) & mask, seed & mask
    return multiply(multiply(a, name, modulus) ^ b, name, modulus) ^ c


@cache
def bit_forms(name, modulus):
    width = modulus.bit_length() - 1
    basis = [hash_value(name, 1 << i, modulus) for i in range(3 * width)]
    return tuple(sum(((value >> j) & 1) << i for i, value in enumerate(basis))
                 for j in reversed(range(width)))


def comparison_cases(head, other, modulus):
    equal_prefix = []
    for u, v in zip(bit_forms(head, modulus), bit_forms(other, modulus)):
        yield equal_prefix + [(u, 1), (v, 0)]
        equal_prefix.append((u ^ v, 0))
    if head > other:
        yield equal_prefix


def solution_count(equations, nbits):
    basis = {}
    for mask, rhs in equations:
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = mask, rhs
                break
            row, value = basis[pivot]
            mask ^= row
            rhs ^= value
        else:
            if rhs:
                return 0
    return 1 << (nbits - len(basis))


@cache
def hit_count(triple, modulus, length, prefix):
    head, left, right = triple
    nbits = 3 * (modulus.bit_length() - 1)
    pins = [(1 << i, (prefix >> i) & 1) for i in range(length)]
    return sum(solution_count(pins + u + v, nbits)
               for u, v in product(comparison_cases(head, left, modulus),
                                   comparison_cases(head, right, modulus)))


@cache
def canonical_seed(triples, modulus):
    seed = 0
    for i in range(3 * (modulus.bit_length() - 1)):
        candidates = seed, seed | (1 << i)
        scores = [sum(hit_count(t, modulus, i + 1, k) for t in triples)
                  for k in candidates]
        seed = candidates[scores[1] > scores[0]]
    return seed


def test_linear_counts():
    # All seed prefixes over GF(4), all designated heads on distinct triples.
    modulus = 0b111
    cases = 0
    for names in combinations(range(4), 3):
        for head in names:
            tails = sorted(set(names) - {head})
            triple = (head, *tails)
            good = [seed for seed in range(64) if head == max(
                names, key=lambda u: (hash_value(u, seed, modulus), u))]
            for length in range(7):
                for prefix in range(1 << length):
                    expected = sum(seed % (1 << length) == prefix for seed in good)
                    assert hit_count(triple, modulus, length, prefix) == expected
                    cases += 1
    return cases


def ppz(forbidden, order, *, model=None, tape=None):
    # Each full proper clause on these three names forbids its indexed assignment.
    prefix = mask = 0
    bits = []
    for u in order:
        possible = [z for z in (0, 1) if not any(
            (mask | 1 << u) == 7 and (prefix | z << u) == f for f in forbidden)]
        assert possible
        if len(possible) == 1:
            bit, = possible
        else:
            bit = (model >> u) & 1 if model is not None else tape[len(bits)]
            bits.append(bit)
        prefix |= bit << u
        mask |= 1 << u
    return prefix, tuple(bits)


def test_formula_codes():
    modulus = 0b1000011  # x^6 + x + 1, for v=3 and ceil(log2(48))=6
    model_count = singleton_count = 0
    for clause_mask in range(256):
        forbidden = {k for k in range(8) if clause_mask >> k & 1}
        model_codes = {}
        for model in sorted(set(range(8)) - forbidden):
            heads = [u for u in range(3) if (model ^ (1 << u)) in forbidden]
            triples = tuple((u, *(v for v in range(3) if v != u)) for u in heads)
            seed = canonical_seed(triples, modulus)
            order = sorted(range(3), key=lambda u: (hash_value(u, seed, modulus), u))
            recovered, guesses = ppz(forbidden, order, model=model)
            assert recovered == model
            assert len(guesses) <= 3 - (len(heads) + 2) // 3
            padded = guesses + (0,) * (3 - len(guesses))
            assert ppz(forbidden, order, tape=padded)[0] == model
            code = tuple((seed >> i) & 1 for i in range(18)) + padded
            assert code not in model_codes
            model_codes[code] = model
            model_count += 1
        if len(model_codes) == 1:
            code, = model_codes
            # At j0=3 the last guess position is omitted.
            code = code[:-1]
            for i, bit in enumerate(code):
                center = bytearray(b'0' * len(code))
                query = center.copy()
                query[i] = ord('1')
                assert sum((a ^ b).bit_count() for a, b in zip(center, query)) == 1
                assert all(d == ord('0') or not c for c, d in zip(code, query)) == (bit == 0)
            singleton_count += 1
    return model_count, singleton_count


if __name__ == '__main__':
    print('Conditional comparison counts:', test_linear_counts())
    print('Formula/model pairs and uniquely satisfiable formulas:', test_formula_codes())
