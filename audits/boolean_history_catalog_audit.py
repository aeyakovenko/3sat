"""Check the trace catalog for binary-payload polynomial fingerprints."""

from collections import Counter
from functools import reduce
from itertools import combinations_with_replacement, product
from math import comb
from operator import xor
from random import Random


def bits(mask):
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length() - 1
        mask ^= lowest


def polynomial_product(a, b):
    return reduce(xor, (b << i for i in bits(a)), 0)


def remainder(a, modulus):
    while a.bit_length() >= modulus.bit_length():
        a ^= modulus << (a.bit_length() - modulus.bit_length())
    return a


class BinaryField:
    def __init__(self, width, modulus):
        self.width = width
        self.size = 1 << width
        self.modulus = modulus
        assert modulus.bit_length() == width + 1
        # The chosen element X must generate the entire nonzero field.
        self.log = [-1] * self.size
        self.exp = []
        element = 1
        for i in range(self.size - 1):
            assert self.log[element] == -1 and element
            self.exp.append(element)
            self.log[element] = i
            element = remainder(element << 1, modulus)
        assert element == 1

    def multiply(self, a, b):
        return self.exp[(self.log[a] + self.log[b]) % (self.size - 1)] if a and b else 0

    def power(self, a, n):
        if not n:
            return 1
        return self.exp[(self.log[a] * n) % (self.size - 1)] if a else 0

    def evaluate(self, binary_poly, a):
        return reduce(xor, (self.power(a, i) for i in bits(binary_poly)), 0)

    def minimal_polynomial(self, a):
        orbit = [a]
        b = self.multiply(a, a)
        while b != a:
            orbit.append(b)
            b = self.multiply(b, b)
        coeff = [1]
        for root in orbit:
            scaled = [self.multiply(root, c) for c in coeff] + [0]
            coeff = [v ^ w for v, w in zip(scaled, [0] + coeff)]
        assert set(coeff) <= {0, 1}
        return sum(c << i for i, c in enumerate(coeff))


def compose(outer, inner):
    value = 0
    for i in reversed(range(outer.bit_length())):
        value = polynomial_product(inner, value) ^ ((outer >> i) & 1)
    return value


def hasse(poly, order):
    # Lucas' theorem in characteristic two.
    return sum(1 << (i - order) for i in bits(poly) if i & order == order)


def build_catalog(s, d, field, exhaustive):
    rng = Random(100 * s + d)
    q = field.size
    Q = 1 << (2 * s)
    D = d * s * Q
    T = 5 * D
    L = (1 << 1) | (1 << (1 << s)) | (1 << Q)
    trace = [a ^ field.power(a, 1 << s) ^ field.power(a, Q) for a in range(q)]
    traces = Counter(trace)
    assert len(traces) == 1 << s and set(traces.values()) == {Q}
    orbit_of = {g: field.minimal_polynomial(g) for g in traces}
    classes = [orbit_of[g] for g in trace]
    orbits = sorted(set(classes))
    K = 2 + ((1 << s) - 2) // s
    assert len(orbits) == K
    assert Counter(classes) == {p: Q * (p.bit_length() - 1) for p in orbits}
    mask = int("".join("0" if j % 3 == 0 else "1" for j in reversed(range(4 * D))), 2)

    words = {}
    aliases = {}
    evals = range(q) if exhaustive else sorted({0, 1, *(rng.randrange(q) for _ in range(15))})
    for selected in combinations_with_replacement(orbits, d):
        M = reduce(polynomial_product, selected, 1)
        P = compose(M, L)
        assert P.bit_length() - 1 <= D
        assert P.bit_count() <= 4 ** ((s * d).bit_length())
        assert remainder(P, 0b111)  # no root at a primitive cube root
        word = polynomial_product(P, mask)
        assert word.bit_length() <= T
        center = (word >> D) & ((1 << (3 * D)) - 1)
        assert center.bit_count() == 2 * D and word.bit_count() >= 2 * D
        assert word not in aliases
        aliases[word] = selected
        words[selected] = word

        derivatives = [hasse(P, order) for order in range(d + 1)]
        for a in evals:
            m = selected.count(classes[a])
            assert field.evaluate(P, a) == field.evaluate(M, trace[a])
            for order in range(m):
                assert field.evaluate(derivatives[order], a) == 0
            assert field.evaluate(derivatives[m], a) != 0
        for j in [D, 4 * D - 1] + [rng.randrange(T) for _ in range(12)]:
            coins = (0 <= j - i < 4 * D and (j - i) % 3 != 0 for i in bits(P))
            assert sum(coins) % 2 == ((word >> j) & 1)
    assert len(words) == comb(K + d - 1, d)

    # Evaluate each returned whole binary word at its distinct field root classes.
    # At nonzero field points exponents may first be reduced modulo q-1.
    def evaluate_word(word, a):
        if not a:
            return word & 1
        return field.evaluate(remainder(word, (1 << (q - 1)) | 1), a)

    if exhaustive:
        coverage = {k: [a for a in range(q) if classes[a] in k] for k in words}
        for k, roots in coverage.items():
            assert all(evaluate_word(words[k], a) == 0 for a in roots)
        for points in product(range(q), repeat=d):
            key = tuple(sorted(classes[a] for a in points))
            assert key in words
    else:
        for _ in range(120):
            points = [rng.randrange(q) for _ in range(d)]
            key = tuple(sorted(classes[a] for a in points))
            assert all(evaluate_word(words[key], a) == 0 for a in points)
    print(f"s={s}, d={d}, T={T}, orbits={K}, {len(words)} distinct words,"
          f" {2*D} interior ones per word")


def probe_audit(field, h):
    # s=3, d=1, m=4. Every possible restriction of h *physical* bit probes
    # is represented by its tuple of linear signatures on the four-bit mask.
    s, m = 3, 4
    small = BinaryField(m, 0b10011)
    D = s * (1 << (2 * s))
    B = (6 * h + 6) * D
    T = B + D
    omega = 2
    L = (1 << 1) | (1 << (1 << s)) | (1 << (1 << (2 * s)))
    trace_small = [
        reduce(xor, (small.power(x, 1 << i) for i in range(m)), 0)
        for x in range(small.size)
    ]
    assert set(trace_small) == {0, 1}
    trace_values = {a ^ field.power(a, 1 << s) ^ field.power(a, 1 << (2*s))
                    for a in range(field.size)}
    factors = {field.minimal_polynomial(g) for g in trace_values}
    tested = 0
    for factor in factors:
        P = compose(factor, L)
        inverse = small.power(omega, small.size - 2)
        multiplier = small.evaluate(P, inverse)
        assert multiplier
        words = [0]
        for lam in range(1, small.size):
            mask_bits = (
                trace_small[small.multiply(lam, small.power(omega, j))]
                for j in reversed(range(B))
            )
            mask = int(''.join(map(str, mask_bits)), 2)
            word = polynomial_product(P, mask)
            assert word.bit_length() <= T
            center = (word >> D) & ((1 << (B-D))-1)
            assert 2 * center.bit_count() >= B-2*D
            phase = small.multiply(lam, multiplier)
            for j in range(D, D + small.size - 1):
                assert (word >> j) & 1 == trace_small[small.multiply(phase, small.power(omega, j))]
            words.append(word)
        basis = [words[1 << i] for i in range(m)]
        for lam, word in enumerate(words):
            assert word == reduce(xor, (basis[i] for i in bits(lam)), 0)
        representatives = {}
        for j in range(T):
            signature = sum(((b >> j) & 1) << i for i, b in enumerate(basis))
            representatives.setdefault(signature, j)
        for patterns in combinations_with_replacement(representatives, h):
            pins = [representatives[sig] for sig in patterns]
            choices = [lam for lam in range(1, small.size)
                       if all(not ((words[lam] >> j) & 1) for j in pins)]
            assert len(choices) >= (1 << (m-h))-1
            tested += 1
    print(f"GF(16) masks, h={h}, {tested} physical probe signatures;"
          f" all admit nonzero masks having at least {(B-2*D)//2} ones")


def affine_audit(field):
    w, q = field.width, field.size
    trace = [reduce(xor, (field.power(x, 1 << i) for i in range(w)), 0) for x in range(q)]
    assert set(trace) == {0, 1}
    for T in (q // 2, q // 2 + 1):
        # Bit columns in the linear map of all affine coordinate coefficients to
        # the concatenated q field fingerprints. Row reduction is over F2.
        pivots = {}
        for j in range(T):
            for c in [None] + [1 << i for i in range(w)]:
                column = 0
                for a in range(q):
                    bit = 1 if c is None else trace[field.multiply(c, a)]
                    column |= (bit * field.power(a, j)) << (w * a)
                while column:
                    pivot = column.bit_length() - 1
                    if pivot not in pivots:
                        pivots[pivot] = column
                        break
                    column ^= pivots[pivot]
        nullity = T * (w + 1) - len(pivots)
        assert (nullity == 0) == (T == q // 2)
        print(f"affine columns over F{q}, T={T}, kernel dimension {nullity}")
    for a in range(q):
        word = sum(1 << (1 << i) for i in range(w)) | trace[a]
        assert word and field.evaluate(word, a) == 0


if __name__ == "__main__":
    field9 = BinaryField(9, (1 << 9) | (1 << 4) | 1)
    field15 = BinaryField(15, (1 << 15) | (1 << 1) | 1)
    for d in (1, 2):
        build_catalog(3, d, field9, exhaustive=True)
        build_catalog(5, d, field15, exhaustive=False)
    for h in (2, 3):
        probe_audit(field9, h)
    affine_audit(BinaryField(3, 0b1011))
    affine_audit(BinaryField(4, 0b10011))
