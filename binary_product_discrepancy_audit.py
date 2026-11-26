"""Audit signed rank-term selection for the exact graph of binary multiplication.

All matrices are packed in row-major order. Modulus zero denotes integer
arithmetic before the final rational Walsh normalization.
"""

from fractions import Fraction
from functools import cache
from itertools import product
from random import Random

from three_bank_matrix_rank_audit import multiply


# Coefficients of the left, right and Frobenius-test forms for the seven
# Strassen products. A four-bit mask selects blocks 00, 01, 10, 11.
STRASSEN = ((9, 9, 9), (12, 1, 12), (1, 10, 10), (8, 5, 5),
            (3, 8, 3), (5, 3, 8), (10, 12, 1))
FIELDS = (0, 3, 5)


def form_table(matrix, inner, bank):
    """Return seven packed inner matrices, one for each block-grid form."""
    side = 2 * inner
    blocks = []
    for block_row, block_col in product(range(2), repeat=2):
        block = 0
        for i, j in product(range(inner), repeat=2):
            pos = (block_row * inner + i) * side + block_col * inner + j
            block |= ((matrix >> pos) & 1) << (i * inner + j)
        blocks.append(block)
    table = []
    for factors in STRASSEN:
        value = 0
        for index, block in enumerate(blocks):
            if factors[bank] & (1 << index):
                value ^= block
        table.append(value)
    return table


def active_terms(left, right, test, inner):
    """Bit ℓ·m³+i·m²+j·m+k is Aℓ[i,j] Bℓ[j,k] Zℓ[i,k]."""
    mask = 0
    for ell, (a, b, z) in enumerate(zip(left, right, test)):
        for i, j, k in product(range(inner), repeat=3):
            bit = (a >> (i * inner + j)) & (b >> (j * inner + k)) & (z >> (i * inner + k)) & 1
            mask |= bit << (((ell * inner + i) * inner + j) * inner + k)
    return mask


def selection_coefficients(pos, neg, bound, prime):
    """Count canonical selections of each degree up to 2·bound.

    Each positive or dummy label occurs at most once. A negative label can
    repeat. Its signed series has coefficients 1,-1,1,... .
    """
    assert abs(pos - neg) <= bound
    coeff = [1] + [0] * (2 * bound)
    for _ in range(bound + pos):
        for j in range(len(coeff) - 1, 0, -1):
            coeff[j] += coeff[j - 1]
            if prime:
                coeff[j] %= prime
    for _ in range(neg):
        for j in range(1, len(coeff)):
            coeff[j] -= coeff[j - 1]
            if prime:
                coeff[j] %= prime
    return coeff


@cache
def signed_contraction(pos, neg, bound, prime):
    coeff = selection_coefficients(pos, neg, bound, prime)
    signed = (-1) ** bound * sum(c * (-2) ** j for j, c in enumerate(coeff))
    return signed % prime if prime else signed


def enumerated_selections(active, minus, bound, rank):
    """Independently sum the actual sorted label words, with one empty suffix."""
    labels = [x for x in range(rank) if active & (1 << x)] + list(range(rank, rank + bound))

    def visit(lower, slots):
        total = 1  # Stop now; the remaining slots are inactive.
        if slots:
            for j in range(lower, len(labels)):
                repeat = bool(minus & (1 << labels[j]))
                factor = 2 if repeat else -2
                total += factor * visit(j if repeat else j + 1, slots - 1)
        return total

    return (-1) ** bound * visit(0, 2 * bound)


def phases(active, minus, bound):
    pos = (active & ~minus).bit_count()
    neg = (active & minus).bit_count()
    return tuple(signed_contraction(pos, neg, bound, p) for p in FIELDS)


def walsh_graph(signals, expected_matrix, prime):
    """Invert the Z-bank Walsh transform and check every open C value."""
    values = list(signals)
    stride = 1
    while stride < len(values):
        for start in range(0, len(values), 2 * stride):
            for i in range(start, start + stride):
                x, y = values[i], values[i + stride]
                values[i], values[i + stride] = x + y, x - y
        stride *= 2
    if prime:
        normalizer = pow(len(values), -1, prime)
    for c, value in enumerate(values):
        actual = value * normalizer % prime if prime else Fraction(value, len(values))
        assert actual == int(c == expected_matrix)


def audit_two():
    probes = [[form_table(a, 1, bank) for a in range(16)] for bank in range(3)]
    support = {}
    for a, b, z in product(range(16), repeat=3):
        mask = active_terms(probes[0][a], probes[1][b], probes[2][z], 1)
        assert mask.bit_count() % 2 == (multiply(a, b, 2) & z).bit_count() % 2
        support[a, b, z] = mask
    patterns = set(support.values())
    # Exhaust all fixed signings to get a genuinely nontrivial finite bound.
    bound, minus = min((max(abs(mask.bit_count() - 2 * (mask & signs).bit_count())
                             for mask in patterns), signs) for signs in range(128))
    for mask in patterns:
        direct = enumerated_selections(mask, minus, bound, 7)
        assert direct == (-1) ** (mask.bit_count() % 2)
        assert phases(mask, minus, bound) == tuple(direct % p if p else direct for p in FIELDS)
    for a, b in product(range(16), repeat=2):
        values = [phases(support[a, b, z], minus, bound) for z in range(16)]
        for field, signal in zip(FIELDS, zip(*values)):
            walsh_graph(signal, multiply(a, b, 2), field)
    return bound


def audit_four():
    rng = Random(24092026)
    rank = 7 * 2**3
    # In the tiny example the universal counting bound for balanced signs
    # is stronger than the asymptotic concentration estimate.
    minus = sum(1 << i for i in rng.sample(range(rank), rank // 2))
    bound = rank // 2
    elementary = [1 << bit for bit in range(16)]
    cases = list(product(elementary, repeat=3))
    cases += [(rng.getrandbits(16), rng.getrandbits(16), rng.getrandbits(16)) for _ in range(320)]
    cases += list(product((0, 0xffff, 0x8421, 0x1248), repeat=3))
    for a, b, z in cases:
        mask = active_terms(form_table(a, 2, 0), form_table(b, 2, 1), form_table(z, 2, 2), 2)
        bit = (multiply(a, b, 4) & z).bit_count() % 2
        assert mask.bit_count() % 2 == bit
        sign = (-1) ** bit
        assert phases(mask, minus, bound) == tuple(sign % p if p else sign for p in FIELDS)

    # For one dense pair contract all 65,536 test masks, then invert the
    # actual resulting signal. Each active primitive is linear in Z at fixed A,B.
    a, b = 0x5b3e, 0xda79
    left, right = form_table(a, 2, 0), form_table(b, 2, 1)
    basis = [active_terms(left, right, form_table(z, 2, 2), 2) for z in elementary]
    signals = [[0] * (1 << 16) for _ in FIELDS]
    mask = prev = 0
    for step in range(1 << 16):
        z = step ^ (step >> 1)
        if step:
            mask ^= basis[(prev ^ z).bit_length() - 1]
        for signal, value in zip(signals, phases(mask, minus, bound)):
            signal[z] = value
        prev = z
    for p, signal in zip(FIELDS, signals):
        walsh_graph(signal, multiply(a, b, 4), p)
    return len(cases)


def audit_sign_blocks():
    # Each affine seed yields four signs. Enumerate two independent blocks
    # and all masks to verify the first two moments used in the signing proof.
    outcomes = []
    for slope, offset in product(range(4), range(2)):
        outcomes.append(tuple((-1) ** (((slope & u).bit_count() + offset) % 2) for u in range(4)))
    pairs = [left + right for left, right in product(outcomes, repeat=2)]
    for mask in range(256):
        scores = [sum(x for i, x in enumerate(row) if mask & (1 << i)) for row in pairs]
        assert sum(scores) == 0
        assert sum(x*x for x in scores) == len(pairs) * mask.bit_count()


def cyclic_expansion(residue, multiplier, prime):
    """Evaluate the truncated selection polynomial at u-1, with u³=1."""
    # residue ≤ 2 and multiplier is 1 or -2; four bounds both signed lifts.
    bound = 4
    pos = max(multiplier, 0) * residue
    neg = max(-multiplier, 0) * residue
    coefficients = selection_coefficients(pos, neg, bound, prime)
    ring_element = [0, 0, 0]
    for coefficient in reversed(coefficients):
        ring_element = [ring_element[(j - 1) % 3] - ring_element[j] for j in range(3)]
        ring_element[0] += coefficient
        if prime:
            ring_element = [v % prime for v in ring_element]
    # Multiplication by u^(-bound) undoes the shift in the exponent.
    return [ring_element[(j + bound) % 3] for j in range(3)]


def audit_ternary_scalar():
    for prime, multiplier, a, b, c in product((0, 2, 5), (1, -2),
                                              range(3), range(3), range(3)):
        total = 0
        for z in range(3):
            residue = (a * b * z) % 3
            phase = cyclic_expansion(residue, multiplier, prime)
            assert phase == [int(i == residue) for i in range(3)]
            # Multiply by u^(-cz), then apply the functional [u^0] - [u^1].
            total += phase[(c * z) % 3] - phase[(1 + c * z) % 3]
        actual = total * pow(3, -1, prime) % prime if prime else Fraction(total, 3)
        assert actual == int((a * b) % 3 == c)


if __name__ == "__main__":
    audit_sign_blocks()
    bound = audit_two()
    samples = audit_four()
    audit_ternary_scalar()
    print(f"2x2: all 4,096 triples, all 128 signings, best signed bound {bound}.")
    print(f"4x4: {samples:,} mixed-grid triples and one complete 65,536-column graph slice.")
    print("Sorted selections, affine-block moments, and graph inversion over Q, F3, F5 passed.")
    print("F3 scalar inputs: all 81 quadruples, both signed lifts, and cyclic inversion over Q, F2, F5 passed.")
