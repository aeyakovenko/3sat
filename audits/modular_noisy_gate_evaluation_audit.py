"""Exact finite audits for paired gate faults and their canonical extension."""

from fractions import Fraction
from itertools import product
from random import Random


def gf16_mul(x, y):
    """Polynomial-basis F16 with modulus x^4+x+1."""
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x & 16:
            x ^= 19
    return result


def gates(seed):
    # Gates use (left, right, truth_table). Negative parents are a fixed 0.
    # First two give a constant and a shared signal. Both feed reconvergent paths.
    rng = Random(seed)
    return [
        (-1, -1, 15 if seed & 1 else 0),
        (0, 0, rng.randrange(16)),
        (0, 1, rng.randrange(16)),
        (1, 2, rng.randrange(16)),
    ]


def table_bit(gate, values):
    left, right, table = gate
    a = values[left] if left >= 0 else 0
    b = values[right] if right >= 0 else 0
    return table >> (a + 2 * b) & 1


def logical_output(circuit, mask):
    values = []
    for g, gate in enumerate(circuit):
        values.append(table_bit(gate, values) ^ (mask >> g & 1))
    return values[-1]


def physical_output(circuit, mask):
    # Literal physical netlist: every original wire reads the trailing buffer.
    wires = []
    for g, (left, right, table) in enumerate(circuit):
        buffered_gate = (2 * left + 1, 2 * right + 1, table)
        wires.append(table_bit(buffered_gate, wires) ^ (mask >> (2 * g) & 1))
        wires.append(wires[-1] ^ (mask >> (2 * g + 1) & 1))
    return wires[-1]


def parity_mask(mask, m):
    result = 0
    for i in range(m):
        if (mask >> (2 * i) & 3) in (1, 2):
            result |= 1 << i
    return result


def field_extension(bits, points):
    """Contract the Boolean truth table by interpolation, bit 0 first."""
    layer = list(bits)
    for p in points:
        layer = [gf16_mul(a, 1 ^ p) ^ gf16_mul(b, p)
                 for a, b in zip(layer[::2], layer[1::2])]
    assert len(layer) == 1
    return layer[0]


def biased_ones(bits, n, p):
    a, b = p.numerator, p.denominator
    numerator = sum(a ** mask.bit_count() * (b - a) ** (n - mask.bit_count())
                    for mask, out in enumerate(bits) if out)
    return Fraction(numerator, b ** n)


def residue(q, modulus):
    return q.numerator * pow(q.denominator, -1, modulus) % modulus


def valuation(k, p):
    assert k > 0
    exponent = 0
    while k % p == 0:
        k //= p
        exponent += 1
    return exponent


def audit():
    counts = dict(physical_assignments=0, field_extensions=0,
                  real_core_checks=0, chain_digests=0, opposite_stretches=0)
    for seed in range(16):
        rng = Random(921 + seed)
        circuit = gates(seed)
        m = len(circuit)
        bits = [logical_output(circuit, u) for u in range(1 << m)]
        micro = [physical_output(circuit, r) for r in range(1 << (2*m))]
        for r, out in enumerate(micro):
            assert out == bits[parity_mask(r, m)]
            counts['physical_assignments'] += 1
        for points in ([(t,) * m for t in range(16)]
                       + [tuple(rng.randrange(16) for _ in circuit) for _ in range(24)]):
            diag = [p for t in points for p in (t, t)]
            assert field_extension(micro, diag) == bits[0]
            counts['field_extensions'] += 1
        for _ in range(24):
            params = [rng.randrange(16) for _ in range(2*m)]
            coarse = [a ^ b for a, b in zip(params[::2], params[1::2])]
            assert field_extension(micro, params) == field_extension(bits, coarse)
            counts['field_extensions'] += 1

        for rate in (Fraction(1, 4), Fraction(1, 3), Fraction(5, 7), Fraction(1, 2)):
            p = biased_ones(micro, 2*m, rate)
            assert p == biased_ones(bits, m, 2 * rate * (1-rate))
            counts['real_core_checks'] += 1
        core = biased_ones(micro, 2*m, Fraction(1, 4))
        assert residue(core, 3) == bits[0]
        for field, t_values in ((3, range(6)), (2, range(1, 7))):
            for t in t_values:
                if field == 3:
                    r = 2 * 3**t
                    q = Fraction(2**r-1, 2**(r+1))
                else:
                    r = 2**t
                    q = Fraction(3**r-1, 2 * 3**r)
                assert valuation(q.numerator, field) == t+1
                assert residue(biased_ones(bits, m, q), field**(t+1)) == bits[0]
                counts['chain_digests'] += 1
        positive = negative = core
        for length in range(1, 16):
            if length == 1:
                negative = 1-negative
            for _ in range(2):
                positive = Fraction(1, 4) + positive / 2
                negative = Fraction(1, 4) + negative / 2
            assert positive + negative == 1
            assert positive - negative == (2*core - 1) / 4**length
            assert abs(positive - negative) <= Fraction(1, 4**length)
            assert positive.denominator == negative.denominator == core.denominator * 4**length
            assert (residue(positive, 3), residue(negative, 3)) == (bits[0], 1-bits[0])
            counts['opposite_stretches'] += 1
    for prime in (2, 3, 5, 7, 11):
        for s, t, a, b in product(range(prime), range(prime), range(2), range(2)):
            c = (s + t - 2*s*t) % prime
            def entry(z, left, right):
                return 1-z if left == right else z
            assert sum(entry(s, a, i) * entry(t, i, b) for i in range(2)) % prime == entry(c, a, b) % prime
    # A forbidden bypass XORs the raw gate with its buffer. The output is r_1
    # even with a protected output pair; its characteristic-two diagonal varies.
    bypass = [((r & 1) ^ ((r & 1) ^ (r >> 1 & 1))) ^ (r >> 2 & 1) ^ (r >> 3 & 1)
              for r in range(16)]
    for t in range(16):
        assert field_extension(bypass, (t,t,t,t)) == t
    return counts


if __name__ == '__main__':
    print(audit())
