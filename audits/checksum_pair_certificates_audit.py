"""Exhaust binary line certificates over F4 and tiny pairwise-hash samplers."""
from fractions import Fraction
from itertools import product
from random import Random


def mul(a, b):
    t = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
    return t ^ (7 if t & 4 else 0)


def tr(a):
    return a ^ mul(a, a)


def line_row(t, u, lam, mu, degree):
    # The constant is a single bit. The other field coefficients are free.
    bits = [tr(lam ^ mu)]
    a, b = t, u
    for _ in range(degree):
        bits.extend((tr(mul(lam, mul(a, basis))) for basis in (1, 2)))
        bits.extend((tr(mul(mu, mul(b, basis))) for basis in (1, 2)))
        a, b = mul(a, t), mul(b, u)
    return sum(bit << i for i, bit in enumerate(bits))


def combination_for_constant(rows):
    pivots = {}
    for i, row in enumerate(rows):
        mask = 1 << i
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row, mask
                break
            value, witness = pivots[p]
            row ^= value
            mask ^= witness
    return pivots.get(0, (0, 0))[1]


def test_lines():
    rng = Random(34)
    checked = 0
    for degree in (1, 2):
        rows = [line_row(t, u, lam, mu, degree)
                for t, u in product(range(1, 4), repeat=2)
                for lam, mu in product(range(4), repeat=2)]
        threshold = Fraction(1 + Fraction(degree, 3)**2, 2)
        # Exact largest agreement with a pair of different common constants.
        maximum = max(sum((r & d).bit_count() % 2 == 0 for r in rows)
                      for d in range(1, 1 << (4 * degree + 1), 2))
        assert Fraction(maximum, len(rows)) == threshold
        for _ in range(64):
            sample = rng.sample(rows, maximum + 1)
            combination = combination_for_constant(sample)
            assert combination.bit_count() <= 4 * degree + 1
            combined = 0
            for i, row in enumerate(sample):
                if combination & (1 << i):
                    combined ^= row
            assert combined == 1
            for coeff in range(1 << (4 * degree + 1)):
                assert (combined & coeff) == (coeff & 1)
            checked += 1
    return checked


def exact_hash_advantage(samples, truth, bucket_bits):
    # All Toeplitz seeds and offsets, with empty matrix if no bucket bits.
    r = (len(samples) - 1).bit_length()
    matrices = 1 << max(0, r + bucket_bits - 1) if bucket_bits else 1
    buckets = 1 << bucket_bits
    signed = 0
    for matrix, offset in product(range(matrices), range(buckets)):
        seen = [set() for _ in truth]
        for seed, (point, label) in enumerate(samples):
            image = offset
            for i in range(bucket_bits):
                image ^= (((matrix >> i) & seed).bit_count() & 1) << i
            if image == 0:
                seen[point].add(label)
        for point, labels in enumerate(seen):
            signed += int(truth[point] in labels) - int((1 ^ truth[point]) in labels)
    return Fraction(signed, 2 * len(truth) * matrices * buckets)


def test_isolation():
    rng = Random(53)
    checked = 0
    for _ in range(256):
        n, r = 4, 8
        truth = [rng.randrange(2) for _ in range(n)]
        samples = [(rng.randrange(n), rng.randrange(2)) for _ in range(r)]
        gamma = Fraction(sum(truth[z] == b for z, b in samples), r) - Fraction(1, 2)
        if gamma <= 0:
            continue
        counts = [sum(z == u for z, _ in samples) for u in range(n)]
        kappa = Fraction(n * sum(x*x for x in counts), r*r)
        bits = 0
        while Fraction(r, n << bits) > 2 * gamma / kappa:
            bits += 1
        alpha = Fraction(r, n << bits)
        adv = exact_hash_advantage(samples, truth, bits)
        assert adv >= alpha*gamma - alpha*alpha*kappa/4 >= gamma*gamma/(2*kappa)
        checked += 1
    return checked


if __name__ == "__main__":
    print(f"{test_lines()} dense pair samples with ≤2ds+1 witnessed rows and sharp line thresholds")
    print(f"{test_isolation()} biased samplers checked under all chosen Toeplitz hashes and offsets")
