"""Finite checks for trace-selector rigidity, including complete alternative searches."""

from collections import Counter
from fractions import Fraction
from itertools import product
from random import Random


class BinaryField:
    def __init__(self, size, modulus):
        self.q = size
        self.s = size.bit_length() - 1

        def multiply(x, y):
            z = 0
            while y:
                if y & 1:
                    z ^= x
                y >>= 1
                x <<= 1
                if x & size:
                    x ^= modulus
            return z

        self.mul = [[multiply(x, y) for y in range(size)] for x in range(size)]
        self.inv = [0] + [self.mul[x].index(1) for x in range(1, size)]
        self.trace = []
        for x in range(size):
            y, acc = x, 0
            for _ in range(self.s):
                acc ^= y
                y = self.mul[y][y]
            assert acc in (0, 1) and y == x
            self.trace.append(acc)
        self.dual = [sum(self.trace[self.mul[x][1 << i]] << i
                         for i in range(self.s)) for x in range(size)]
        assert len(set(self.dual)) == size

    def factors(self, p):
        row = [1]
        for x in p:
            row = [self.mul[1 ^ x][a] for a in row] + [self.mul[x][a] for a in row]
        return row

    def word(self, p, mask):
        return sum(self.trace[self.mul[mask][x]] << i
                   for i, x in enumerate(self.factors(p)))

    def square(self, x):
        return self.mul[x][x]

    def from_odds(self, r):
        return self.mul[r][self.inv[r ^ 1]]


def span_size(forms):
    span = {0}
    for z in forms:
        span |= {u ^ z for u in span}
    return len(span)


def orbit_size(field, point, mask):
    labels = tuple(point) + (mask,)
    acc = set()
    while labels not in acc:
        acc.add(labels)
        labels = tuple(map(field.square, labels))
    return len(acc)


def exhaustive_orbits(field, group_size):
    # Two groups spanning the field plus one field-generating coordinate
    # suffice for exact (noise-free) rigidity via their trace pairings.
    d = 2*group_size + 1
    counts = Counter()
    held = []
    for point in product(range(field.q), repeat=d):
        row = field.factors(point)
        columns = [sum(field.trace[field.mul[1 << l][z]] << i
                       for i, z in enumerate(row)) for l in range(field.s)]
        words = [0]
        for column in columns:
            words += [word ^ column for word in words]
        counts.update(words)
        interior = all(z >= 2 for z in point)
        if interior and (span_size(field.factors(point[:group_size])) == field.q
                         and span_size(field.factors(point[group_size:-1])) == field.q
                         and orbit_size(field, [point[-1]], 0) == field.s):
            held.append((point, words))
    checked = 0
    for point, words in held:
        for mask, word in enumerate(words[1:], 1):
            assert orbit_size(field, point, mask) == field.s
            assert counts[word] == field.s
            if checked % 251 == 0:
                assert field.word(tuple(map(field.square, point)), field.square(mask)) == word
            checked += 1
    assert counts[0] > field.s
    return checked, sum(counts.values())


def truncation_examples(field):
    rng = Random(1474)
    cases = 0
    for _ in range(80):
        point = [rng.randrange(2, field.q) for _ in range(5)]
        mask = rng.randrange(1, field.q)
        original = field.word(point, mask)
        t = point[-1]
        first_half = (1 << 16) - 1
        found = False
        for other in range(2, field.q):
            new_mask = field.mul[field.mul[mask][1 ^ t]][field.inv[1 ^ other]]
            new_word = field.word(point[:-1] + [other], new_mask)
            diff = original ^ new_word
            assert not diff & first_half
            if (diff >> 16) & 1:
                assert (diff & ((1 << 17)-1)).bit_count() == 1
                found = True
                break
        assert found
        cases += 1
    return cases


def subset_counts(field, ratios):
    counts = [0]*field.q
    counts[1] = 1
    for r in ratios:
        new = counts.copy()
        for a, value in enumerate(counts):
            new[field.mul[a][r]] += value
        counts = new
    return counts


def total_variation(counts):
    n, q = sum(counts), len(counts)
    return Fraction(sum(abs(q*x-n) for x in counts), 2*n*q)


def collision_identity(field, maximum):
    q = field.q
    checks = 0
    for m in range(maximum + 1):
        square_mass = 0
        for ratios in product(range(2, q), repeat=m):
            counts = subset_counts(field, ratios)
            square_mass += sum(x*x for x in counts)
        observed = Fraction((q-1)*square_mass, (q-2)**m * 4**m) - 1
        expected = (q-2)*Fraction(q-3, 2*(q-2))**m
        assert observed == expected
        checks += 1
    return checks


def hadamard(array):
    out = array.copy()
    step = 1
    while step < len(out):
        for offset in range(0, len(out), 2*step):
            for i in range(offset, offset+step):
                a, b = out[i], out[i+step]
                out[i], out[i+step] = a+b, a-b
        step *= 2
    return out


def pair_histogram(q, left, right):
    counts = [0]*(q*q)
    for a, b in zip(left, right, strict=True):
        counts[a*q+b] += 1
    return counts


def pairing_distances(field, a, ap, b, bp):
    # The Walsh transform of the joint second-block histogram gives the
    # complete row-distance matrix, without materializing the address tensor.
    q = field.q
    transformed = hadamard(pair_histogram(q, b, bp))
    distances = [[(len(b)-transformed[field.dual[x]*q+field.dual[y]])//2
                  for y in range(q)] for x in range(q)]
    disagreements = sum(distances[x][y] for x, y in zip(a, ap, strict=True))
    return Fraction(disagreements, len(a)*len(b)), distances


def mixing_and_rigidity(field):
    q, s = field.q, field.s
    rng = Random(63179)

    def order(g):
        x, n = g, 1
        while x != 1:
            x = field.mul[x][g]
            n += 1
        return n

    generator = next(x for x in range(2, q) if order(x) == q-1)
    packet = [generator]
    for _ in range(s-1):
        packet.append(field.square(packet[-1]))
    left = packet*2
    right = left.copy()
    rng.shuffle(right)
    mixing = 0
    for ratios in (left, right):
        for omit in range(-1, len(ratios)):
            effective = [r for i, r in enumerate(ratios) if i != omit]
            assert total_variation(subset_counts(field, effective)) <= Fraction(1, 32)
            mixing += 1

    random_good = 0
    for _ in range(40):
        ratios = [rng.randrange(2, q) for _ in range(18)]
        random_good += all(total_variation(subset_counts(field, ratios[:i]+ratios[i+1:]))
                           <= Fraction(1, 32) for i in range(len(ratios)))
    assert random_good > 0

    p = list(map(field.from_odds, left+right))
    half = len(left)
    mask = rng.randrange(1, q)

    def blocks(point, lam):
        a = [field.mul[lam][z] for z in field.factors(point[:half])]
        b = field.factors(point[half:])
        return a, b

    a, b = blocks(p, mask)
    orbit = set()
    point, lam = p.copy(), mask
    for _ in range(s):
        orbit.add((tuple(point), lam))
        point, lam = list(map(field.square, point)), field.square(lam)
    alternatives = set(orbit)
    alternatives.add((tuple(p), 0))
    for i in range(len(p)):
        for new in (0, 1, rng.randrange(2, q)):
            alt = p.copy()
            alt[i] = new
            alternatives.add((tuple(alt), mask))
            if new != 1 and new != p[i]:
                # Preserve the complete address half with bit i equal to zero.
                adjusted = field.mul[field.mul[mask][1 ^ p[i]]][field.inv[1 ^ new]]
                alternatives.add((tuple(alt), adjusted))
    for _ in range(15):
        alternatives.add((tuple(rng.randrange(q) for _ in p), rng.randrange(q)))
    for lam in range(1, q):
        alternatives.add((tuple(p), lam))
    least = Fraction(1)
    for point, lam in sorted(alternatives):
        ap, bp = blocks(point, lam)
        error, _ = pairing_distances(field, a, ap, b, bp)
        if (point, lam) in orbit:
            assert not error
        else:
            least = min(least, error)
            assert error >= Fraction(1, 64)
    assert least < Fraction(1,3)

    # Apply an arbitrary invertible binary shear and its trace-adjoint inverse,
    # then corrupt a small number of rows and columns. Check identification of
    # every alternate symbol by its corresponding honest row.
    transform = [x ^ ((x & 1) << 1) for x in range(q)]
    inverse = {y: x for x, y in enumerate(transform)}
    transformed_pair_keys = [
        sum(field.trace[field.mul[transform[1 << i]][z]] << i for i in range(s))
        for z in range(q)]
    adjoint_inverse = [transformed_pair_keys.index(field.dual[y]) for y in range(q)]
    ap = [transform[x] for x in a]
    bp = [adjoint_inverse[y] for y in b]
    assert pairing_distances(field, a, ap, b, bp)[0] == 0
    for data in (ap, bp):
        for i in rng.sample(range(len(data)), len(data)//256):
            data[i] ^= rng.randrange(1, q)
    e, distances = pairing_distances(field, a, ap, b, bp)
    assert 0 < e < Fraction(1,64)
    decoded = []
    for y in range(q):
        matches = [x for x in range(q) if 8*distances[x][y] <= len(b)]
        assert matches == [inverse[y]]
        decoded.append(matches[0])
    assert all(decoded[x^y] == decoded[x]^decoded[y] for x in range(q) for y in range(q))
    alpha, tau, nu = Fraction(15,32), Fraction(1,16), Fraction(1,32)
    assert 6*tau < alpha and 1-2*Fraction(1,64)/(alpha-2*tau) > Fraction(1,2)+nu
    return mixing, random_good, len(alternatives), least, e


if __name__ == "__main__":
    small = BinaryField(4, 0b111)
    middle = BinaryField(8, 0b1011)
    large = BinaryField(64, 0b1000011)
    for field, group_size in [(small, 1), (middle, 2)]:
        true_tuples, full_search = exhaustive_orbits(field, group_size)
        print(f"F{field.q}: {true_tuples} full-span descriptors checked "
              f"against all {full_search} alternatives")
    # Bad full-grid descriptors can be one bit apart on an arbitrarily large
    # cube. Here the coordinate tuple is Boolean and the trace mask is nonzero.
    trace_one = small.trace.index(1)
    assert small.word([0]*10, trace_one) == 1
    assert small.word([0]*10, 0) == 0
    print(f"{truncation_examples(middle)} truncated-grid one-bit discrepancies; "
          f"{collision_identity(small, 5)+collision_identity(middle, 4)} "
          "exact multiplicative second moments")
    mixing, random_good, alternatives, least, noisy = mixing_and_rigidity(large)
    print(f"F64: {mixing} deterministic mixing checks; {random_good}/40 seeded "
          f"random blocks satisfy all single-deletion TV bounds")
    print(f"{alternatives} alternatives on 2^24 addresses; smallest observed "
          f"inequivalent distance {float(least):.6f}; recovered all 64 linear "
          f"labels with corrupted pair error {float(noisy):.6f}")
