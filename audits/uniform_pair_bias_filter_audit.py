"""Exact finite checks for the soft filters in the uniform-witness construction."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb, lcm, prod

from uniform_soft_link_audit import make_clauses, satisfies


def decode(raw, q):
    return (raw ^ (raw >> q) ^ (raw >> (2 * q))) & ((1 << q) - 1)


@lru_cache(maxsize=None)
def masks(lit, y, z):
    allowed = []
    for u, v in product((0, 1), repeat=2):
        h = u ^ v
        a, b, c = lit ^ u, y ^ v, z ^ h
        if (a, b, c) != (1, 1, 1):
            allowed.append((u, v, h, a, b, c))
    assert len(allowed) == (3 if lit ^ y ^ z else 4)
    return allowed


@lru_cache(maxsize=None)
def extensions(lit, y, z, low):
    if low == 3:
        return masks(lit, y, z)
    assert low == 2
    clauses = make_clauses()
    return [
        bits for bits in product((0, 1), repeat=6)
        if satisfies((lit, y, z) + bits, clauses)
    ]


@lru_cache(maxsize=None)
def link_mass(lit, y, z, k, low):
    if not ((lit or not y or z) and (lit or y or not z)):
        return 0
    count = len(extensions(lit, y, z, low))
    assert count == (4 if lit == (y ^ z) else low)
    return count ** k


def path_mass(literals, width, k, low):
    total = 0
    for seed in (0, 1):
        ways = [int(y == seed) for y in (0, 1)]
        for j in range(width):
            lit = (literals >> j) & 1
            ways = [
                sum(ways[y] * link_mass(lit, y, z, k, low) for y in (0, 1))
                for z in (0, 1)
            ]
        total += ways[1 - seed]
    return total


def omission_weights(width, h, k, low):
    return [
        (s, comb(h, s) * (low**s * 4**(width - s))**k)
        for s in range(h + 1) if (h - s) % 2
    ]


def check_masses(k, low):
    masses = {}
    raw_scopes = 0
    for q in (2, 3, 4):
        width = 3 * q
        paths = []
        for word in range(1 << width):
            h = word.bit_count()
            terms = omission_weights(width, h, k, low)
            value = path_mass(word, width, k, low)
            assert value == 2 * sum(weight for _, weight in terms)
            paths.append(value)
            if h:
                assert min(s for s, _ in terms) == 1 - h % 2
                if h % 2:
                    nonideal = sum(weight for s, weight in terms if s)
                    assert Fraction(2 * nonideal, value) <= (1 << width) * Fraction(low, 4)**(2*k)

        fibers = [[] for _ in range(1 << q)]
        for word in range(1 << width):
            fibers[decode(word, q)].append(word)
        for delta, fiber in enumerate(fibers):
            masses[q, delta] = prod(paths[word] for word in fiber)
        # Compare weight histograms for *each* raw encoding on a shared scope.
        # Other forbidden tuples translate this test by XOR.
        bad = 1
        profile = [Counter(word.bit_count() for word in fiber) for fiber in fibers]
        for raw in range(1 << width):
            delta = decode(raw, q) ^ bad
            assert Counter((raw ^ p).bit_count() for p in fibers[bad]) == profile[delta]
            assert bool(masses[q, delta]) == bool(delta)
            raw_scopes += 1
    return masses, raw_scopes


def check_scans(masses):
    checked = 0
    for t in range(1, 9):
        one_hot = []
        for flags in product((0, 1), repeat=t):
            mass = 1
            for sequence in (flags, flags[::-1]):
                p = 0
                for a in sequence:
                    # Scope (p, p', a) with an independently shared copy p'=p.
                    delta = 7 ^ (p | p << 1 | a << 2)
                    mass *= masses[3, delta]
                    p ^= a
                if p != 1:
                    mass = 0
            assert bool(mass) == (sum(flags) == 1)
            if mass:
                one_hot.append(mass)
            checked += 1
        # The hard parity checks have two seeds for each complemented or
        # ordinary cycle, and each logical bit has four raw encodings. Both
        # factors are constant across positions and omitted here.
        assert len(one_hot) == t and len(set(one_hot)) == 1
    return checked


@lru_cache(maxsize=None)
def mask_moments(lit, y, z, low):
    outcomes = [[1 - 2 * bit for bit in bits] for bits in extensions(lit, y, z, low)]
    means = [12 * sum(column) // len(outcomes) for column in zip(*outcomes)]
    corrections = {
        (i, j): 144 * sum(v[i] * v[j] for v in outcomes) // len(outcomes) - means[i] * means[j]
        for i, j in combinations(range(6), 2)
    }
    return means, corrections


def check_worked_cycle(low, t=8, k=16):
    # A chosen inactive pin a OR not-x in the one-hot construction. The
    # unique source model has x=0. All other tests have already been summed
    # out conditional on the decoded tuple, via the constant fiber masses.
    # The old bits are the six input shares and the six stored states. Two
    # copies out of k at every edge cover all within- and between-copy pairs.
    q = 2
    width = 3 * q
    forbidden = 2  # First-share representative decoding to (a=0, x=1).
    total_bits = width * 2 + width * 2 * 6
    singles = [0] * total_bits
    pairs = [[0] * i for i in range(total_bits)]
    normalizers = {
        h: sum(w for _, w in omission_weights(width, h, k, low))
        for h in range(1, width + 1)
    }
    common = lcm(*normalizers.values())
    total = 0
    for raw in range(1 << width):
        logical = decode(raw, q)
        if logical not in (0, 1):
            continue
        multiplicity = t - 1 if logical == 0 else 1
        literals = raw ^ forbidden
        h = literals.bit_count()
        base = multiplicity * (common // normalizers[h])
        for increments in range(1 << width):
            if increments & ~literals or increments.bit_count() % 2 == 0:
                continue
            omitted = h - increments.bit_count()
            weight = base * (low**omitted * 4**(width - omitted))**k
            for seed in (0, 1):
                states = [seed]
                for j in range(width):
                    states.append(states[-1] ^ (increments >> j & 1))
                assert states[-1] == 1 - seed
                old = [(raw >> j) & 1 for j in range(width)] + states[:-1]
                means = [12 * (1 - 2 * x) for x in old]
                for j in range(width):
                    m, corrections = mask_moments(literals >> j & 1, states[j], states[j + 1], low)
                    for _ in range(2):
                        offset = len(means)
                        means.extend(m)
                        for (r, s), correction in corrections.items():
                            pairs[offset + s][offset + r] += weight * correction
                for i, mean in enumerate(means):
                    factor = weight * mean
                    singles[i] += factor
                    for j in range(i):
                        pairs[i][j] += factor * means[j]
                total += weight
    assert total == 2 * t * 4**q * common
    max_single = Fraction(max(map(abs, singles)), 12 * total)
    max_pair = Fraction(max(abs(v) for row in pairs for v in row), 144 * total)
    # In the inactive fiber, couple to no omissions using the same raw shares
    # and seed. The sign expectation changes by at most twice the error.
    bound = Fraction(1, t) + (2 << width) * Fraction(low, 4)**(2*k)
    assert max_single <= bound and max_pair <= bound < 1
    assert (max_single == 0) == (low == 2)
    assert not any(singles[:2 * width])
    return total_bits, max_single, max_pair, bound


def main():
    for low in (2, 3):
        masses, raw_scopes = check_masses(k=3, low=low)
        flags = check_scans(masses)
        print(f"4/{low}: {raw_scopes} raw encodings, arities 2 through 4, "
              f"{flags} two-scan flag vectors")
        bits, single, pair, bound = check_worked_cycle(low)
        print(f"4/{low} at t=8, k=16: {bits} singles and {comb(bits, 2)} distinct pairs")
        print(f"Maximum absolute moments {float(single):.9f}, {float(pair):.9f}; "
              f"bound {float(bound):.9f}")


if __name__ == "__main__":
    main()
