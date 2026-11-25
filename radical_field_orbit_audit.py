"""Check simple-field compatibility under joint quadratics and the orbit counting factors."""

from collections import Counter
from itertools import product
from math import factorial, prod
from random import Random

from trace_product_bias_audit import field


def sample_quadratic(n, rng):
    # A general joint quadratic, expressed as a sum of products of two parities.
    masks = [(rng.randrange(1 << n), rng.randrange(1 << n)) for _ in range(2 * n)]
    return [sum(((a & x).bit_count() & (b & x).bit_count() & 1)
                for a, b in masks) & 1 for x in range(1 << n)]


def compatibility_trial(degrees, rng):
    parts = [(1 << e, *field(e)) for e in degrees]
    n = 3 * sum(degrees)
    masks = list(product(*(range(q) for q, _, _ in parts)))
    all_inputs = list(product(*(range(q) for q, _, _ in parts for _ in range(3))))
    widths = [e for e in degrees for _ in range(3)]
    offsets = [sum(widths[:j]) for j in range(len(widths))]

    def pack(coords):
        return sum(entry << k for entry, k in zip(coords, offsets))

    quad = sample_quadratic(n, rng)
    truth = [0] * (1 << n)
    for coords in all_inputs:
        value = quad[pack(coords)]
        for i, (_, mul, trace) in enumerate(parts):
            a, b, c = coords[3*i:3*i+3]
            value ^= trace[mul[mul[a][b]][c]]
        truth[pack(coords)] = value

    compatible = 0
    for coords in all_inputs:
        x = pack(coords)
        signs = []
        for s_vec in masks:
            v = 0
            cubic = 0
            for i, ((_, mul, trace), s) in enumerate(zip(parts, s_vec)):
                a, b, c = coords[3*i:3*i+3]
                for k, entry in enumerate((a, b, c), 3*i):
                    v |= mul[s][entry] << offsets[k]
                coeff = mul[s][s] ^ s
                cubic ^= trace[mul[coeff][mul[mul[a][b]][c]]]
            direct = truth[x^v] ^ truth[x] ^ truth[v] ^ truth[0]
            polar_q = quad[x^v] ^ quad[x] ^ quad[v] ^ quad[0]
            assert direct == cubic ^ polar_q
            signs.append(1 - 2*direct)
        assert sum(signs) in (0, len(masks))
        compatible += (sum(signs) == len(masks))
    return compatible


def root_count(degree, copies):
    q = 1 << degree
    mul, _ = field(degree)
    minpoly_ids = {}
    for z in range(1, q):
        # The Frobenius orbit identifies the irreducible polynomial of the element.
        orbit = {z}
        w = mul[z][z]
        while w != z:
            orbit.add(w)
            w = mul[w][w]
        if len(orbit) == degree:
            minpoly_ids[z] = min(orbit)

    singles = Counter()
    for a, b, c in product(range(1, q), repeat=3):
        z = mul[mul[a][b]][c]
        if z in minpoly_ids:
            singles[minpoly_ids[z]] += 1
    assert all(m == degree*(q-1)**2 for m in singles.values())
    multiset_counts = Counter()
    for types in product(singles, repeat=copies):
        if len(set(types)) == copies:
            multiset_counts[tuple(sorted(types))] += prod(singles[t] for t in types)
    expected = factorial(copies) * (degree * (q-1)**2)**copies
    assert multiset_counts and set(multiset_counts.values()) == {expected}
    return len(multiset_counts), expected


if __name__ == "__main__":
    rng = Random(71399)
    for degrees in [(2,), (1, 2), (3,)]:
        counts = [compatibility_trial(degrees, rng) for _ in range(4)]
        print(f"Field degrees {degrees}, compatible-shift counts {counts} out of {2**(3*sum(degrees))}")
    for e, h in [(2, 1), (3, 2), (4, 2)]:
        print(f"Degree {e}, multiplicity {h}, orbit counts and multiplicity {root_count(e, h)}")
