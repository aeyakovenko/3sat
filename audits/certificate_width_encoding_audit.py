"""Check the witness-mass estimate on small conjunctions of local tests."""
from fractions import Fraction
from itertools import combinations, product
from random import Random


def all_subcubes(p):
    cubes = []
    for pattern in product((-1, 0, 1), repeat=p):
        mask = sum(1 << x for x in range(1 << p)
                   if all(b == -1 or ((x >> i) & 1) == b for i, b in enumerate(pattern)))
        cubes.append((sum(b != -1 for b in pattern), mask))
    return cubes


def make_test(coords, table, p):
    return sum(1 << x for x in range(1 << p)
               if (table >> sum(((x >> bit) & 1) << j for j, bit in enumerate(coords))) & 1)


def check(p, k):
    all_bits = (1 << (1 << p))-1
    tests = [make_test(coords, t, p) for coords in combinations(range(p), k)
             for t in range(1 << (1 << k))]
    cubes = all_subcubes(p)
    rng = Random(41 + 3*p + k)
    cases = [(a & b,) for a in tests for b in tests] if p <= 3 else []
    for _ in range(1800):
        witnesses = []
        for _ in range(rng.choice((1, 2, 4))):
            value = all_bits
            for _ in range(rng.randrange(1, 7)):
                value &= rng.choice(tests)
            witnesses.append(value)
        cases.append(tuple(witnesses))
    for witnesses in cases:
        f = 0
        for w in witnesses:
            f |= w
        if not f:
            continue
        c = min(fixed for fixed, mask in cubes if (mask & f) == mask)
        bound = (1-Fraction(1, 2**k))**((c+k-1)//k)
        assert all(Fraction(w.bit_count(), 2**p) <= bound for w in witnesses)
        assert Fraction(f.bit_count(), 2**p) <= len(witnesses)*bound
    return len(cases)


if __name__ == "__main__":
    print(f"{sum(check(p,k) for p,k in ((3,1),(3,2),(4,2),(5,3)))} local-test witness systems checked")
