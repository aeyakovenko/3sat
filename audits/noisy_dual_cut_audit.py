"""Exact small cases for the conditional dual-code kernel and its SAT guard."""
from collections import Counter
from itertools import combinations, product
from math import prod
from random import Random


def parity(x):
    return x.bit_count() % 2


def masks(size, lo, hi):
    for width in range(lo, hi + 1):
        for positions in combinations(range(size), width):
            yield sum(1 << i for i in positions)


def check_conditional_density():
    k = 7
    dual = [sum(parity(m & col) << (col - 1) for col in range(1, 8))
            for m in range(8)]
    primal = [x for x in range(1 << k) if all(not parity(x & v) for v in dual)]
    assert len(primal) == 16 and all(v.bit_count() == 4 for v in dual[1:])
    # p=1/4. Density relative to uniform, with denominator 4**k.
    density = [(2**k // len(primal)) * sum(3**(k - (x ^ u).bit_count()) for u in primal)
               for x in range(1 << k)]
    cases = 0
    for prefix in masks(k, 0, 2):
        rest = ((1 << k) - 1) ^ prefix
        for pin in range(1 << k):
            if pin & ~prefix:
                continue
            points = [x for x in range(1 << k) if x & prefix == pin]
            assert sum(density[x] for x in points) == len(points) * 4**k
            # The exact distribution of *all* noise bits survives conditioning.
            for noise in range(1 << k):
                assert sum((u ^ noise) & prefix == pin for u in primal) * 2**prefix.bit_count() == len(primal)
            for row in masks(k, 2, 2):
                if row & prefix:
                    continue
                col = rest ^ row
                cells = [(v & row, v & col) for v in dual]
                assert len(set(cells)) == len(dual)
                for part in (row, col):
                    freq = Counter(v & part for v in dual)
                    assert max(freq.values()) * (part.bit_count() - 1) <= k
                for x in points:
                    delta = sum((-1)**(parity(v & pin) ^ parity(v & row & x) ^ parity(v & col & x))
                                * (4**k // 2**v.bit_count()) for v in dual[1:])
                    assert 4**k + delta == density[x]
                cases += 1
    return cases


def mul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 0b1011
    return out


def ev(poly, x):
    ans = 0
    for c in reversed(poly):
        ans = mul(ans, x) ^ c
    return ans


def trace(z):
    z2 = mul(z, z)
    return z ^ z2 ^ mul(z2, z2)


def check_dual_guard():
    sites = tuple(range(5))
    inner = [0b1001, 0b0010, 0b1100]
    encoded = []
    for m in range(8):
        v = 0
        for i, image in enumerate(inner):
            if (m >> i) & 1:
                v ^= image
        encoded.append(v)
    code = [tuple(encoded[ev(coef, x)] for x in sites)
            for coef in product(range(8), repeat=2)]
    derivative = []
    for x in sites:
        h = 1
        for y in sites:
            if y != x:
                h = mul(h, x ^ y)
        derivative.append(h)
    candidates = {tuple(ev(q, x) for x in sites) for q in product(range(8), repeat=3)}
    represent = {}
    for u in range(8):
        represent[tuple(trace(mul(u, 1 << j)) for j in range(3))] = u
    assert len(represent) == 8
    def convert(z):
        return represent[tuple(parity(z & c) for c in inner)]
    # Test every syndrome input up to the inner transpose's kernel,
    # then add an independently drawn lift at each coordinate.
    fibers = [[z for z in range(16) if convert(z) == u] for u in range(8)]
    rng = Random(481)
    hits = 0
    for us in product(range(8), repeat=len(sites)):
        raw = tuple(rng.choice(fibers[u]) for u in us)
        dual_member = all(sum(parity(z & c) for z, c in zip(raw, w)) % 2 == 0 for w in code)
        has_witness = tuple(mul(d, u) for d, u in zip(derivative, us)) in candidates
        assert dual_member == has_witness
        hits += dual_member
    assert hits == 8**3
    return prod([8] * len(sites))


if __name__ == "__main__":
    print(f"{check_conditional_density()} conditional Walsh splits passed")
    print(f"{check_dual_guard()} concatenated-code dual tests passed")
