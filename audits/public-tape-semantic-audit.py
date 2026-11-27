"""Exact finite checks of adaptive moment transfer and the sharp success-grid bound."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod


def field_multiply(x, y):
    """GF(8) in the polynomial basis with modulus u^3+u+1."""
    out = 0
    while y:
        if y & 1:
            out ^= x
        y >>= 1
        x <<= 1
        if x & 8:
            x ^= 0b1011
    return out


def polynomial_tapes(h):
    # Project degree-<h polynomials to the low bit at all eight positions.
    # Count all multiplicities through the binary linear image of each coefficient.
    powers = [1] * 8
    pool = Counter({0: 1})
    for _ in range(h):
        for basis in (1, 2, 4):
            mask = sum((field_multiply(basis, value) & 1) << i for i, value in enumerate(powers))
            extra = Counter({tape ^ mask: mass for tape, mass in pool.items()})
            pool.update(extra)
        powers = [field_multiply(value, x) for x, value in enumerate(powers)]
    assert pool.total() == 8**h
    return pool


def cardinal_weights(nodes, at):
    return [prod((Fraction(at - other, x - other) for other in nodes if other != x),
                 start=Fraction(1)) for x in nodes]


def grid_bound(ceiling, floor, d):
    # An optimum set of interpolation nodes certifies both sides of the discrete LP.
    choices = combinations(range(ceiling + 1), d + 1)
    nodes = min(choices, key=lambda xs: sum(map(abs, cardinal_weights(xs, floor))))
    weights = cardinal_weights(nodes, floor)
    norm = sum(map(abs, weights))
    signs = [1 if w > 0 else -1 for w in weights]
    scored = [sum(s*w for s, w in zip(signs, cardinal_weights(nodes, x))) for x in range(floor + 3)]
    assert all(abs(v) <= 1 for v in scored[:ceiling + 1])
    assert all(left <= right for left, right in zip(scored[ceiling:], scored[ceiling+1:]))
    assert scored[floor] == norm
    positive = sum(w for w in weights if w > 0)
    actual = {floor: 1 / positive}
    restricted = {}
    for x, w in zip(nodes, weights):
        if w > 0:
            restricted[x] = w / positive
        else:
            actual[x] = -w / positive
    assert sum(actual.values()) == sum(restricted.values()) == 1
    for power in range(d + 1):
        assert sum(m * x**power for x, m in actual.items()) == sum(m * x**power for x, m in restricted.items())
    assert actual[floor] == 2 / (1 + norm)
    return Fraction(actual[floor])


def transcript(tape, i, mode):
    first = (i + mode) % 8
    a = (tape >> first) & 1
    if mode % 3 == 0:
        second = first if a else (3*i + 1) % 8
    elif mode % 3 == 1:
        second = (i + (3 if a else 6)) % 8
    else:
        second = first if i == 0 else (i ^ (5 + a)) % 8
    b = (tape >> second) & 1
    return 2*a + b


def normalized(hist, total):
    return {code: Fraction(count, total) for code, count in hist.items()}


def test_tapes():
    actual = Counter({tape: 1 for tape in range(256)})
    tests = moments = certified = 0
    for t in (2, 3):
        sim = polynomial_tapes(2*t)
        assert len(sim) < len(actual)
        bounds = {(a,b): grid_bound(a,b,t) for a in range(t, 8) for b in range(a+1, 9)}
        for mode in range(4):
            paths = [[transcript(tape, i, mode) for i in range(8)] for tape in actual]
            for indices in product(range(8), repeat=t):
                codes = [sum(path[i] << (2*j) for j, i in enumerate(indices)) for path in paths]
                left = Counter(codes)
                right = Counter()
                for tape, mass in sim.items():
                    right[codes[tape]] += mass
                assert normalized(left, actual.total()) == normalized(right, sim.total())
                tests += 1
            outputs = [sum((((bits >> 1) ^ bits ^ (i >> 1)) & 1) << i
                           for i, bits in enumerate(path)) for path in paths]
            for target in (0, 1, 0x96, 0x99, 0xAA, 0xFF):
                successes = [8 - (word ^ target).bit_count() for word in outputs]
                left = Counter(successes)
                right = Counter()
                for tape, mass in sim.items():
                    right[successes[tape]] += mass
                for j in range(t + 1):
                    assert sum(x**j * n for x,n in left.items()) * sim.total() == sum(
                        x**j * n for x,n in right.items()) * actual.total()
                    moments += 1
                for cutoff in range(t + 1):
                    def accepted(x):
                        return sum(comb(t,k) * x**k * (8-x)**(t-k) for k in range(cutoff, t+1))
                    assert sum(accepted(x)*n for x,n in left.items()) * sim.total() == sum(
                        accepted(x)*n for x,n in right.items()) * actual.total()
                for (a,b), limit in bounds.items():
                    fraction = Fraction(sum(n for x,n in left.items() if x >= b), actual.total())
                    if fraction > limit:
                        assert max(right) > a
                        certified += 1
    # One-wise uniform tapes suffice for one input, yet they can lose all accuracy advantage.
    balanced = 0x0F
    one = polynomial_tapes(1)
    assert set(one) == {0, 255}
    assert max(8 - (balanced ^ z).bit_count() for z in one) == 4
    assert actual[balanced] == 1
    return tests, moments, certified


def chebyshev(d, x):
    a, b = 1, x
    for _ in range(d):
        a, b = b, 2*x*b - a
    return a


if __name__ == '__main__':
    grids = 0
    for a in range(9):
        for b in range(a+1, 10):
            for d in range(a+1):
                value = grid_bound(a,b,d)
                if a and d <= 3 and (d <= 1 or a % (2 if d == 2 else 4) == 0):
                    # In these cases all continuous extrema are already grid points.
                    assert value == Fraction(2, 1 + chebyshev(d, Fraction(2*b,a)-1))
                grids += 1
    tests, moments, certified = test_tapes()
    print(f"{grids} sharp grid laws; {tests} adaptive repeated-input tuples; "
          f"{moments} matched accuracy moments; {certified} strict grid transfers")
