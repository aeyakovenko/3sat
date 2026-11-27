"""Finite checks for sparse monomial evaluation spans and dyadic selector pulses."""

from functools import cache
from itertools import product
from random import Random


def evaluation(monomials, point):
    return sum(1 << i for i, s in enumerate(monomials) if point & s == s)


def xor_rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            i = v.bit_length() - 1
            if i not in pivots:
                pivots[i] = v
                break
            v ^= pivots[i]
    return len(pivots)


def sample_vectors(monomials, fixed_mask, ones):
    # A surviving monomial restricts to its free coordinates. Evaluating at
    # those supports samples the inclusion matrix on its distinct rows.
    supports = {s & ~fixed_mask for s in monomials if not (s & fixed_mask & ~ones)}
    return [evaluation(monomials, ones | s) for s in sorted(supports)]


def span_audit():
    n = 3
    checked = 0
    for mask in range(1 << (1 << n)):
        family = [s for s in range(1 << n) if mask >> s & 1]
        for assignment in product((-1, 0, 1), repeat=n):
            fixed = sum(1 << j for j, v in enumerate(assignment) if v != -1)
            ones = sum(1 << j for j, v in enumerate(assignment) if v == 1)
            actual = [evaluation(family, x) for x in range(1 << n) if x & fixed == ones]
            samples = sample_vectors(family, fixed, ones)
            assert set(samples) <= set(actual)
            assert len(samples) == xor_rank(samples) == xor_rank(actual)
            checked += 1
    return checked


def bilinear_audit(rng):
    # The i-th mixed monomial is the product of feature i from each side.
    # Repeated supports occur on either side and circuit terms may cancel.
    n = 4
    checked = 0
    outcomes = set()
    for _ in range(2048):
        width = rng.randrange(1, 15)
        families = [[rng.randrange(1 << n) for _ in range(width)] for _ in range(2)]
        actual, samples = [], []
        for family in families:
            fixed = rng.randrange(1 << n)
            ones = rng.randrange(1 << n) & fixed
            actual.append([evaluation(family, x) for x in range(1 << n) if x & fixed == ones])
            samples.append(sample_vectors(family, fixed, ones))
        coefficients = rng.randrange(1 << width)
        def all_zero(rows, cols):
            return all((x & y & coefficients).bit_count() % 2 == 0 for x in rows for y in cols)
        result = all_zero(*actual)
        assert all_zero(*samples) == result
        outcomes.add(result)
        checked += 1
    assert outcomes == {True, False}
    return checked


def selected_width(u, n):
    k = n // 2
    q = u >> k
    return min(k, q & -q) if q else 1


@cache
def variable_table(dimensions, bit):
    size = 1 << dimensions
    run = 1 << bit
    # Repeat run zeroes, run ones in increasing point order.
    return (((1 << size) - 1) // ((1 << (2 * run)) - 1)) * (((1 << run) - 1) << run)


def monomial_table(dimensions, support):
    table = (1 << (1 << dimensions)) - 1
    while support:
        bit = support & -support
        table &= variable_table(dimensions, bit.bit_length() - 1)
        support ^= bit
    return table


def selector_audit(rng):
    slices = 0
    comparisons = 0
    for n in (2, 3, 4, 5, 6, 8):
        k = n // 2
        p = 1
        while p <= k:
            # Fix only bits determining q = p mod 2p, not the full selector.
            fixed = (2*p - 1) << k
            free = [j for j in range(2*n) if not (fixed >> j & 1)]
            dim = len(free)
            active = sum(1 << free.index(j) for i in range(p) for j in (i, n+i))
            truth_bytes = bytearray(((1 << dim) + 7) // 8)
            for x in range(1 << dim):
                uv = (p << k) | sum(((x >> i) & 1) << j for i, j in enumerate(free))
                u, v = uv & ((1 << n) - 1), uv >> n
                assert selected_width(u, n) == p
                if not (u & v & ((1 << p) - 1)):
                    truth_bytes[x // 8] |= 1 << (x % 8)
            pulse = int.from_bytes(truth_bytes, 'little')
            # The coefficient of the product of all 2p active variables is
            # the parity on their subcube with every other free bit zero.
            face_points = [s for s in range(1 << dim) if s & ~active == 0]
            face = sum(1 << s for s in face_points)
            assert (pulse & face).bit_count() % 2 == 1
            bound = 1 << (dim - 2*p)
            assert bound * 2*p * 4**p == 1 << (2*n)
            # Generate lower-degree perturbations on all free variables.
            corrections = [0]
            for _ in range(32):
                correction = 0
                for _ in range(rng.randrange(1, 18)):
                    chosen = rng.sample(range(dim), rng.randrange(2*p))
                    correction ^= monomial_table(dim, sum(1 << j for j in chosen))
                corrections.append(correction)
            for base in corrections:
                residual = pulse ^ base
                assert (residual & face).bit_count() % 2 == 1
                assert residual.bit_count() >= bound
                comparisons += 1
            # Exhaust all degree < 2p additions on the active variables for
            # p <= 2, reusing the previous truth table via binary Gray code.
            if p <= 2:
                active_dim = 2*p
                tt = sum(((pulse >> s) & 1) << i for i, s in enumerate(face_points))
                terms = [monomial_table(active_dim, s) for s in range((1 << active_dim) - 1)]
                residual = tt
                for i in range(1 << len(terms)):
                    if i:
                        residual ^= terms[(i & -i).bit_length() - 1]
                    assert residual.bit_count() % 2 == 1
                    comparisons += 1
            slices += 1
            p *= 2
    return slices, comparisons


if __name__ == '__main__':
    rng = Random(20261125)
    print(f'{span_audit()} exhaustive monomial-family and subcube span tests')
    print(f'{bilinear_audit(rng)} direct grid versus paired span tests')
    slices, checks = selector_audit(rng)
    print(f'{slices} selector slices and {checks} lower-degree perturbations')
