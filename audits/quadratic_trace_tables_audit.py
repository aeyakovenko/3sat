"""Exact contraction of two arbitrary lookup tables behind affine/quadratic maps."""
from fractions import Fraction
from random import Random


def dot(a, b):
    return (a & b).bit_count() % 2


def linear_image(masks, x):
    return sum(dot(mask, x) << i for i, mask in enumerate(masks))


def combine(basis, coefficients):
    result = 0
    for i, vector in enumerate(basis):
        if (coefficients >> i) & 1:
            result ^= vector
    return result


def constrain(origin, basis, equations):
    for mask, bit in equations:
        pivot = next((v for v in basis if dot(mask, v)), None)
        if pivot is None:
            if dot(origin, mask) != bit:
                return None
            continue
        if dot(origin, mask) != bit:
            origin ^= pivot
        basis = [(v ^ pivot if dot(mask, v) else v) for v in basis if v != pivot]
    return origin, basis


def split_kernel(basis, image):
    kernel, complement, pivots = [], [], {}
    for v in basis:
        y = image(v)
        while y:
            p = y.bit_length() - 1
            if p not in pivots:
                pivots[p] = (v, y)
                complement.append(v)
                break
            old, old_image = pivots[p]
            v ^= old
            y ^= old_image
        else:
            kernel.append(v)
    return kernel, complement


def complete_basis(initial, spanning):
    pivots = {}
    extra = []
    for i, original in enumerate(initial + spanning):
        v = original
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                pivots[p] = v
                if i >= len(initial):
                    extra.append(original)
                break
            v ^= pivots[p]
    return extra


def evaluate(monomials, x):
    return sum(x & m == m for m in monomials) % 2


def quadratic_expansion(d, value):
    constant = value(0)
    units = [value(1 << i) for i in range(d)]
    result = {0} if constant else set()
    for i in range(d):
        if units[i] ^ constant:
            result.add(1 << i)
        for j in range(i):
            ij = (1 << i) | (1 << j)
            if value(ij) ^ units[i] ^ units[j] ^ constant:
                result.add(ij)
    return result


def eliminate(phase, visible, internal):
    """Sum over internal variables and return power, affine constraints, phase."""
    remaining = set(range(visible, visible + internal))
    power = 0
    while True:
        pair = next((m for m in phase if m.bit_count() == 2 and
                     all(i in remaining for i in range(m.bit_length()) if (m >> i) & 1)), None)
        if pair is None:
            break
        a = pair & -pair
        b = pair ^ a
        left = {m ^ a for m in phase if (m & a) and m != pair}
        right = {m ^ b for m in phase if (m & b) and m != pair}
        phase = {m for m in phase if not (m & pair)}
        for u in left:
            for v in right:
                phase.symmetric_difference_update([u | v])
        power += 1
        remaining -= {a.bit_length() - 1, b.bit_length() - 1}
    equations = []
    for i in sorted(remaining):
        a = 1 << i
        terms = {m ^ a for m in phase if m & a}
        equations.append((sum(terms), int(0 in terms)))
        phase = {m for m in phase if not (m & a)}
    return power + len(remaining), equations, phase


def walsh(values):
    size = 1
    while size < len(values):
        for start in range(0, len(values), size * 2):
            for i in range(start, start + size):
                u, v = values[i], values[i + size]
                values[i] = u + v
                values[i + size] = u - v
        size *= 2


def sign(bit):
    return 1 - 2 * bit


def contract(d, left, right, phase, equations):
    left_masks, left_table = left
    right_masks, right_table = right
    support = constrain(0, [1 << i for i in range(d)], equations)
    if support is None:
        return 0
    origin, basis = support
    kernel, visible = split_kernel(basis, lambda x: linear_image(left_masks + right_masks, x))
    row_basis = visible + kernel

    def phase_on_coords(z):
        return evaluate(phase, origin ^ combine(row_basis, z))

    reduced = quadratic_expansion(len(row_basis), phase_on_coords)
    power, extra_equations, reduced = eliminate(reduced, len(visible), len(kernel))
    visible_support = constrain(0, [1 << i for i in range(len(visible))], extra_equations)
    if visible_support is None:
        return 0
    offset, visible_basis = visible_support

    def row(z):
        return combine(visible, z)

    a_basis, _ = split_kernel(visible_basis, lambda z: linear_image(right_masks, row(z)))
    b_basis, _ = split_kernel(visible_basis, lambda z: linear_image(left_masks, row(z)))
    shared = complete_basis(a_basis + b_basis, visible_basis)
    if len(a_basis) > len(b_basis):
        a_basis, b_basis = b_basis, a_basis
        left_masks, right_masks = right_masks, left_masks
        left_table, right_table = right_table, left_table

    def q(z):
        return evaluate(reduced, z)

    def interaction(a, b):
        return q(a ^ b) ^ q(a) ^ q(b) ^ q(0)

    cross = [sum(interaction(a, b) << j for j, a in enumerate(a_basis)) for b in b_basis]
    result = 0
    for t in range(1 << len(shared)):
        center = offset ^ combine(shared, t)
        buffer = [0] * (1 << len(a_basis))
        for b in range(1 << len(b_basis)):
            z = center ^ combine(b_basis, b)
            idx = linear_image(right_masks, origin ^ row(z))
            buffer[combine(cross, b)] += sign(q(z) ^ q(center)) * right_table[idx]
        walsh(buffer)
        for a in range(1 << len(a_basis)):
            z = center ^ combine(a_basis, a)
            idx = linear_image(left_masks, origin ^ row(z))
            result += sign(q(z)) * left_table[idx] * buffer[a]
    return result << power


def cubic_trace_flats():
    # GF(4) in polynomial basis modulo X²+X+1.
    def mul(a, b):
        high = (a << 1) ^ (7 if a & 2 else 0)
        return (a if b & 1 else 0) ^ (high if b & 2 else 0)

    def f(x):
        value = mul(mul(x & 3, (x >> 2) & 3), x >> 4)
        return value ^ mul(value, value)

    def degree_within_two(origin, basis):
        d = len(basis)
        values = [f(origin ^ combine(basis, x)) for x in range(1 << d)]
        for i in range(d):
            for x in range(1 << d):
                if x & (1 << i):
                    values[x] ^= values[x ^ (1 << i)]
        return all(v == 0 or x.bit_count() <= 2 for x, v in enumerate(values))

    units = [1 << i for i in range(6)]
    for normal in range(1, 64):
        for bit in (0, 1):
            flat = constrain(0, units, [(normal, bit)])
            assert not degree_within_two(*flat)
    for u in range(4):
        assert degree_within_two(u, units[2:])

    for z in range(1, 64):
        def derivative(x):
            return f(x) ^ f(x ^ z)
        polar_rows = [sum((derivative(a ^ b) ^ derivative(a) ^ derivative(b) ^ derivative(0)) << i
                          for i, b in enumerate(units)) for a in units]
        assert len(complete_basis([], polar_rows)) == 4

    # Gray-order search of all binary quadratics on six bits up to an output flip.
    terms = units + [a | b for i, a in enumerate(units) for b in units[:i]]
    truth_masks = [sum(int((x & t) == t) << x for x in range(64)) for t in terms]
    error_mask = sum(f(x) << x for x in range(64))
    best = abs(64 - 2 * error_mask.bit_count())
    for i in range(1, 1 << len(terms)):
        error_mask ^= truth_masks[(i & -i).bit_length() - 1]
        best = max(best, abs(64 - 2 * error_mask.bit_count()))
    assert best == 28

    for h in range(2):
        fibers = {}
        for x in range(64):
            u, v = x & 3, (x >> 2) & 3
            # z flips u's low bit. In these polynomial-basis coordinates one
            # dual coordinate of v is its low bit; w can be rebased implicitly.
            observations = (x >> 1, ((u & 1) * (v & 1)) if h else 0)
            votes = fibers.setdefault(observations, [0, 0])
            votes[f(x)] += 1
        assert min(map(sum, fibers.values())) >= 1
        assert sum(min(votes) for votes in fibers.values()) == (12 if h == 0 else 4)

    rng = Random(3321)
    lossy_count = 0
    for _ in range(500):
        masks = [rng.randrange(64) for _ in range(rng.randrange(3, 7))]
        phase = {i | k for i in [0] + units for k in [0] + units if rng.randrange(3) == 0}
        fibers = {}
        for x in range(64):
            observations = (linear_image(masks, x), evaluate(phase, x))
            votes = fibers.setdefault(observations, [0, 0])
            votes[f(x)] += 1
        if len(fibers) < 64:
            lossy_count += 1
            assert sum(min(votes) for votes in fibers.values()) >= 4
    assert lossy_count >= 300

    for x in range(64):
        u, v, w = x & 3, (x >> 2) & 3, x >> 4
        compressed = u | (mul(v, w) << 2)
        assert f(x) == f((compressed & 3) | ((compressed >> 2) << 2) | 16)



def trials():
    rng = Random(46531)
    for trial in range(1400):
        d = rng.randrange(1, 10)

        def table():
            r = rng.randrange(min(d, 6) + 1)
            return [rng.randrange(1 << d) for _ in range(r)], [rng.randint(-7, 7) for _ in range(1 << r)]

        left, right = table(), table()
        all_terms = [0] + [1 << i for i in range(d)]
        all_terms.extend((1 << i) | (1 << j) for i in range(d) for j in range(i))
        phase = {m for m in all_terms if rng.randrange(3) == 0}
        equations = [(rng.randrange(1 << d), rng.randrange(2)) for _ in range(rng.randrange(4))]
        expected = sum(sign(evaluate(phase, x)) * left[1][linear_image(left[0], x)]
                       * right[1][linear_image(right[0], x)] for x in range(1 << d)
                       if all(dot(x, m) == b for m, b in equations))
        assert contract(d, left, right, phase, equations) == expected, trial

    r, h = 7, 28
    d = 2 * (r + h)
    left = [1 << i for i in range(r)], [rng.randint(-5, 5) for _ in range(1 << r)]
    right = [1 << (r + i) for i in range(r)], [rng.randint(-5, 5) for _ in range(1 << r)]
    phase = {(1 << i) | (1 << (r + i)) for i in range(r)}
    phase.update(3 << (2 * (r + i)) for i in range(h))
    transformed = right[1].copy()
    walsh(transformed)
    expected = sum(x*y for x, y in zip(left[1], transformed)) << h
    assert contract(d, left, right, phase, []) == expected

    a, b = [0, 0, 1, 1], [0, 1, 0, 1]
    forged = [Fraction(-1, 2)] + [Fraction(1, 2)] * 3
    assert sum(z*(z-1) for z in forged) == 0
    assert sum(x*y - 2*x*z - 2*y*z + 3*z for x, y, z in zip(a, b, forged)) == 0
    assert forged != [x*y for x, y in zip(a, b)]
    cubic_trace_flats()
    print("1400 random contractions, a 70-bit cube, a fractional forgery, 126 GF(4) trace hyperplanes, all 63 derivative ranks, 500 observation maps and every six-bit quadratic up to sign passed.")


if __name__ == "__main__":
    trials()
