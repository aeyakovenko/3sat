"""Exact finite checks for trace-product table cost and stabilizer overlap."""

from itertools import combinations, product
from random import Random

from quadratic_trace_tables_audit import dot, linear_image, walsh
from trace_product_bias_audit import field


def trace_signs(m):
    mul, trace = field(m)
    q = 1 << m
    return [
        1 - 2 * trace[mul[mul[u][v]][w]]
        for w, v, u in product(range(q), repeat=3)
    ]


def quadratic(tableau, x):
    return dot(tableau[0], x) ^ sum(
        (x >> i & 1) * dot(mask, x) for i, mask in enumerate(tableau[1:])
    ) % 2


def check_blocks(m, trials, rng):
    f = trace_signs(m)
    n = len(f)
    d = 3 * m
    q = 1 << m
    max_sum = (2 * q - 1) * q
    assert sum(f) == max_sum
    # The full derivative mixture has the smallest possible absolute mass.
    # Check all translations at small m, and a range of basepoints thereafter.
    basepoints = range(n) if m < 3 else rng.sample(range(n), 32)
    for x in basepoints:
        assert sum(f[x] * f[x ^ z] for z in range(n)) == f[x] * max_sum

    mul, trace = field(m)
    for x, expected in enumerate(f):
        u, v, w = x % q, x // q % q, x // (q * q)
        received = sum(
            (u == a) * (1 - 2 * trace[mul[mul[a][v]][w]]) for a in range(q)
        )
        assert expected == received

    for _ in range(trials):
        observations = [rng.randrange(n) for _ in range(rng.randrange(d + 1))]
        guards = [(rng.randrange(n), rng.randrange(2)) for _ in range(rng.randrange(4))]
        phase = [rng.randrange(n) for _ in range(d + 1)]
        size = 2 << len(observations)
        table = [rng.randrange(-12, 13) for _ in range(size)]
        coefficients = table.copy()
        walsh(coefficients)
        table_square_sum = sum(a * a for a in table)
        assert sum(c * c for c in coefficients) == size * table_square_sum
        total = 0
        for x in range(n):
            if all(dot(mask, x) == bit for mask, bit in guards):
                key = 2 * linear_image(observations, x) + quadratic(phase, x)
                total += f[x] * table[key]
        assert abs(total) * size <= max_sum * sum(abs(c) for c in coefficients)
        assert total * total <= max_sum * max_sum * table_square_sum


def check_stabilizers_on_three_bits():
    n = 8
    f = trace_signs(1)
    # Generate all affine subspaces by closing singleton sets under translation.
    flats = {frozenset({x}) for x in range(n)}
    for _ in range(3):
        flats.update(
            support | {x ^ v for x in support}
            for support in tuple(flats) for v in range(n)
        )
    best = (0, 1)
    phases = set()
    for linear in range(n):
        for pair_mask in range(8):
            pairs = [3, 5, 6]
            phases.add(tuple(
                dot(linear, x) ^ (sum(
                    (pair_mask >> i & 1) * ((x & pair) == pair)
                    for i, pair in enumerate(pairs)
                ) % 2) for x in range(n)
            ))
    for support, phase, ell in product(flats, phases, range(n)):
        real = imag = 0
        for x in support:
            sign = f[x] * (1 - 2 * phase[x])
            if dot(ell, x):
                imag += sign
            else:
                real += sign
        top, bottom = real * real + imag * imag, n * len(support)
        assert top * n <= bottom * sum(f)
        if top * best[1] > best[0] * bottom:
            best = top, bottom
    # For CCZ the known stabilizer fidelity is 9/16.
    assert 16 * best[0] == 9 * best[1]


def linear_spaces(d):
    """Enumerate binary subspaces once via reduced row-echelon bases."""
    for rank in range(d + 1):
        for pivots in combinations(range(d), rank):
            free = [(i, c) for i, p in enumerate(pivots)
                    for c in range(p + 1, d) if c not in pivots]
            for mask in range(1 << len(free)):
                basis = [1 << p for p in pivots]
                for j, (i, c) in enumerate(free):
                    if mask & (1 << j):
                        basis[i] |= 1 << c
                space = [0]
                for b in basis:
                    space += [x ^ b for x in space]
                yield basis, frozenset(space)


def check_fidelity_over_four():
    # Hadamards on the third register turn the trace-product state into
    # the uniform superposition on the graph of multiplication in dual bases.
    # A linear basis change recovers ordinary field coordinates. All graph
    # amplitudes are positive, so the best phase on each support is constant.
    q = 4
    n = q**3
    mul, _ = field(2)
    graph = {u + q*v + q*q*mul[u][v] for u, v in product(range(q), repeat=2)}
    truth = trace_signs(2)
    best = (0, 1)
    n_flats = planes = 0
    for basis, space in linear_spaces(6):
        unseen = set(range(n))
        while unseen:
            origin = min(unseen)
            flat = {origin ^ x for x in space}
            unseen -= flat
            score, normalization = len(flat & graph)**2, q*q*len(flat)
            if score * best[1] > best[0] * normalization:
                best = score, normalization
            n_flats += 1
        if len(basis) != 4:
            continue
        # A full-dimensional equality support for the original phase must
        # have zero third derivatives, independent of the translate.
        restricted_quadratic = all(
            truth[a] * truth[b] * truth[c] * truth[a^b] * truth[a^c] *
            truth[b^c] * truth[a^b^c] * truth[0] == 1
            for a, b, c in combinations(basis, 3)
        )
        k_linear = all(
            mul[2][x % q] + q*mul[2][x // q % q] + q*q*mul[2][x // (q*q)] in space
            for x in basis
        )
        assert restricted_quadratic == k_linear
        planes += k_linear
    assert n_flats == 26387
    assert planes == q*q + q + 1
    assert q * best[0] == best[1]


if __name__ == "__main__":
    random = Random(710391)
    for m in (1, 2, 3):
        check_blocks(m, 150, random)
    check_stabilizers_on_three_bits()
    check_fidelity_over_four()
    print("Exact table, derivative, and stabilizer checks passed.")
