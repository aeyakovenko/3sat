"""Finite tests for actual field normalizations, noisy symbols and anchor filtering."""
from collections import Counter
from itertools import product
from random import Random


# Binary polynomial basis modulo 1+u+u^2+u^3+u^4.
def binary_product(x, y):
    z = 0
    while y:
        if y & 1:
            z ^= x
        x <<= 1
        if x & 16:
            x ^= 31
        y //= 2
    return z


MUL = [[binary_product(x, y) for y in range(16)] for x in range(16)]
INV = {x: MUL[x].index(1) for x in range(1, 16)}
ROOTS = [1, 2, 4, 8, 15]


def field_power(x, e):
    result = 1
    for _ in range(e % 15):
        result = MUL[result][x]
    return result


def combine(values):
    value = 1
    for z in values:
        value = MUL[value][z]
    return value


# K = F_25 in basis 1,z modulo z^2-2.
def extension_product(a, b):
    x, y = a % 5, a // 5
    s, t = b % 5, b // 5
    return (x * s + 2 * y * t) % 5 + 5 * ((x * t + s * y) % 5)


ADD = [[(a % 5 + b % 5) % 5 + 5 * ((a // 5 + b // 5) % 5)
        for b in range(25)] for a in range(25)]
PROD = [[extension_product(a, b) for b in range(25)] for a in range(25)]
NEG = [ADD[a].index(0) for a in range(25)]
DIV = {a: PROD[a].index(1) for a in range(1, 25)}
DUAL = [[(a % 5 * (b % 5) + a // 5 * (b // 5)) % 5
         for b in range(25)] for a in range(25)]


def lagrange(i, point):
    z = 1
    for j, p in enumerate(reversed(point)):
        z = PROD[z][p if (i >> j) & 1 else ADD[1][NEG[p]]]
    return z


def message_at(bits, point):
    z = 0
    for i, value in enumerate(bits):
        if value:
            z = ADD[z][lagrange(i, point)]
    return z


def point_for(e):
    return MUL[ROOTS[e]][INV[1 ^ ROOTS[e]]]


def choose_exponent(c, upper):
    b = 2 if c == 4 else 1
    return (b + c) % 5 if upper else b


def normalization(v, p, dual, upper):
    """Truncated-grid histogram via digit DP, compared with naive products."""
    bound = v - 1
    rows = Counter({(True, 1): 1})
    for j, a in enumerate(p):
        limit = (bound >> (len(p) - j - 1)) & 1
        following = Counter()
        for (equal, z), count in rows.items():
            for digit, factor in enumerate([ADD[1][NEG[a]], a]):
                if equal and digit > limit:
                    continue
                key = (equal and digit == limit, PROD[z][factor])
                following[key] = (following[key] + count) % 15
        rows = following
    return combine(field_power(1 ^ point_for(choose_exponent(DUAL[dual][z], upper)), k)
                   for (_, z), k in rows.items())


def hole_indicator_at(hole, ts):
    return combine(t if bit else 1 ^ t for bit, t in zip(hole, ts, strict=True))


def canonical_positive(holes, ts, full=False):
    if not full:
        total = 1
        for hole in holes:
            total ^= hole_indicator_at(hole, ts)
        return total
    total = 0
    for assignment in product(range(2), repeat=len(ts)):
        if assignment not in holes:
            total ^= hole_indicator_at(assignment, ts)
    return total


def check_fields():
    rng = Random(14623)
    tests = full_tests = 0
    for trial in range(1700):
        v = rng.randrange(2, 12)
        tag = rng.randrange(v)
        bits = [rng.randrange(2) for _ in range(v)]
        bits[tag] = 0
        holes = [tuple(bits)]
        if rng.randrange(2):
            other = [rng.randrange(2) for _ in range(v)]
            other[tag] = 1
            holes.append(tuple(other))
        dim = (v - 1).bit_length()
        p, dual = [rng.randrange(25) for _ in range(dim)], rng.randrange(25)
        digits = [DUAL[dual][lagrange(i, p)] for i in range(v)]
        unshifted_roots = []
        for upper in (False, True):
            base = [choose_exponent(c, upper) for c in digits]
            normal = normalization(v, p, dual, upper)
            pair = []
            g = 2 if base[tag] == 4 else 1
            for shift in (False, True):
                e = base.copy()
                if shift:
                    e[tag] = (e[tag] + g) % 5
                ts = [point_for(a) for a in e]
                assert all(t not in (0, 1) for t in ts)
                denominator = normal
                if shift:
                    denominator = MUL[MUL[normal][INV[1 ^ point_for(base[tag])]]][1 ^ ts[tag]]
                assert denominator == combine(1 ^ t for t in ts)
                value = canonical_positive(holes, ts)
                if v <= 7 and trial < 300:
                    assert canonical_positive(holes, ts, True) == value
                    full_tests += 1
                pair.append(MUL[1 ^ value][INV[denominator]])
                # Fixed scalar, equal-bit copies and pinned zero padding.
                scalar = point_for(1)
                copied = [tuple(bit if j < weight else 0
                                for bit, weight in zip(word, e) for j in range(5))
                          for word in holes]
                scalar_val = canonical_positive(copied, [scalar] * (5 * v))
                assert MUL[scalar_val ^ 1][INV[field_power(1 ^ scalar, 5 * v)]] == pair[-1]
                tests += 1
            y = MUL[pair[0] ^ pair[1]][INV[1 ^ ROOTS[g]]]
            unshifted_roots.append(pair[0] ^ y)
        symbol = MUL[unshifted_roots[1]][INV[unshifted_roots[0]]]
        assert symbol == ROOTS[DUAL[dual][message_at(bits, p)]]
        copy_weight = sum(bit * (c or 5) for bit, c in zip(bits, digits))
        assert ROOTS[copy_weight % 5] == symbol
    return tests, full_tests


def line_value(coefficients, x):
    total = 0
    for a in reversed(coefficients):
        total = ADD[a][PROD[x][total]]
    return total


def solve(rows, variables):
    """One solution to a consistent rectangular linear system over K."""
    rows = [r[:] for r in rows]
    pivots = []
    for column in range(variables):
        i = len(pivots)
        pivot = next((j for j in range(i, len(rows)) if rows[j][column]), None)
        if pivot is None:
            continue
        rows[i], rows[pivot] = rows[pivot], rows[i]
        rows[i] = [PROD[x][DIV[rows[i][column]]] for x in rows[i]]
        for j, row in enumerate(rows):
            if j != i and row[column]:
                multiplier = NEG[row[column]]
                rows[j] = [ADD[x][PROD[multiplier][y]] for x, y in zip(row, rows[i])]
        pivots.append(column)
    assert all(not any(r[:-1]) and not r[-1] for r in rows[len(pivots):])
    result = [0] * variables
    for i, p in enumerate(pivots):
        result[p] = rows[i][-1]
    return result


def check_noisy_lines():
    rng = Random(2569)
    count = 0
    for _ in range(96):
        d = rng.randrange(1, 5)
        e = rng.randrange(0, 7)
        coeff = [rng.randrange(25) for _ in range(d + 1)]
        errors = set(rng.sample(range(1, 25), e))
        system = []
        for t in range(1, 25):
            symbol = line_value(coeff, t)
            if t in errors:
                symbol = ADD[symbol][rng.randrange(1, 25)]
            powers = [1]
            for _ in range(d + e):
                powers.append(PROD[t][powers[-1]])
            system.append(powers + [NEG[PROD[symbol][x]] for x in powers[:e]]
                          + [PROD[symbol][powers[e]]])
        sol = solve(system, d + 1 + 2 * e)
        top, loc = sol[:d + e + 1], sol[d + e + 1:] + [1]
        for t in range(25):
            assert line_value(top, t) == PROD[line_value(loc, t)][line_value(coeff, t)]
            count += 1
    for a in range(25):
        for b in range(a):
            assert sum(DUAL[k][a] != DUAL[k][b] for k in range(25)) == 20
            count += 1
    return count


def check_advised_lines():
    # Deliberately include line words for which the actual line is absent.
    # For quadratics over F5, enumerate exact lists and all possible anchors.
    rng = Random(6827)
    values = {
        p: tuple((p[0] + p[1] * x + p[2] * x * x) % 5 for x in range(5))
        for p in product(range(5), repeat=3)
    }
    checks = misses = 0
    for _ in range(300):
        message = rng.choice(list(values.values()))
        received = tuple(rng.randrange(5) for _ in range(5))
        candidates = [v for v in values.values() if sum(a == b for a, b in zip(v, received)) >= 4]
        others = [v for v in candidates if v != message]
        bad = sum(any(v[t] == message[t] for v in others) for t in range(1, 5))
        assert bad <= 2 * len(others)
        if message not in candidates:
            misses += 1
        checks += 4
    assert misses > 0
    return checks



def curve_audit():
    # Scalar K_a samples factor coordinatewise for vectors; also test that
    # deleting parameter zero leaves the advised parameter uniform.
    point_pairs = 0
    anchor_tuples = 0
    for x in [0, 7, 19]:
        for t in range(1, 25):
            tsq = PROD[t][t]
            parameters = [p for p in range(1, 25) if p != t]
            curves = [(a, b, ADD[x][ADD[PROD[a][t]][PROD[b][tsq]]])
                      for a, b in product(range(25), repeat=2)]
            for u in parameters:
                u2 = PROD[u][u]
                outcomes = {(z, ADD[x][ADD[PROD[a][u]][PROD[b][u2]]])
                            for a, b, z in curves}
                assert len(outcomes) == 25 ** 2
                point_pairs += len(outcomes)
            for a, b, z in curves:
                advised = PROD[ADD[ADD[z][NEG[x]]][NEG[PROD[b][tsq]]]][DIV[t]]
                assert advised == a
                anchor_tuples += 1
    return point_pairs, anchor_tuples


def soft_score_audit():
    # Over F5, use the normalized score times 4q. Check Parseval's bound,
    # interpolation cost and the filtered-list Gram inequality independently.
    rng = Random(15373)
    q = 5
    polynomials = [tuple((a + b*t) % q for t in range(q))
                   for a, b in product(range(q), repeat=2)]
    checks = 0
    for _ in range(500):
        scores = []
        for t in range(q):
            guesses = [rng.randrange(q) for lam in range(q)]
            row = [5 * sum(guesses[lam] == (lam * z) % q for lam in range(q)) - q
                   for z in range(q)]
            assert sum(c*c for c in row) <= (4*q)**2
            scores.append(row)
        multiplicities = [max(0,c) // 4 for row in scores for c in row]
        assert sum(m*(m+1)//2 for m in multiplicities) <= q**3
        for threshold in [5,10,15]:
            selected = [p for p in polynomials
                        if sum(scores[t][p[t]] for t in range(q)) >= threshold*q]
            n = len(selected)
            assert (n * threshold)**2 * q <= (4*q)**2 * (n*q + n*(n-1))
            checks += 1
    return checks


def binary_fixed_scalar_audit():
    def diagram_value(bits, challenges, mask=None):
        padding = (-len(bits)) % 4
        hole = [x for h, c in zip(bits, challenges, strict=True)
                for x in (h, 1-h, c*h, c*h)]
        hole += [1, 0, 0, 0] * padding
        if mask is not None:
            hole += [mask, mask, 0, 0]
        indicator = 1
        for bit in hole:
            indicator = indicator * (-1 if bit else 2) % 5
        return (1-indicator) % 5

    tests = 0
    for v in range(1, 6):
        for h in product(range(2), repeat=v):
            for c in product(range(2), repeat=v):
                b = sum(u*w for u, w in zip(h, c, strict=True)) % 2
                assert diagram_value(h, c) == 2*b
                answers = [diagram_value(h, c, mask) for mask in (0, 1)]
                assert answers == [2*b, 2*(b ^ 1)]
                tests += 1

    rng = Random(17019)
    for _ in range(500):
        v = rng.randrange(1, 40)
        point = [rng.randrange(16) for _ in range((v-1).bit_length())]
        dual = rng.randrange(16)
        h = [rng.randrange(2) for _ in range(v)]
        lags = [combine(x if (i >> k) & 1 else (1 ^ x)
                        for k, x in enumerate(point)) for i in range(v)]
        p_value = 0
        for lag, bit in zip(lags, h, strict=True):
            if bit:
                p_value ^= lag
        challenges = [(dual & lag).bit_count() % 2 for lag in lags]
        assert diagram_value(h, challenges) == 2*((dual & p_value).bit_count() % 2)
        tests += 1
    return tests


if __name__ == "__main__":
    mixed, full = check_fields()
    print(f"{mixed} mixed/fixed normalizations, {full} full Boolean multilinear sums")
    print(f"{check_noisy_lines()} noisy line and inner-word checks")
    print(f"{check_advised_lines()} advised anchor checks including bad lines")
    pairs, anchors = curve_audit()
    print(f"{pairs:,} pairwise-independent curve images, {anchors:,} advice reconstructions")
    print(f"{soft_score_audit()} soft-score list/constraint bounds")
    print(f"{binary_fixed_scalar_audit()} binary five-field fixed-scalar checks")
