"""Integer checks of derivative compatibility and the adaptive bent strategy."""

from random import Random

from quadratic_trace_tables_audit import walsh


MODULI = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101}


def field(m):
    q = 1 << m

    def mul(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            a <<= 1
            if a & q:
                a ^= MODULI[m]
            b >>= 1
        return result

    table = [[mul(a, b) for b in range(q)] for a in range(q)]
    traces = []
    for a in range(q):
        total, power = 0, a
        for _ in range(m):
            total ^= power
            power = table[power][power]
        assert total in (0, 1) and power == a
        traces.append(total)
    return table, traces


def symplectic_pairs(m, phase):
    def polar(s, t):
        return phase[s] ^ phase[t] ^ phase[s ^ t]

    basis = [1 << i for i in range(m)]
    pairs = []
    while basis:
        candidate = next(((e, f) for e in basis for f in basis if polar(e, f)), None)
        if candidate is None:
            break
        e, f = candidate
        pairs.append((e, f))
        basis = [v ^ (e if polar(v, f) else 0) ^ (f if polar(v, e) else 0)
                 for v in basis if v not in (e, f)]
    for i, (e, f) in enumerate(pairs):
        for j, (u, v) in enumerate(pairs):
            assert polar(e, v) == (i == j)
            assert not polar(e, u) and not polar(f, v)
    return pairs


def check_strategies(m):
    q = 1 << m
    mul, tr = field(m)
    n = q ** 3
    truth = [tr[mul[mul[x & (q-1)][(x >> m) & (q-1)]][x >> (2*m)]]
             for x in range(n)]
    best_sum = 2*q*q - q
    assert sum(1-2*b for b in truth) == best_sum
    cubes = {mul[mul[s][s]][s] for s in range(q)}
    c = 1 if m & 1 else min(set(range(1, q)) - cubes)
    phase = [tr[mul[c][mul[mul[s][s]][s]]] for s in range(q)]
    pairs = symplectic_pairs(m, phase)
    assert len(pairs) == m // 2
    shifts = [s | (s << m) | (mul[c][s] << (2*m)) for s in range(q)]
    span = [0]
    for r in range(len(pairs) + 1):
        if r:
            e, f = pairs[r - 1]
            span = [v ^ w for w in (0, e, f, e ^ f) for v in span]
        total = 0
        for x in range(n):
            # A_i=D_e F and B_i=D_f F are each a single quadratic query.
            output = 0
            for e, f in pairs[:r]:
                a = truth[x ^ shifts[e]] ^ truth[x]
                b = truth[x ^ shifts[f]] ^ truth[x]
                output ^= a & b
            signed = 1 - 2 * output
            direct = sum(1 - 2 * (truth[x ^ shifts[s]] ^ truth[x]) for s in span)
            assert direct == (1 << r) * signed
            total += signed * (1 - 2 * truth[x])
        assert total == (1 << r) * best_sum
    # Use coset bits of the first input before the quadratic prediction on W.
    for r in range((m+1)//2, m+1):
        dimension_pairs = m-r
        subgroup = [0]
        for e, f in pairs[:dimension_pairs]:
            subgroup = [v ^ w for w in (0, e, f, e ^ f) for v in subgroup]
        representatives = [min(u ^ w for w in subgroup) for u in range(q)]
        total = 0
        for x in range(n):
            u, v, w = x & (q-1), (x >> m) & (q-1), x >> (2*m)
            rep = representatives[u]
            residual = x ^ rep
            output = tr[mul[mul[rep][v]][w]]
            for e, f in pairs[:dimension_pairs]:
                left = truth[residual ^ shifts[e]] ^ truth[residual]
                right = truth[residual ^ shifts[f]] ^ truth[residual]
                output ^= left & right
            total += 1 - 2 * (truth[x] ^ output)
        expected = q*q*(1 << r) + n//(1 << r) - q*(1 << r)
        assert total == expected
    # A nondeterministic certificate can verify two guessed bits per question.
    for actual in range(q):
        for guess in range(q):
            different = actual ^ guess
            outcomes = [int((different >> i) & 3 == 0) for i in range(0,m,2)]
            assert all(outcomes) == (actual == guess)
    return truth, mul, tr, len(pairs) + 1


def check_derivatives(m, truth, mul, tr, rng):
    q = 1 << m
    n = len(truth)
    masks = [1 << i for i in range(3*m)]
    masks += [(1 << i) | (1 << j) for i in range(3*m) for j in range(i)]
    for _ in range(14):
        terms = [mask for mask in masks if rng.randrange(2)]
        quadratic = [sum(x & t == t for t in terms) % 2 for x in range(n)]
        signed = [1-2*(a^b) for a, b in zip(truth, quadratic, strict=True)]
        transform = signed.copy()
        walsh(transform)
        squares = [c*c for c in transform]
        walsh(squares)
        assert all(v % n == 0 for v in squares)
        autocorr = [v // n for v in squares]
        assert sum(autocorr) == sum(signed)**2
        compatible_count = 0
        scalar_sums = [0] * q
        for z in range(n):
            u, v, w = z & (q-1), (z >> m) & (q-1), z >> (2*m)
            phase = []
            for t in range(q):
                tz = mul[t][u] | (mul[t][v] << m) | (mul[t][w] << (2*m))
                bq = quadratic[0] ^ quadratic[z] ^ quadratic[tz] ^ quadratic[z ^ tz]
                derivative = tr[mul[mul[t][t] ^ t][mul[mul[u][v]][w]]] ^ bq
                assert signed[0]*signed[z]*signed[tz]*signed[z ^ tz] == 1-2*derivative
                phase.append(1-2*derivative)
                scalar_sums[t] += phase[-1]
            compatible = all(v == 1 for v in phase)
            assert sum(phase) == q * compatible
            compatible_count += compatible
            if z:
                assert abs(autocorr[z]) == q*q * compatible
        assert q * compatible_count == sum(scalar_sums)
        assert all(abs(v) <= 2*q*q-q for v in scalar_sums[2:])
        assert abs(sum(signed)) <= 2*q*q-q
    return 14


if __name__ == "__main__":
    rng = Random(34571)
    strategy_count = derivative_count = 0
    for bits in MODULI:
        truth, mul, tr, count = check_strategies(bits)
        strategy_count += count
        if bits <= 3:
            derivative_count += check_derivatives(bits, truth, mul, tr, rng)
    print(f"{strategy_count} exact optimal-strategy sums over GF(2) through GF(32)")
    print(f"{derivative_count} complete shift and scalar moment tables verified")
    print("Large-depth conditional strategies and paired teacher certificates checked through GF(32)")
