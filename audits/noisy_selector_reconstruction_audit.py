"""Finite checks of transport recognition, noisy scalar products and field recovery."""
from random import Random
import numpy as np
from scipy.optimize import linear_sum_assignment


Q = 128
DEGREE = 7
MODULUS = 0x83   # X^7 + X + 1


def mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & Q:
            a ^= MODULUS
    return result


def power(a, index):
    result = 1
    while index:
        if index & 1:
            result = mul(result, a)
        index >>= 1
        a = mul(a, a)
    return result


def trace(a):
    val = 0
    for _ in range(DEGREE):
        val ^= a
        a = mul(a, a)
    assert val in (0, 1)
    return val


def subset_products(ratios):
    vals = [1]
    for r in ratios:
        vals += [mul(v, r) for v in vals]
    return vals


def linear(coords, basis):
    val = 0
    for i, elem in enumerate(basis):
        if coords >> i & 1:
            val ^= elem
    return val


def composition(a, b):
    return tuple(linear(col, a) for col in b)


def min_matching_cost(dataset, term, precomputed):
    # Translation-invariant Hamming costs on a uniform empirical sample.
    cost = np.fromiter(((x ^ term).bit_count() for x in precomputed), dtype=np.int64,
                       count=len(precomputed)).reshape(len(dataset),len(dataset))
    rows, cols = linear_sum_assignment(cost)
    return int(cost[rows, cols].sum())


def group_coordinates(representatives):
    count = len(representatives)

    def nearest(v):
        return min(representatives, key=lambda u: (u ^ v).bit_count())

    zero = nearest(0)
    span = [zero]
    for r in representatives:
        if r not in span:
            span += [nearest(r ^ u) for u in span]
    assert len(span) == count == len(set(span))
    coordinate = {r:i for i,r in enumerate(span)}
    for i, x in enumerate(span):
        for j, y in enumerate(span):
            assert nearest(x ^ y) == span[i ^ j]
    return coordinate, nearest


def decode_matrices(pairs):
    # Each pair is two decoded class vectors (possibly corrupted).
    columns = [0] * DEGREE
    for outbit in range(DEGREE):
        best = min(range(Q), key=lambda a: sum(
            ((a & x).bit_count() ^ (y >> outbit)) & 1 for x, y in pairs))
        for i in range(DEGREE):
            columns[i] |= ((best >> i) & 1) << outbit
    return tuple(columns)


def recovered_ratios(matrices):
    identity = tuple(1 << i for i in range(DEGREE))
    group = {identity}
    queue = [identity]
    for x in queue:
        for m in matrices:
            new = composition(m, x)
            if new not in group:
                group.add(new)
                queue.append(new)
        assert len(group) <= Q-1
    assert len(group) == Q-1
    for generator in queue:
        powers = [identity]
        cursor = composition(generator, identity)
        while cursor != identity:
            powers.append(cursor)
            cursor = composition(generator, cursor)
        if len(powers) == Q-1:
            break
    scalar_orbit = [p[0] for p in powers[:DEGREE+1]]
    coeff = next(i for i in range(Q) if linear(i, scalar_orbit[:-1]) == scalar_orbit[-1])
    roots = [a for a in range(1,Q) if power(a,DEGREE) == linear(coeff, [power(a,k) for k in range(DEGREE)])]
    assert len(roots) == DEGREE
    return [power(min(roots), powers.index(m)) for m in matrices]


def audit():
    rng = Random(59)
    logs = [power(2, i) for i in range(Q-1)]
    assert len(set(logs)) == Q-1
    anchor = [rng.choice(logs[1:]) for _ in range(10)]
    outside = [rng.choice(logs[1:]) for _ in range(13)]
    scale = rng.choice(logs)
    h = subset_products(anchor)
    z = [mul(scale, v) for v in subset_products(outside)]
    width = len(h)
    code = [sum(trace(mul(a,c)) << i for i,c in enumerate(h)) for a in range(Q)]
    assert min(c.bit_count() for c in code[1:]) > .43*width
    address = {}
    for y,val in enumerate(z):
        address.setdefault(val, []).append(y)
    assert len(address) == Q-1

    def observed(y):
        # A fixed correlated error pattern, including a small set of bad entire rows.
        err = ((1 << width)-1) if y % 2048 == 0 else 1 << (y*117 % width) if y & 1 else 0
        return code[z[y]] ^ err

    assert sum((observed(y)^code[val]).bit_count() for y,val in enumerate(z))*256 < len(z)*width
    # Finite calibration: stratify by the clean scalar solely to ensure a small
    # empirical distribution. The theorem's actual algorithm samples without it.
    obs_data = [observed(rng.choice(address[a])) for a in logs]
    precomputed = [a ^ b for a in obs_data for b in obs_data]
    reps = []
    trials = matched = 0
    while len(reps) < Q and trials < 8000:
        trials += 1
        word = observed(rng.randrange(len(z))) ^ observed(rng.randrange(len(z)))
        if any((word^r).bit_count() < .15*width for r in reps):
            continue
        cost = min_matching_cost(obs_data, word, precomputed)
        matched += 1
        if cost*1000 <= 36*len(obs_data)*width:
            reps.append(word)
    assert len(reps) == Q
    for _ in range(8):
        junk = rng.getrandbits(width)
        assert min_matching_cost(obs_data, junk, precomputed)*1000 > 36*len(obs_data)*width

    coordinate, nearest = group_coordinates(reps)
    def read(y):
        return coordinate[nearest(observed(y))]
    matrices = []
    for i in range(len(outside)):
        pairs = []
        for _ in range(220):
            y = rng.randrange(len(z)) & ~(1 << i)
            pairs.append((read(y), read(y | (1<<i))))
        matrices.append(decode_matrices(pairs))
    ratios = recovered_ratios(matrices)
    sigma = next(t for t in range(DEGREE) if ratios == [power(r,1<<t) for r in outside])
    # Reverse-block scalar decoding against sampled outside addresses. Native
    # output never appears in these observations.
    products = subset_products(ratios)
    ts = [trace(x) for x in range(Q)]
    def reversed_row(u):
        samples = [rng.randrange(len(z)) for _ in range(260)]
        bits = [(observed(y) >> u) & 1 for y in samples]
        return min(range(Q), key=lambda c: sum(
            ts[mul(c, products[y])] != bit for y,bit in zip(samples,bits)))
    zero = reversed_row(0)
    decoded_anchor = [mul(reversed_row(1<<i), power(zero,Q-2)) for i in range(len(anchor))]
    assert zero == power(scale,1<<sigma)
    assert decoded_anchor == [power(r,1<<sigma) for r in anchor]
    return dict(field_size=Q, headerless_ratios=len(outside)+len(anchor),
                transport_evaluations=matched+8, tests_of_group_addition=Q**2,
                candidate_trials=trials, fixed_corruption_below='1/256',
                Frobenius_power=sigma)


if __name__ == '__main__':
    print(audit())
