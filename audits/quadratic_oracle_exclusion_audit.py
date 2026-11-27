"""Small exact checks for degree-two extension queries. No external packages."""
from itertools import combinations_with_replacement, permutations, product
from math import prod
from random import Random


def basis(rows, p):
    """Unique reduced basis of the given row span over the prime field."""
    pivots = {}
    for row in rows:
        v = [c % p for c in row]
        for j, w in sorted(pivots.items()):
            if v[j]:
                a = v[j]
                v = [(b-a*d) % p for b, d in zip(v, w)]
        j = next((j for j, c in enumerate(v) if c), None)
        if j is None:
            continue
        inv = pow(v[j], -1, p)
        v = [a*inv % p for a in v]
        for k, w in list(pivots.items()):
            a = w[j]
            pivots[k] = [(b-a*d) % p for b, d in zip(w, v)]
        pivots[j] = v
    return tuple(tuple(v) for _, v in sorted(pivots.items()))


def mul(a, b, p):
    return tuple(x*y % p for x, y in zip(a, b))


def update(V, I, z, p):
    z2 = mul(z, z, p)
    defect = tuple((a-b) % p for a, b in zip(z2, z))
    return (basis([*V, *(mul(z, v, p) for v in V), *(mul(z2, v, p) for v in V)], p),
            basis([*I, *(mul(z, v, p) for v in I), *(mul(defect, v, p) for v in V)], p))


def values(points, exponents, p):
    return tuple(prod(pow(x, a, p) for x, a in zip(y, exponents)) % p for y in points)


def spaces(points, p):
    h, i = len(points[0]), len(points)
    V, I = basis([(1,)*i], p), ()
    kept = []
    for j, z in enumerate(zip(*points)):
        v, u = update(V, I, z, p)
        if (v, u) != (V, I):
            kept.append(j)
            V, I = v, u
    assert len(kept) <= 2*i-1
    cols, diffs = [], []
    for a in product(range(3), repeat=h):
        col = values(points, a, p)
        flat = values(points, tuple(min(x, 1) for x in a), p)
        cols.append(col)
        diffs.append(tuple((x-y) % p for x, y in zip(col, flat)))
    assert (V, I) == (basis(cols, p), basis(diffs, p))
    return I


def delta(u, y, p):
    return prod(x if b else 1-x for x, b in zip(y, u)) % p


def supports_and_replies():
    p = 3
    cube = list(product(range(2), repeat=2))
    points = list(product(range(p), repeat=2))
    tables = list(product(range(2), repeat=len(cube)))
    families = 0
    for k in (1, 2, 3, 4):
        for ys in combinations_with_replacement(points, k):
            I = spaces(ys, p)
            deltas = [[delta(u, y, p) for y in ys] for u in cube]
            relations = []
            for lam in product(range(p), repeat=k):
                if any(sum(a*b for a, b in zip(col, lam)) % p for col in I):
                    continue
                weights = [sum(a*b for a, b in zip(d, lam)) % p for d in deltas]
                assert sum(w != 0 for w in weights) <= k
                for u, du in enumerate(deltas):
                    for v, dv in enumerate(deltas):
                        assert sum(w*x*y for w, x, y in zip(lam, du, dv)) % p == (weights[u] if u == v else 0)
                relations.append((lam, weights))
            feasible_offsets = {tuple(sum(a*b for a, b in zip(coeff, col)) % p for col in zip(*I))
                                for coeff in product(range(p), repeat=len(I))} if I else {(0,)*k}
            for b in tables:
                base = tuple(sum(x*d[j] for x, d in zip(b, deltas)) % p for j in range(k))
                # Test the just-forced or free reply on a feasible prefix.
                prefix = base[:-1]
                feasible = { (base[-1]+off[-1]) % p for off in feasible_offsets if not any(off[:-1]) }
                predicted = set(range(p))
                for lam, weights in relations:
                    if lam[-1]:
                        rhs = sum(w*x for w, x in zip(weights,b))-sum(a*x for a,x in zip(lam,prefix))
                        predicted &= {rhs*pow(lam[-1], -1, p) % p}
                assert feasible == predicted
                families += 1
    rng = Random(318)
    for _ in range(140):
        k = rng.randrange(1, 5)
        spaces([tuple(rng.randrange(5) for _ in range(5)) for _ in range(k)], 5)
    return families


def poly_mul(a, b, p):
    d = len(a)
    return [sum(a[j]*b[i-j] for j in range(i+1)) % p for i in range(d)]


def cycle(perm):
    j, count = perm[0], 1
    while j:
        j = perm[j]
        count += 1
    return count == len(perm)


def truncated_odds():
    rng = Random(19)
    total = 0
    for m in (2, 3, 4):
        for p in (2, 3, 5, 7):
            one = [1]+[0]*m
            for _ in range(8):
                x = [rng.randrange(p) for _ in range(m*m)]
                z = [[0]+[(-1)**(i-1)*a**i % p for i in range(1,m+1)] for a in x]
                absent = [[(v-w) % p for v,w in zip(one, val)] for val in z]
                denom = one
                for a in x:
                    denom = poly_mul(denom, [1,a]+[0]*(m-1), p)
                for only_cycles in (False, True):
                    mass, formal = [0]*(m+1), 0
                    for perm in permutations(range(m)):
                        if only_cycles and not cycle(perm):
                            continue
                        term = one
                        formal += prod(x[i*m+v] for i,v in enumerate(perm))
                        for k in range(m*m):
                            factor = z[k] if perm[k//m] == k % m else absent[k]
                            term = poly_mul(term, factor, p)
                        mass = [(v+w) % p for v,w in zip(mass,term)]
                    assert poly_mul(mass,denom,p) == [0]*m+[formal % p]
                    total += 1
    return total


def corrupted_bank_queries():
    """Use a single polynomial perturbation across all calls in each trial."""
    rng = Random(419)
    p = 101
    trials = 0
    for errors in range(4):
        banks = 2 * errors + 1
        for _ in range(50):
            entries = [rng.randrange(p - 1) for _ in range(4)]
            denominators = [(1 + x) % p for x in entries]
            z = [x * pow(d, -1, p) % p for x, d in zip(entries, denominators)]
            permanent = (entries[0] * entries[3] + entries[1] * entries[2]) % p
            # The last physical coordinate is syntax, fixed to one in all calls.
            width = 4 * banks + 1
            errors_at = [rng.randrange(width) for _ in range(errors)]
            forms = [[rng.randrange(p) for _ in range(width)] for _ in errors_at]
            answers = []
            for active in range(banks):
                point = [0] * (4 * banks) + [1]
                point[4 * active:4 * (active + 1)] = z
                none = 1
                for b in range(banks):
                    a, e, c, d = point[4 * b:4 * (b + 1)]
                    is_perm = a * (1 - e) * (1 - c) * d + (1 - a) * e * c * (1 - d)
                    none = none * (1 - is_perm) % p
                answer = 1 - none
                for k, form in zip(errors_at, forms):
                    dense = 1 + sum(c * x for j, (c, x) in enumerate(zip(form, point)) if j != k)
                    answer += (point[k] ** 2 - point[k]) * dense
                answers.append(answer * prod(denominators) % p)
            assert answers.count(permanent) >= errors + 1
            trials += 1
    return trials


if __name__ == "__main__":
    print(f"{supports_and_replies()} Boolean-table transcripts passed")
    print(f"{truncated_odds()} truncated permanent and cycle identities passed")
    print(f"{corrupted_bank_queries()} shared polynomial corruption trials passed")
