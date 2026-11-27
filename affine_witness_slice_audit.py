"""Finite independent checks for the cubing-graph DIMACS address construction."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from random import Random


def remainder(f, divisor):
    while f.bit_length() >= divisor.bit_length():
        f ^= divisor << (f.bit_length() - divisor.bit_length())
    return f


@lru_cache(None)
def modulus(degree):
    # Brute force is confined to the finite audit.
    for p in range((1 << degree) + 1, 2 << degree, 2):
        if all(remainder(p, d) for k in range(1, degree // 2 + 1)
               for d in range(1 << k, 2 << k)):
            return p
    raise AssertionError(degree)


def mult(x, y, p):
    value = 0
    while y:
        if y & 1:
            value ^= x
        x <<= 1
        y >>= 1
    return remainder(value, p)


@lru_cache(None)
def cubes(a):
    p = modulus(a)
    return tuple(mult(mult(x, x, p), x, p) for x in range(1 << a))


@lru_cache(None)
def regions(ell):
    result = []
    for b in range(1, 1+ell//2):
        k = b.bit_length()-1
        c = 2*k+1
        if 2*b+c > ell:
            continue
        tag = (((1 << k)-1) << (k+1)) | (b ^ (1 << k))
        start = tag << (ell-c)
        result.append((start, 1 << (ell-c), b, ell-c-b))
    return result


def params(ell, index):
    for start, size, b, a in regions(ell):
        if start <= index < start+size:
            return b, a
    return 0, 0


def row_image(ell, i):
    b, a = params(ell, i)
    if not b:
        return i, False
    x = i & ((1 << a) - 1)
    z = (i >> a) & ((1 << b) - 1)
    return i ^ ((cubes(a)[x] & ((1 << b) - 1)) << a), z == 0


def model(ell, u):
    b, a = params(ell, u)
    if not b:
        return False
    x = u & ((1 << a) - 1)
    y = (u >> a) & ((1 << b) - 1)
    return y == (cubes(a)[x] & ((1 << b) - 1))


def physical(ell):
    v = 1 << ell
    length = 1 << (ell + 12).bit_length()
    header = f"p cnf 1{'1' * ell} {v+7}\n"
    anchors = []
    for forbidden in product((0, 1), repeat=3):
        if any(forbidden):
            clause = tuple(-i if bit else i for i, bit in enumerate(forbidden, 1))
            anchors.append(clause)
            header += " ".join(map(str, clause)) + " 0\n"
    prefix = header.encode().ljust(v*length, b" ")
    assert len(prefix) == v*length
    rows = []
    for i in range(v):
        u, positive = row_image(ell, i)
        line = f"{' ' if positive else '-'}1{u:0{ell}b} 1 2 0\n".encode()
        rows.append(line.ljust(length, b" "))
    raw = prefix + b"".join(rows)
    tokens = raw.split()
    assert tokens[:2] == [b"p", b"cnf"] and int(tokens[3]) == v+7
    tokens = list(map(int, tokens[4:]))
    assert len(tokens) == 4*(v+7) and all(x == 0 for x in tokens[3::4])
    clauses = list(zip(tokens[0::4], tokens[1::4], tokens[2::4]))
    assert clauses[:7] == anchors
    assert [x for x in product((0, 1), repeat=3)
            if all(any(x[abs(l)-1] == (l > 0) for l in C) for C in anchors)] == [(0, 0, 0)]
    pins = {}
    for literal, u, v_ in clauses[7:]:
        assert (u, v_) == (1, 2)
        name = str(abs(literal))
        assert name[0] == "1" and len(name) == ell+1
        index = int(name[1:], 2)
        assert index not in pins
        pins[index] = literal > 0
    assert all(pins[x] == model(ell, x) for x in range(v))

    # In each tag, replace the sign by a constant. The remaining whole-row
    # integer has algebraic degree <= 2 in its free high-address variables.
    for start, span, b, a in regions(ell):
        anf = [int.from_bytes(b" "+r[1:], "little") for r in rows[start:start+span]]
        for j in range(a+b):
            for x in range(span):
                if x & (1 << j):
                    anf[x] ^= anf[x ^ (1 << j)]
        assert all(not x or mask.bit_count() <= 2 for mask, x in enumerate(anf))
    return len(raw)*8, len(pins)


def difference_census():
    pairs = 0
    for a in range(2, 8):
        values = cubes(a)
        for h in range(1, 1 << a):
            for b in range(1, a+1):
                fibers = Counter((y ^ values[x ^ h]) & ((1 << b)-1)
                                 for x, y in enumerate(values))
                assert max(fibers.values()) <= 1 << (a-b+1)
                pairs += len(values)
    return pairs


def subspace_census():
    # Graph in nine name bits, a=5, b=4, q=2. Every 2-flat direction
    # occurs once by taking two numerically least nonzero vectors of its span.
    a, b = 5, 4
    n = 1 << (a+b)
    points = {((v & 15) << a) | x for x, v in enumerate(cubes(a))}
    count = 0
    hist = Counter()
    for x, y in combinations(range(1, n), 2):
        z = x ^ y
        if y > z:
            continue
        isolated = sum(all((p ^ s) not in points for s in (x, y, z)) for p in points)
        assert isolated >= len(points) - 3*(1 << (a-b+1))
        hist[isolated] += 1
        count += 1
    assert count == (n-1)*(n-2)//6
    smallest = min(hist)
    return count, smallest


def affine_images(ell, rng):
    # Invertibility follows by elementary row operations.
    cols = [1 << x for x in range(ell)]
    for _ in range(8*ell):
        i, j = rng.sample(range(ell), 2)
        cols[i] ^= cols[j]
    vals = [rng.randrange(1 << ell)]
    for col in cols:
        vals += [x ^ col for x in vals]
    return vals


def parity_and_interval_audit():
    # a=5,b=5 plus an extra tag bit. On blocks of 8 names the
    # intersection with the chosen tag is at least two dimensional.
    a = b = 5
    ell = a+b+1
    q = b-2
    slices = [((c & 31) << a) | x for x, c in enumerate(cubes(a))]
    rng = Random(64381)
    flats = singleton_count = 0
    for _ in range(120):
        perm = affine_images(ell, rng)
        assert len(set(perm)) == 1 << ell
        allowed = [False]*(1 << ell)
        actual = [False]*(1 << ell)
        for x in range(1 << (ell-1)):
            allowed[perm[x]] = True
        for x in slices:
            actual[perm[x]] = True
        cuts = sorted(rng.sample(range(1, 1 << ell), 13))
        coeffs = [rng.randrange(1 << (ell+1)) for _ in range(len(cuts)+1)]
        breaks = set(cuts)
        isolated = mismatch = charged = 0
        for start in range(0, 1 << ell, 1 << q):
            block = range(start, start+(1 << q))
            if sum(actual[x] for x in block) != 1:
                continue
            isolated += 1
            class_size = sum(allowed[x] for x in block)
            assert class_size in (4, 8)
            if any(x in breaks for x in list(block)[1:]):
                charged += 1
                continue
            coeff = coeffs[sum(x <= start for x in cuts)]
            predictions = [((coeff & (x | (1 << ell))).bit_count() & 1)
                           for x in block if allowed[x]]
            assert sum(predictions) % 2 == 0
            assert any(pred != actual[x] for pred, x in
                       zip(predictions, [x for x in block if allowed[x]]))
            mismatch += 1
        assert isolated >= len(slices) - ((1 << q)-1)*2
        assert isolated <= charged + mismatch
        singleton_count += isolated
        flats += 1
    return flats, singleton_count


if __name__ == "__main__":
    cases = [physical(ell) for ell in range(4, 12)]
    print("physical files, bits, forced names:", len(cases), *map(sum, zip(*cases)))
    print("direction/input/projection tests:", difference_census())
    print("all 2-flat directions, minimum isolated:", *subspace_census())
    print("affine changes, parity witnesses:", *parity_and_interval_audit())
