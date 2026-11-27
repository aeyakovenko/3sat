"""Exhaust canonical primary witnesses for every binary matrix through dimension four."""
from itertools import product


def polymul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out


def remainder(a, f):
    while a.bit_length() >= f.bit_length():
        a ^= f << (a.bit_length() - f.bit_length())
    return a


def power(a, k, op, identity):
    result = identity
    while k:
        if k & 1:
            result = op(result, a)
        a = op(a, a)
        k >>= 1
    return result


def apply(cols, v):
    out = 0
    while v:
        bit = v & -v
        out ^= cols[bit.bit_length() - 1]
        v ^= bit
    return out


def compose(left, right):
    return tuple(apply(left, v) for v in right)


def identity(d):
    return tuple(1 << j for j in range(d))


def ambient_bases(d):
    def visit(cols, span):
        if len(cols) == d:
            images = [0] * (1 << d)
            for i, image in enumerate(span):
                images[image] = i
            yield cols, tuple(images[1 << j] for j in range(d))
            return
        for v in range(1, 1 << d):
            if v not in span:
                yield from visit(cols + (v,), span + tuple(v ^ w for w in span))
    return list(visit((), (0,)))


def block_types(d):
    fs = []
    for f in range(2, 1 << (d+1)):
        degree = f.bit_length()-1
        if all(remainder(f, g) for g in range(2, 1 << (1 + degree//2))):
            fs.extend((f, r) for r in range(1, 1 + d//degree))

    def fill(remaining, start):
        if not remaining:
            yield ()
        for i in range(start, len(fs)):
            f, r = fs[i]
            weight = (f.bit_length()-1)*r
            if weight <= remaining:
                for tail in fill(remaining-weight, i):
                    yield ((f, r),) + tail
    return fill(d, 0)


class PrimaryShape:
    def __init__(self, shape):
        self.shape = shape
        self.operator = []
        self.banks = {}
        offset = 0
        for f, r in shape:
            e = f.bit_length()-1
            n = e*r
            p = power(f, r, polymul, 1)
            self.operator.extend(remainder(1 << (i+1), p) << offset for i in range(n))
            bank = self.banks.setdefault(f, [])
            for t in range(r):
                for j in range(e):
                    # height, is-top, standard generator order, local degree
                    key = (r-t, t == 0, offset, j)
                    element = power(f, t, polymul, 1) << (offset+j)
                    bank.append((key, element))
            offset += n
        self.operator = tuple(self.operator)
        self.banks = [sorted(bank) for bank in self.banks.values()]

    def accepted(self, basis):
        for bank in self.banks:
            reduced = []
            tests = []
            for (height, top, _, j), polycol in bank:
                g = apply(basis, polycol)
                z = g
                for pivot, col in reduced:
                    if z & pivot:
                        z ^= col
                assert z
                p = z & -z
                if top and j == 0:
                    if z != g:
                        return False
                    tests.append((height, len(reduced), p))
                reduced.append((p, z))
            for height, start, first in tests:
                largest = max(reduced[h][0] for h in range(start, len(bank))
                              if bank[h][0][0] == height)
                if first != largest:
                    return False
        return True

    def reduced_power(self, k):
        d = len(self.operator)
        period = 1 << (d-1).bit_length()
        for f in set(f for f, _ in self.shape if f != 2):
            period *= (1 << (f.bit_length()-1))-1
        n = k if k < d else d + (k-d) % period
        cols = []
        offset = 0
        for f, r in self.shape:
            p = power(f, r, polymul, 1)
            v = power(2, n, lambda x, y: remainder(polymul(x, y), p), 1)
            for _ in range(p.bit_length()-1):
                cols.append(v << offset)
                v = remainder(v << 1, p)
            offset = len(cols)
        return tuple(cols)


def exhaust(d):
    bases = ambient_bases(d)
    seen = set()
    checks = shapes = 0
    ks = (0, 1, 2, 7, (1 << 67)+d)
    for shape in block_types(d):
        spec = PrimaryShape(shape)
        shapes += 1
        # Test actual powering against all columns of each block.
        for k in ks:
            oracle = power(spec.operator, k, compose, identity(d))
            assert spec.reduced_power(k) == oracle
        k = ks[-1]
        canonical_power = spec.reduced_power(k)
        for basis, inverse in bases:
            if not spec.accepted(basis):
                continue
            actual = compose(compose(basis, spec.operator), inverse)
            assert actual not in seen, (d, shape, basis)
            seen.add(actual)
            # A nontrivial external-coordinate check on each selected orbit.
            if checks < shapes:
                assert compose(compose(basis, canonical_power), inverse) == power(actual, k, compose, identity(d))
                checks = shapes
    assert len(seen) == 1 << (d*d)
    return shapes, len(bases)*shapes, len(seen)


def rank(cols):
    pivots = {}
    for v in cols:
        while v:
            p = v & -v
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def square_zero_tests():
    n = 2
    ms = list(product(range(1 << n), repeat=n))
    for a, b, c in product(ms, repeat=3):
        # Columns of [I B; A C]. Embedding this as an off-diagonal
        # block of a square-zero matrix preserves rank.
        schur = tuple(x | (y << n) for x, y in zip(identity(n)+b, a+c))
        assert (rank(schur) == n) == (compose(a,b) == c)
    return len(ms)**3


if __name__ == '__main__':
    for dim in range(1, 5):
        shapes, candidates, accepted = exhaust(dim)
        print(f'd={dim}: {shapes} shapes, {candidates} conjugators, exactly {accepted} canonical matrices',
              flush=True)
    print(f'{square_zero_tests()} square-zero similarity predicates checked')
