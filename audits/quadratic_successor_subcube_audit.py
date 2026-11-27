"""Exhaust small Boolean preservation systems and their coordinate restrictions."""
from functools import cache
from itertools import combinations, product


def terms(polynomial):
    while polynomial:
        low = polynomial & -polynomial
        yield low.bit_length() - 1
        polynomial ^= low


def var(i):
    return 1 << (1 << i)


def mul(p, q):
    result = 0
    for a in terms(p):
        for b in terms(q):
            result ^= 1 << (a | b)
    return result


def val(p, x):
    return sum(x & term == term for term in terms(p)) % 2


def subst(p, images):
    total = 0
    for monomial in terms(p):
        term = 1
        for i in terms(monomial):
            term = mul(term, images[i])
        total ^= term
    return total


@cache
def quad_part(p):
    return sum(1 << term for term in terms(p) if term.bit_count() == 2)


def echelon(equations):
    basis = {}
    for p in equations:
        while p:
            quadratic = quad_part(p)
            pivot = (quadratic or p).bit_length() - 1
            if pivot not in basis:
                basis[pivot] = p
                break
            p ^= basis[pivot]
    linear = {pivot: p for pivot, p in basis.items() if not quad_part(p)}
    quadratic = tuple(p for p in basis.values() if quad_part(p))
    return linear, quadratic


def simplify(n, equations):
    """Solve all affine consequences and repeat in the remaining coordinates."""
    while True:
        linear, reduced = echelon(equations)
        if 0 in linear:  # the monomial 1 is a pivot
            return None
        if not linear:
            return n, reduced
        free = [i for i in range(n) if (1 << i) not in linear]
        images = [0] * n
        for j, i in enumerate(free):
            images[i] = var(j)
        for pivot, p in sorted(linear.items()):
            i = pivot.bit_length() - 1
            images[i] = subst(p ^ (1 << pivot), images)
        equations = tuple(subst(p, images) for p in reduced)
        n = len(free)


@cache
def gauss(n, p):
    """Return the signed character sum by eliminating a mixed term xy."""
    quad = quad_part(p)
    if not quad:
        return 0 if p > 1 else (1 - 2*p) * (1 << n)
    mixed = next(terms(quad))
    i, j = tuple(terms(mixed))
    surviving = [k for k in range(n) if k not in (i, j)]
    def restrict(x, y):
        mapping = [0] * n
        mapping[i], mapping[j] = x, y
        for index, old in enumerate(surviving):
            mapping[old] = var(index)
        return subst(p, mapping)
    c = restrict(0, 0)
    a = restrict(1, 0) ^ c
    b = restrict(0, 1) ^ c
    return 2 * gauss(n - 2, c ^ mul(a, b))


def dual_count(n, reduced):
    sums = [0]
    for p in reduced:
        sums += [s ^ p for s in sums]
    total = sum(gauss(n, p) for p in sums)
    assert total % len(sums) == 0
    return total // len(sums)


def small_systems():
    n = 3
    monomials = [k for k in range(1 << n) if k.bit_count() <= 2]
    polys = [sum(1 << monomials[i] for i in terms(p)) for p in range(1 << len(monomials))]
    all_points = list(range(1 << n))
    zero_masks = {p: sum(1 << x for x in all_points if not val(p, x)) for p in polys}
    cubes = []
    for state in product((0, 1, 2), repeat=n):  # 2 means editable
        free = state.count(2)
        mask = sum(1 << x for x in all_points if all(
            v == 2 or v == (x >> i) & 1 for i, v in enumerate(state)))
        cubes.append((free, mask))
    counts = restrictions = refined = 0
    for p in polys:
        for q in polys:
            expected = zero_masks[p] & zero_masks[q]
            strata = simplify(n, (p, q))
            if strata is None:
                assert expected == 0
            else:
                u, residual = strata
                assert expected.bit_count() == dual_count(u, residual)
                h, r = n - u, len(residual)
                direct_l, direct_q = echelon((p, q))
                refined += (h + 2*r < len(direct_l) + 2*len(direct_q))
                for t, mask in cubes:
                    overlap = (expected & mask).bit_count()
                    if overlap:
                        assert overlap >= 1 << max(0, t-h-2*r)
                        restrictions += 1
            counts += 1
    return counts, restrictions, refined


def sharp_chains():
    tested = 0
    for h in range(5):
        for r in range(4):
            n = h + 2*r + 1
            differences = [var(i) ^ var(i+1) for i in range(n-1)]
            eqs = list(differences[:h])
            for i in range(h, n-1, 2):
                eqs.append(1 ^ mul(1 ^ differences[i], 1 ^ differences[i+1]))
            assert simplify(n, tuple(eqs))[0] == n - h
            assert [x for x in range(1 << n) if not any(val(p, x) for p in eqs)] == [0, (1 << n)-1]
            tested += 1
    return tested


def known_extensions():
    """Full gate-bit exhaustion for every unary F, using f(x)=c+a*x."""
    checked = 0
    for c, a in product((0, 1), repeat=2):
        s, x, fx, first, second, verdict = (var(i) for i in range(6))
        equations = (fx ^ c ^ a*x, first ^ mul(s, fx),
                     second ^ mul(1 ^ s, 1 ^ x), verdict ^ first ^ second, 1 ^ verdict)
        # The last XOR computes OR because its two inputs are disjoint.
        candidates = [z for z in range(64) if not any(val(p, z) for p in equations)]
        expected = sum(c ^ (a*t) for t in (0, 1))
        assert len(candidates) == 1 + expected
        assert sum(not (z & 1) for z in candidates) == 1
        u, residual = simplify(6, equations)
        assert dual_count(u, residual) == 1 + expected
        checked += 64
    return checked


if __name__ == '__main__':
    total, local, refinements = small_systems()
    print(f'{total} three-bit systems; {local} nonempty prescribed subcubes; '
          f'{refinements} systems with a strictly improved reduced degree budget')
    print(f'{sharp_chains()} sharp distance/density examples; '
          f'{known_extensions()} complete circuit fillings in known-seed tests')
