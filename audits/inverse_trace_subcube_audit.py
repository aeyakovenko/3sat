"""Exact rooted coordinate subcubes of inverse trace, and independent moment checks."""

from collections import Counter
from fractions import Fraction
from math import comb, log2

from inverse_trace_chart_audit import divmod_polynomial, polynomial_product


def irreducible(d):
    for p in range((1 << d) + 1, 2 << d, 2):
        if all(divmod_polynomial(p, divisor)[1] != 0
               for divisor in range(2, 2 << (d // 2))):
            return p
    raise AssertionError("missing irreducible polynomial")


def positive_roots(d):
    q = 1 << d
    p = irreducible(d)

    def mul(x, y):
        return divmod_polynomial(polynomial_product(x, y), p)[1]

    def power(x, exponent):
        value = 1
        while exponent:
            if exponent & 1:
                value = mul(value, x)
            x = mul(x, x)
            exponent >>= 1
        return value

    mask = 0
    for x in range(q):
        y = power(x, q - 2) if x else 0
        assert (x == 0 and y == 0) or mul(x, y) == 1
        trace = 0
        for _ in range(d):
            trace ^= y
            y = mul(y, y)
        assert trace in (0, 1)
        mask |= (1 - trace) << x
    assert mask.bit_count() == q // 2
    return p, mask


def submasks(mask):
    part = mask
    while True:
        yield part
        if part == 0:
            break
        part = (part - 1) & mask


def rooted_faces(d, side):
    """At direction mask u, bit x means the entire face x+span(u) is in side."""
    q = 1 << d
    low = {1 << i: sum(1 << x for x in range(q) if not (x >> i) & 1) for i in range(d)}
    faces = [side]
    for u in range(1, q):
        direction = u & -u
        previous = faces[u ^ direction]
        shifted = ((previous & low[direction]) << direction) | ((previous >> direction) & low[direction])
        faces.append(previous & shifted)
    # Independent face enumeration over fixed and free coordinates.
    for u in range(q):
        points = sum(1 << x for x in submasks(u))
        for root in submasks((q - 1) ^ u):
            translated = points << root  # root has no free coordinate set.
            expected = translated & side == translated
            assert faces[u] & translated == (translated if expected else 0)
    return faces


def ideal_moments(d, j):
    choices = comb(d, j)
    size = 1 << j
    first = Fraction(choices, 1 << (size - 1))
    second = Fraction()
    for shared in range(max(0, 2 * j - d), j + 1):
        multiplicity = comb(j, shared) * comb(d - j, j - shared)
        union = 2 * size - (1 << shared)
        second += Fraction(choices * multiplicity, 1 << (union - 1))
    return first, second


def check_pattern(q, observed, size):
    # Eq. (4.1), expanded in the prescribed signs and conditioned on the root:
    # |2 observed/q - 2^(1-size)| <= 8 size / sqrt(q).
    if 64 * size * size < q:
        denominator = 1 << (size - 1)
        assert (2 * observed * denominator - q) ** 2 <= 64 * size * size * q * denominator ** 2


def audit_side(d, side):
    q = 1 << d
    faces = rooted_faces(d, side)
    largest = [-1] * q
    for j in range(d + 1):
        directions = [u for u in range(q) if u.bit_count() == j]
        per_root = [0] * q
        for u in directions:
            marked = faces[u]
            check_pattern(q, marked.bit_count(), 1 << j)
            while marked:
                bit = marked & -marked
                root = bit.bit_length() - 1
                largest[root] = j
                per_root[root] += 1
                marked ^= bit
        by_overlap = Counter()
        pair_total = 0
        for u in directions:
            for v in directions:
                shared = (u & v).bit_count()
                by_overlap[shared] += 1
                pair_count = (faces[u] & faces[v]).bit_count()
                check_pattern(q, pair_count, (2 << j) - (1 << shared))
                pair_total += pair_count
        assert sum(t * t for t in per_root) == pair_total
        assert sum(per_root) == sum(faces[u].bit_count() for u in directions)
        assert all(n == len(directions) * comb(j, l) * comb(d - j, j - l)
                   for l, n in by_overlap.items())
        hits = sum(t > 0 for t in per_root)
        assert sum(per_root) ** 2 <= hits * pair_total
        assert hits <= sum(per_root)
    return dict(sorted(Counter(largest[x] for x in range(q) if side >> x & 1).items()))


def audit_iid_tables():
    tests = 0
    for d in (1, 2, 3, 4):
        q = 1 << d
        for j in range(d + 1):
            all_points = [sum(1 << x for x in submasks(u))
                          for u in range(q) if u.bit_count() == j]
            first = second = 0
            # Enumerate every truth table conditioned on a positive sign at the origin.
            for positives in range(1, 1 << q, 2):
                observed = sum(positives & cube == cube for cube in all_points)
                first += observed
                second += observed ** 2
            normalizer = 1 << (q - 1)
            assert (Fraction(first, normalizer), Fraction(second, normalizer)) == ideal_moments(d, j)
            tests += 1
    return tests


def log_fraction(x):
    return log2(x.numerator) - log2(x.denominator)


def numerical_window():
    # d=2^(2^t) makes floor(log2 log2 d + log2 log2 log2 d) exact using integers.
    for t in (3, 4, 5, 6, 8):
        log_d = 1 << t
        d = 1 << log_d
        m = t + t.bit_length() - 1
        first, second = ideal_moments(d, m)
        variance_ratio = second / first ** 2 - 1
        upper, _ = ideal_moments(d, m + 2)
        # Eq. (4.1) errors relative to the lower first moment and its square,
        # and absolute total error on the upper first moment. Cap the exact
        # error exponent to avoid any integer having 2^256 binary digits.
        error_bits = min(256, d // 2 - (3 + m) - ((1 << m) - 1),
                         d // 2 - (4 + m) - 2 * ((1 << m) - 1),
                         d // 2 - (m + 2) * log_d - (3 + m + 2))
        assert error_bits > 0
        error = Fraction(1, 1 << error_bits)
        lower_tail = variance_ratio + 3 * error
        upper_tail = upper + error
        assert lower_tail + upper_tail < 1
        print(f"d=2^{log_d}, m={m}: log2 upper bounds on P(J<m) and P(J>m+1) "
              f"{log_fraction(lower_tail):.2f}, {log_fraction(upper_tail):.2f}.")


def main():
    print(f"First and second ideal moments matched exhaustive fixed-root truth tables "
          f"in {audit_iid_tables()} dimension/face-size pairs.")
    for d in range(3, 11):
        q = 1 << d
        p, positive = positive_roots(d)
        plus = audit_side(d, positive)
        minus = audit_side(d, positive ^ ((1 << q) - 1))
        print(f"d={d} P={p:#b}: + {plus}, - {minus}.")
    numerical_window()


if __name__ == "__main__":
    main()
