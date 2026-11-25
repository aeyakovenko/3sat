"""Finite inverse-trace, chart-width and additive character audits; standard library."""

from collections import Counter
from itertools import combinations, permutations, product


def polynomial_product(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        b >>= 1
    return result


def divmod_polynomial(numerator, modulus):
    quotient = 0
    while numerator.bit_length() >= modulus.bit_length():
        shift = numerator.bit_length() - modulus.bit_length()
        quotient ^= 1 << shift
        numerator ^= modulus << shift
    return quotient, numerator


def source_audit(d, modulus):
    size = 1 << d
    values = range(size)
    assert modulus.bit_length() == d + 1
    raw = [[polynomial_product(x, y) for y in values] for x in values]
    mul = [[divmod_polynomial(raw[x][y], modulus)[1] for y in values] for x in values]
    # Each nonzero polynomial residue acts invertibly, checking the chosen modulus too.
    assert all(len(set(row)) == size for row in mul[1:])
    inverse = [0] + [mul[x].index(1) for x in range(1, size)]
    traces = []
    for y in values:
        frobenius, trace = y, 0
        for _ in range(d):
            trace ^= frobenius
            frobenius = mul[frobenius][frobenius]
        assert frobenius == y and trace in (0, 1)
        traces.append(trace)
    sign = [1 - 2 * traces[inverse[x]] for x in values]
    assert sum(sign) == 0
    for pins in product((0, 1), repeat=d):
        x = sum(bit << i for i, bit in enumerate(pins))
        assert all((x >> i) & 1 == bit for i, bit in enumerate(pins))
        # Enumerate the witnesses for the actual polynomial identity (no field reduction).
        possible = [(y, quotient) for y in values for quotient in values
                    if (y == 0 if x == 0 else
                        raw[x][y] == (1 ^ polynomial_product(modulus, quotient)))]
        assert {y for y, _ in possible} == {inverse[x]}
        if x:
            assert len(possible) == 1
            assert possible[0][1] == divmod_polynomial(raw[x][inverse[x]] ^ 1, modulus)[0]
        else:
            assert (0, 0) in possible
        assert any(traces[y] for y, _ in possible) == (sign[x] == -1)
    return sign


def parity(n):
    return n.bit_count() % 2


def characters(q):
    return [[1 - 2 * parity(frequency & x) for x in range(q)] for frequency in range(q)]


def affine_cells(q):
    """List every linear span and every coset, independently of any field basis search."""
    spaces = {frozenset([0])}
    for x in range(1, q):
        spaces |= {space | frozenset(v ^ x for v in space) for space in spaces}
    return {sum(1 << (v ^ shift) for v in space) for space in spaces for shift in range(q)}


def audit_fourier(sign):
    q = len(sign)
    chars = characters(q)
    spectral = [sum(s * c for s, c in zip(sign, row)) for row in chars]
    maximum = max(map(abs, spectral))
    cells = affine_cells(q)
    masks = range(1 << q) if q == 8 else cells
    for mask in masks:
        elements = [x for x in range(q) if mask & (1 << x)]
        spectrum = [sum(row[x] for x in elements) for row in chars]
        norm = sum(map(abs, spectrum))
        if mask in cells:
            assert norm == q
        for twist, row in enumerate(chars):
            correlation = sum(sign[x] * row[x] for x in elements)
            assert q * correlation == sum(c * spectral[u ^ twist] for u, c in enumerate(spectrum))
            assert q * abs(correlation) <= norm * maximum
            if mask in cells and abs(correlation) == len(elements):
                assert len(elements) <= maximum
    # Repetitions and zero shifts are allowed in these even tuples.
    for length in ((2, 4) if q == 8 else (2,)):
        for shifts in product(range(q), repeat=length):
            net = 0
            for z in shifts:
                net ^= z
            for row in chars:
                for a in range(q):
                    translated = 1
                    for z in shifts:
                        translated *= row[a ^ z]
                    assert translated == row[net]
    return len(cells), maximum


def coordinates(basis, x):
    return sum(parity(row & x) << i for i, row in enumerate(basis))


def clause_masks(q, k):
    d = q.bit_length() - 1
    full = (1 << q) - 1
    clauses = {0, full}  # An empty clause, and the empty conjunction.
    for size in range(1, k + 1):
        for indices in combinations(range(d), size):
            projection = sum(1 << i for i in indices)
            for assignment in range(q):
                forbidden = sum(1 << x for x in range(q)
                                if (x & projection) == (assignment & projection))
                clauses.add(full ^ forbidden)
    return clauses


def chart_masks(q, k):
    full = (1 << q) - 1
    clauses = clause_masks(q, k)
    masks = {full}
    for clause in clauses:
        masks |= {mask & clause for mask in masks}
    # Rebuild from the theory of each of the 256 candidate truth sets, separately.
    for target in range(1 << q):
        hull = full
        for clause in clauses:
            if target & clause == target:
                hull &= clause
        assert (target == hull) == (target in masks)
    assert all(a & b in masks for a in masks for b in masks)
    return masks, sorted(clauses - {0, full})


def repeated_challenges(family, survey, q):
    full = (1 << q) - 1
    truth = full
    for test in survey:
        truth &= test
    counts = Counter([full])
    for repetitions in range(1, 6):
        following = Counter()
        for old, copies in counts.items():
            for test in survey:
                following[old & test] += copies
        counts = following
        denominator = len(survey) ** repetitions
        assert sum(counts.values()) == denominator
        assert all(outcome in family and outcome & truth == truth for outcome in counts)
        errors = []
        for x in range(q):
            passes = sum((test >> x) & 1 for test in survey)
            accepted = sum(copies for outcome, copies in counts.items() if outcome >> x & 1)
            assert accepted == passes ** repetitions
            if not truth >> x & 1:
                errors.append(accepted)
        assert denominator - counts[truth] <= sum(errors)


def audit_frames(sign):
    q, d = len(sign), 3
    chars = characters(q)
    full = (1 << q) - 1
    frames = [tuple(coordinates(basis, x) for x in range(q))
              for basis in permutations(range(1, q), d)]
    frames = [coords for coords in frames if len(set(coords)) == q]
    assert len(set(frames)) == len(frames) == 168
    for k in (1, 2):
        masks, clauses = chart_masks(q, k)
        by_frame = Counter()
        for coords in frames:
            # A coordinate mask is pulled back to field inputs by the actual frame.
            pull = [sum(1 << x for x in range(q) if mask >> coords[x] & 1)
                    for mask in range(full + 1)]
            family = {pull[mask] for mask in masks}
            assert len(family) == len(masks)
            sample = [pull[clauses[i]] for i in (0, len(clauses) // 2, len(clauses) - 1)]
            repeated_challenges(family, sample, q)
            # True sets contained in either sign class, including all additive Walsh twists.
            for row in chars:
                plus = sum(1 << x for x, c in enumerate(row) if sign[x] * c == 1)
                for side in (plus, full ^ plus):
                    best = max(mask.bit_count() for mask in family if mask & side == mask)
                    by_frame[best] += 1
        print(f"GF(8), width {k}: {len(masks)} CNF truth sets per frame; "
              f"maximal one-sided sizes over 168 frames, 8 twists, 2 signs {dict(sorted(by_frame.items()))}.")


def main():
    for d, modulus in ((3, 0b1011), (4, 0b10011)):
        sign = source_audit(d, modulus)
        cell_count, maximum = audit_fourier(sign)
        print(f"GF({len(sign)}): {len(sign)} pinned coefficient inputs, {cell_count} nonempty affine cells, "
              f"maximum absolute unnormalized Walsh coefficient {maximum}.")
        if d == 3:
            audit_frames(sign)


if __name__ == "__main__":
    main()
