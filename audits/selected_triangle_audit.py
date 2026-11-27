"""Exhaust three side-two physical cubes and verify their field identities.

Requires pycosat. This tests a small layout, not its asymptotic size.
"""

from itertools import product
from random import Random

import pycosat

from table_probe_context_audit import parse


def side_two_layout(pin_selectors=True):
    """The returned offsets are ASCII low bits, each used exactly once."""
    used = {1, 2, 3, 10, 11, 20, 21, 30, 31, 40, 41}
    fixed = [tuple(-i if (mask >> (i - 1)) & 1 else i for i in (1, 2, 3))
             for mask in range(1, 8)]
    fixed.extend([(-10, 1, 2), (11, 1, 2)])
    fixed.extend([(-v, 1, 2) for v in range(1, 42) if v not in used])
    for v in (20, 30, 40):
        fixed.extend([(v, v+1, 1), (-v, -v-1, 1)])

    # Each row contributes one editable decimal digit. A wrong pair of
    # indices disables a table row. The matching row requires constant 11.
    slots = []
    for left, right in ((20, 30), (30, 40), (40, 20)):
        for u, v in product(range(2), repeat=2):
            slots.append(f"-{left+u} -{right+v} 1# 0\n")
    if pin_selectors:
        for selector in (20, 30, 40):
            slots.append(f"{selector//10}# 1 2 0\n")

    body = "".join(" ".join(map(str, row)) + " 0\n" for row in fixed)
    template = (f"p cnf 41 {len(fixed)+len(slots)}\n" + body + "".join(slots)).encode()
    offsets = [i for i, byte in enumerate(template) if byte == ord("#")]
    assert len(offsets) == (15 if pin_selectors else 12)
    return template.replace(b"#", b"0"), offsets


def physical_truth_table():
    source, offsets = side_two_layout()
    files = bytearray(source)
    verdicts = []
    for mask in range(1 << 15):
        for bit, offset in enumerate(offsets):
            files[offset] = 48 + ((mask >> bit) & 1)
        clauses, variables = parse(files)
        assert variables == 41
        models = pycosat.itersolve(clauses, vars=variables)
        first = next(models, None)
        assert next(models, None) is None
        i, k, j = ((mask >> bit) & 1 for bit in (12, 13, 14))
        selected = (2*i+k, 4+2*k+j, 8+2*j+i)
        expected = int(all((mask >> bit) & 1 for bit in selected))
        observed = int(first is not None)
        assert observed == expected
        verdicts.append(observed)
    return verdicts, len(source), len(parse(source)[0])


def gf_mul(x, y):
    """Polynomial basis modulo u²+u+1."""
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x & 4:
            x ^= 7
    return result


MUL = tuple(tuple(gf_mul(x, y) for y in range(4)) for x in range(4))
INV = (None, 1, 3, 2)


def normalized_expectation(verdicts, means):
    # Eliminate the physical bits directly from the measured truth table.
    values = verdicts
    for mean in means:
        zero_weight, one_weight = MUL[mean ^ 1], MUL[mean]
        values = [zero_weight[values[i]] ^ one_weight[values[i+1]]
                  for i in range(0, len(values), 2)]
    value, = values
    return value


def triangle(x, y, z):
    result = 0
    for i, k, j in product(range(2), repeat=3):
        result ^= MUL[MUL[x[2*i+k]][y[2*k+j]]][z[2*j+i]]
    return result


def check_field(verdicts):
    assert all(MUL[v][INV[v]] == 1 for v in (1, 2, 3))
    units = [tuple(int(i == j) for j in range(4)) for i in range(4)]
    cases = list(product(units, repeat=3))
    rng = Random(3049)
    cases.extend(tuple(tuple(rng.randrange(4) for _ in range(4)) for _ in range(3))
                 for _ in range(16))
    contractions = 0
    observed = set()
    for selectors in product((2, 3), repeat=3):
        pi, pk, pj = ((v ^ 1, v) for v in selectors)
        for x, y, z in cases:
            a = [MUL[x[2*i+k]][INV[MUL[pi[i]][pk[k]]]]
                 for i, k in product(range(2), repeat=2)]
            b = [MUL[y[2*k+j]][INV[pj[j]]] for k, j in product(range(2), repeat=2)]
            result = normalized_expectation(verdicts, [*a, *b, *z, *selectors])
            assert result == triangle(x, y, z)
            observed.add(result)
            contractions += 1
    assert observed == set(range(4))
    return contractions


def one_hot_layout(side):
    """Proper gate encoding with one editable pin digit per matrix entry."""
    entries = 3 * side * side
    pairs = [(10*r, 10*r+1) for r in range(1, entries+1)]
    used = {1, 2, 3}.union(v for pair in pairs for v in pair)
    last = pairs[-1][1]
    rows = [tuple(-i if (mask >> (i-1)) & 1 else i for i in (1, 2, 3))
            for mask in range(1, 8)]
    rows.extend((-v, 1, 2) for v in range(1, last+1) if v not in used)
    for off, on in pairs:
        rows.extend(((off, on, 1), (-off, -on, 1)))

    def or_gate(a, b):
        nonlocal last
        last += 1
        rows.extend(((-a, last, 1), (-b, last, 1), (a, b, -last)))
        return last

    def disjunction(bits):
        result = bits[0]
        for bit in bits[1:]:
            result = or_gate(result, bit)
        return result

    area = side * side
    tables = [[pairs[s*area+t][1] for t in range(area)] for s in range(3)]
    for table in tables:
        seen = table[0]
        for bit in table[1:]:
            rows.append((-seen, -bit, 1))
            seen = or_gate(seen, bit)
        rows.append((seen, 1, 2))
    # The chosen column of each table equals the chosen row of the next.
    for s in range(3):
        left, right = tables[s], tables[(s+1) % 3]
        for label in range(side):
            col = disjunction(left[label::side])
            row = disjunction(right[side*label:side*(label+1)])
            rows.extend(((-col, row, 1), (col, -row, 1)))
    pins = [f"{off//10}# 1 2 0\n" for off, _ in pairs]
    header = f"p cnf {last} {len(rows)+len(pins)}\n"
    body = "".join(" ".join(map(str, row)) + " 0\n" for row in rows)
    template = (header + body + "".join(pins)).encode()
    offsets = [i for i, ch in enumerate(template) if ch == ord("#")]
    assert len(offsets) == entries
    return template.replace(b"#", b"0"), offsets


def integer_mobius(values):
    coefficients = list(values)
    width = len(values).bit_length()-1
    assert len(values) == 1 << width
    for bit in range(width):
        step = 1 << bit
        for mask in range(len(values)):
            if mask & step:
                coefficients[mask] -= coefficients[mask ^ step]
    return coefficients


def check_one_hot():
    source, offsets = one_hot_layout(2)
    files = bytearray(source)
    verdicts = []
    distances = []
    accepted = set()
    for mask in range(1 << len(offsets)):
        for bit, offset in enumerate(offsets):
            files[offset] = 48 + ((mask >> bit) & 1)
        clauses, variables = parse(files)
        models = pycosat.itersolve(clauses, vars=variables)
        sat = next(models, None) is not None
        assert next(models, None) is None
        verdicts.append(int(sat))
        if sat:
            accepted.add(mask)
            distances.append(sum((a^b).bit_count() for a, b in zip(source, files)))

    triangles = {(1 << (2*i+k)) | (1 << (4+2*k+j)) | (1 << (8+2*j+i))
                 for i, k, j in product(range(2), repeat=3)}
    assert accepted == triangles and len(triangles) == 8
    assert min(distances) == max(distances) == 3
    coefficients = integer_mobius(verdicts)
    lower = [v for mask, v in enumerate(coefficients) if mask.bit_count() < 3]
    cubic = {mask: v for mask, v in enumerate(coefficients) if mask.bit_count() == 3}
    assert len(lower) == 79 and not any(lower)
    assert len(cubic) == 220
    assert all(value == int(mask in triangles) for mask, value in cubic.items())
    return len(source), variables, len(clauses), len(accepted), len(cubic)


def check_free_selectors(pinned_verdicts):
    radius = 5
    source, offsets = side_two_layout(pin_selectors=False)
    files = bytearray(source)
    witnesses = {(i, k, j): (1 << (2*i+k)) | (1 << (4+2*k+j)) | (1 << (8+2*j+i))
                 for i, k, j in product(range(2), repeat=3)}
    verdicts = []
    total_models = 0
    ambiguous = 0
    for mask in range(1 << len(offsets)):
        for bit, offset in enumerate(offsets):
            files[offset] = 48 + ((mask >> bit) & 1)
        clauses, variables = parse(files)
        seen = set()
        for model in pycosat.itersolve(clauses, vars=variables):
            triple = tuple(int(bit in model) for bit in (21, 31, 41))
            assert triple not in seen
            seen.add(triple)
        assert seen == {triple for triple, support in witnesses.items()
                        if mask & support == support}
        assert len(seen) == sum(pinned_verdicts[mask | (s << 12)] for s in range(8))
        verdicts.append(int(bool(seen)))
        total_models += len(seen)
        ambiguous += len(seen) > 1

    # Compute the integer coefficients three ways: independent SAT verdicts,
    # the same sparse truth table completed by zero, and inclusion-exclusion
    # over edge unions of the geometrically specified triangles.
    sparse = [verdict if mask.bit_count() <= radius else 0
              for mask, verdict in enumerate(verdicts)]
    full_coeff = integer_mobius(verdicts)
    capped_coeff = integer_mobius(sparse)
    edge_sets = list(witnesses.values())
    from_unions = [0] * len(verdicts)
    for chosen in range(1, 1 << len(edge_sets)):
        union = 0
        for i, support in enumerate(edge_sets):
            if chosen & (1 << i):
                union |= support
        if union.bit_count() <= radius:
            from_unions[union] += 1 if chosen.bit_count() % 2 else -1
    low = [mask for mask in range(len(verdicts)) if mask.bit_count() <= radius]
    assert all(full_coeff[m] == capped_coeff[m] == from_unions[m] for m in low)
    assert all(full_coeff[m] == int(m in edge_sets) for m in low if m.bit_count() <= 3)
    assert min(m.bit_count() for m, sat in enumerate(verdicts) if sat) == 3
    quintics = [full_coeff[m] for m in low if m.bit_count() == 5 and full_coeff[m]]
    assert quintics == [-1] * 12
    return sum(verdicts), ambiguous, total_models, len(low)


def triangle_transversals(side):
    """Compare independently enumerated minimum transversals with all index partitions."""
    area = side * side
    triangles = [(1 << (side*i+k)) | (1 << (area+side*k+j)) | (1 << (2*area+side*j+i))
                 for i, k, j in product(range(side), repeat=3)]
    edges = range(3*area)
    if side <= 2:
        # All subsets, including nonminimal and nonoptimal transversals.
        feasible = [s for s in range(1 << (3*area)) if all(s & t for t in triangles)]
        optimum = min(s.bit_count() for s in feasible)
        assert optimum == area
        minimizing = {s for s in feasible if s.bit_count() == optimum}
    else:
        # Each coordinate hits d of the d³ triangles. Consequently reaching
        # the lower bound d² requires disjoint triangle covers. Branch at the
        # first uncovered triangle over its three incident coordinates.
        covers = [sum(1 << t for t, triangle in enumerate(triangles)
                      if triangle & (1 << e)) for e in edges]
        assert all(c.bit_count() == side for c in covers)
        universe = (1 << len(triangles)) - 1
        minimizing = set()

        def exact_cover(covered, selected):
            missing = universe ^ covered
            if not missing:
                assert selected.bit_count() == area
                minimizing.add(selected)
                return
            pivot = missing & -missing
            for e, hits in enumerate(covers):
                if hits & pivot and not (hits & covered):
                    exact_cover(covered | hits, selected | (1 << e))

        exact_cover(0, 0)
    classified = set()
    for bank, split in product(range(3), range(1 << side)):
        sites = 0
        for label in range(side):
            if split & (1 << label):
                selected = (bank*area + side*label + j for j in range(side))
            else:
                selected = (((bank-1) % 3)*area + side*i + label for i in range(side))
            for site in selected:
                sites |= 1 << site
        classified.add(sites)
    assert len(classified) == 3*(1 << side)-3
    assert minimizing == classified
    return len(minimizing)


if __name__ == "__main__":
    verdicts, size, count = physical_truth_table()
    checks = check_field(verdicts)
    print(f"side 2: {size} bytes, 41 declared names, {count} proper clauses, 15 editable bits")
    print(f"{len(verdicts)} files: {sum(verdicts)} unique models, "
          f"{len(verdicts)-sum(verdicts)} unsatisfiable")
    print(f"{checks} F4 contractions across all 8 fully supported selector settings")
    size, names, count, accepted, terms = check_one_hot()
    print(f"one-hot side 2: {size} bytes, {names} declared names, {count} proper clauses")
    print(f"4096 files, {accepted} unique-model files, all at physical distance 3 in the cube")
    print(f"79 zero lower coefficients and {terms} integer cubic coefficients checked")
    accepted, ambiguous, models, compared = check_free_selectors(verdicts)
    print(f"free side 2: {accepted} SAT files of 4096, {ambiguous} with multiple models, "
          f"{models} models across all files")
    print(f"{compared} integer coefficients through degree 5 match the sparse cap and edge unions")
    for side in (1, 2, 3):
        minimizers = triangle_transversals(side)
        method = "all subsets" if side <= 2 else "exact covers of triangles"
        print(f"side {side}: minimum {side**2}, {minimizers} minimizing transversals ({method})")
