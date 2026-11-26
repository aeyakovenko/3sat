"""Finite checks for the one- and two-old-variable clause batch theorems."""

from collections import Counter, deque
from itertools import combinations, combinations_with_replacement, product
from random import Random
from math import gcd


def queued_core(mask, triples):
    incident = [set() for _ in range(12)]
    for i, triangle in enumerate(triples):
        if mask >> i & 1:
            for v in triangle:
                incident[v].add(i)
    queue = deque(v for v, rows in enumerate(incident) if 0 < len(rows) <= 2)
    while queue:
        v = queue.popleft()
        batch = set(incident[v])
        if not 1 <= len(batch) <= 2:
            continue
        names = {x for i in batch for x in triples[i]}
        if sum(bool(incident[x] - batch) for x in names) > 2:
            continue
        for i in batch:
            mask ^= 1 << i
            for x in triples[i]:
                incident[x].remove(i)
                if len(incident[x]) in (1, 2):
                    queue.append(x)
    return mask


def verify_structural_optimum():
    # The first and last support denote distinct signed clauses on the same triple.
    triples = [(0, 1, 2), (2, 3, 4), (4, 5, 6), (0, 2, 7), (8, 9, 10),
               (0, 3, 5), (6, 7, 8), (0, 1, 2), (1, 6, 8), (8, 10, 11)]
    total = 1 << len(triples)
    vertices = [0] * total
    optimum = [0] * total
    residual = [0] * total
    for mask in range(1, total):
        bit = mask & -mask
        vertices[mask] = vertices[mask ^ bit] | sum(1 << v for v in triples[bit.bit_length()-1])
        best = mask.bit_count()
        cores = set()
        batch = mask
        while batch:
            old = mask ^ batch
            exterior = (vertices[old] & vertices[batch]).bit_count()
            if exterior <= 1:
                best = min(best, max(optimum[old], batch.bit_count()))
            if exterior <= 2 and batch.bit_count() <= 2:
                cores.add(residual[old])
            batch = (batch - 1) & mask
        optimum[mask] = best
        if not cores:
            cores.add(mask)
        assert len(cores) == 1
        residual[mask] = cores.pop()
        assert queued_core(mask, triples) == residual[mask]
        chosen = [triangle for i, triangle in enumerate(triples) if mask >> i & 1]
        # Independently test whether any one vertex deletion can separate two
        # triangle interiors; only distinct biconnected blocks are separable.
        signatures = [[] for _ in chosen]
        for deleted in range(-1, 12):
            label = list(range(12))
            for triangle in chosen:
                rest = [v for v in triangle if v != deleted]
                labels = {label[v] for v in rest}
                target = min(labels)
                label = [target if x in labels else x for x in label]
            for signature, triangle in zip(signatures, chosen):
                signature.append(label[next(v for v in triangle if v != deleted)])
        block_max = max(Counter(map(tuple, signatures)).values())
        assert optimum[mask] == block_max
    return total


def verify_two_row_projections():
    # Two possible old variables and up to six fresh ones cover all union types.
    one_rows = []
    for scope in combinations(range(8), 3):
        for signs in product((0, 1), repeat=3):
            truth = sum(1 << word for word in range(256)
                        if any(((word >> v) & 1) == s for v, s in zip(scope, signs)))
            one_rows.append((sum(1 << v for v in scope), truth))
    boundaries = [sum(1 << word for word in range(old, 256, 4)) for old in range(4)]
    tested = filtering = 0
    for (scope_a, a), (scope_b, b) in combinations_with_replacement(one_rows, 2):
        unused_factor = 1 << (6 - ((scope_a | scope_b) >> 2).bit_count())
        fibers = [(a & b & group).bit_count() // unused_factor for group in boundaries]
        if 0 in fibers:
            assert sorted(fibers) == [0, 2, 2, 2]
            filtering += 1
        tested += 1
    return tested, filtering


def verify_affine_planes():
    # Translate the chosen model to zero. Vary the intersection of two triples
    # and all forbidden patterns distinct from zero on each triple.
    checked = 0
    for common in range(4):
        left = (0, 1, 2)
        right = tuple(range(common)) + tuple(range(3, 6-common))
        dimension = 6 - common
        def forbidden_words(row, pattern):
            return {w for w in range(1 << dimension) if
                    all((w >> v & 1) == (pattern >> i & 1) for i, v in enumerate(row))}
        for a, b in product(range(1, 8), repeat=2):
            bad = forbidden_words(left, a) | forbidden_words(right, b)
            attainable = any(all((word & normal).bit_count() & 1 for word in bad)
                             for normal in range(1, 1 << dimension))
            common_mask = (1 << common) - 1
            assert attainable == bool((a & common_mask) and (b & common_mask))
            checked += 1
    return checked


def verify_composed_affine_spaces():
    rng = Random(39057)
    for _trial in range(240):
        names = 0
        equations = []
        lower = 0
        for _step in range(12):
            old = rng.sample(range(names), rng.randrange(min(names, 2) + 1))
            rows = rng.randint(1, 2)
            count = 3 if rows == 1 else rng.randint(3, 6)
            fresh = list(range(names, names + count - len(old)))
            names += len(fresh)
            used = old + fresh
            rng.shuffle(used)
            supports = [used[:3]]
            if rows == 2:
                supports.append(used[3:] + rng.sample(used[:3], 6 - count))
            forbidden = [rng.randrange(1, 8) for row in supports]
            lower += 2 - len(old)
            if count == 3:
                normal = next(mask for mask in range(1, 1 << count)
                              if all(sum((mask >> used.index(v) & 1) * (p >> i & 1)
                                         for i, v in enumerate(row)) % 2
                                     for row, p in zip(supports, forbidden)))
                batch_eqs = [sum((normal >> i & 1) << v for i, v in enumerate(used))]
            else:
                batch_eqs = [1 << row[next(i for i in range(3) if p >> i & 1)]
                             for row, p in zip(supports, forbidden)]
            for bits in range(1 << count):
                word = sum((bits >> i & 1) << v for i, v in enumerate(used))
                if all((word & eq).bit_count() % 2 == 0 for eq in batch_eqs):
                    assert all(any((word >> v & 1) != (p >> i & 1) for i, v in enumerate(row))
                               for row, p in zip(supports, forbidden))
            equations.extend(batch_eqs)
        basis = {}
        for normal in equations:
            while normal and normal.bit_length() in basis:
                normal ^= basis[normal.bit_length()]
            if normal:
                basis[normal.bit_length()] = normal
        assert names - len(basis) >= lower
    return 240


def row_satisfied(row, assignment):
    return any(assignment[abs(lit)] == (lit > 0) for lit in row)


def padded(a, b, z):
    return [(a, b, z), (a, b, -z)]


def cleanup(z, anchor, p):
    return [(-z, anchor, p), (-z, anchor, -p), (z, anchor, -p)]


def private_count(rows, assigned):
    private = sorted({abs(lit) for row in rows for lit in row} - set(assigned))
    return sum(all(row_satisfied(row, assigned | dict(zip(private, values))) for row in rows)
               for values in product((False, True), repeat=len(private)))


def test_compiler(source, clean):
    next_id = 0
    def fresh():
        nonlocal next_id
        next_id += 1
        return next_id

    history = []
    anchor = fresh() if clean else None
    if clean:
        y, h, k = fresh(), fresh(), fresh()
        start = [padded(-anchor, y, h), padded(-anchor, -y, k)]
        start.extend(cleanup(v, anchor, fresh()) for v in (y, h, k))
        start_rows = [row for batch in start for row in batch]
        assert private_count(start_rows, {anchor: False}) == 1
        assert private_count(start_rows, {anchor: True}) == 0
        history.extend(start)
    signed_rows = []
    occurrences = {}
    local_vars = []
    for clause in source:
        row = []
        for literal in clause:
            name = fresh()
            occurrences.setdefault(abs(literal), []).append(name)
            local_vars.append(name)
            row.append(name if literal > 0 else -name)
        signed_rows.append(tuple(row))
        history.append([tuple(row)])

    factors = []
    for names in occurrences.values():
        for left, right in zip(names, names[1:]):
            for a, b in ((-left, right), (left, -right)):
                z = fresh()
                rows = padded(a, b, z)
                history.append(rows)
                factor = list(rows)
                if clean:
                    extra = cleanup(z, anchor, fresh())
                    history.append(extra)
                    factor.extend(extra)
                # Verify each private factor directly under all four endpoints.
                table = {}
                for x, y in product((False, True), repeat=2):
                    assignment = {abs(a): x, abs(b): y}
                    if clean:
                        assignment[anchor] = False
                    table[x, y] = private_count(factor, assignment)
                factors.append((abs(a), abs(b), table))

    previously_used = set()
    for batch in history:
        used = {abs(lit) for row in batch for lit in row}
        assert len(batch) <= 2 + int(clean) and len(used & previously_used) <= 2
        assert all(len(row) == len(set(map(abs, row))) == 3 for row in batch)
        previously_used |= used

    output_total = 0
    for values in product((False, True), repeat=len(local_vars)):
        assignment = dict(zip(local_vars, values))
        if all(row_satisfied(row, assignment) for row in signed_rows):
            count = 1
            for a, b, table in factors:
                count *= table[assignment[a], assignment[b]]
            output_total += count
    original_vars = sorted(occurrences)
    source_total = sum(all(row_satisfied(row, dict(zip(original_vars, word))) for row in source)
                       for word in product((False, True), repeat=len(original_vars)))
    assert output_total == source_total * (1 if clean else 1 << len(factors))


def verify_ordinary_model_minima():
    for v in (3, 4):
        cube_size = 1 << v
        flats = set()
        for support in combinations(range(v), 3):
            for signs in product((0, 1), repeat=3):
                excluded = sum(1 << x for x in range(cube_size)
                               if all((x >> i) & 1 == s for i, s in zip(support, signs)))
                # Flipping signs represents any surviving model by the origin.
                if excluded & 1 == 0:
                    flats.add(excluded)
        reachable = {0}
        for m in range(v + 6):
            actual = cube_size - max(mask.bit_count() for mask in reachable)
            expected = ((8-m) * (1 << (v-3)) if m <= 7
                        else 1 << max(0, v-m+4))
            assert actual == expected, (v, m, actual, expected)
            reachable.update({mask | flat for mask in reachable for flat in flats})


def verify_two_point_product_spaces():
    checked = 0
    for d in (1, 2):
        bits = d * d
        size = 1 << bits
        identity = sum(1 << (i*d+i) for i in range(d))

        def point(a, b):
            out = 0
            for i, j, k in product(range(d), repeat=3):
                if a & (1 << (i*d+k)) and b & (1 << (k*d+j)):
                    out ^= 1 << (i*d+j)
            return ((a << bits | b) << bits) | out

        graph = {point(a, b) for a, b in product(range(size), repeat=2)}
        for a, b in product(range(size), repeat=2):
            base = point(a, b)
            shift = base ^ point(a ^ identity, b ^ identity)
            allowed = {p ^ base for p in graph}
            directions = [x for x in allowed if x ^ shift in allowed]
            initial = frozenset((0, shift))
            seen = {initial}
            queue = deque([initial])
            while queue:
                space = queue.popleft()
                for x in directions:
                    if x in space:
                        continue
                    enlarged = space.union(y ^ x for y in space)
                    if enlarged <= allowed and enlarged not in seen:
                        seen.add(enlarged)
                        queue.append(enlarged)
            largest = max(map(len, seen))
            assert largest == 1 << (bits // 4 + 1), (d, a, b, largest)
            checked += 1
    return checked


def verify_modular_pads():
    for petals in range(1, 5):
        rows = [(1, 2, 3), (1, 2, -3)]
        rows.extend((3, 4+2*j, 5+2*j) for j in range(petals))
        for first, second in product((False, True), repeat=2):
            actual = private_count(rows, {1: first, 2: second})
            expected = 3**petals + 4**petals if first or second else 0
            assert actual == expected
            if petals == 1:
                by_pad = [private_count(rows, {1: first, 2: second, 3: z})
                          for z in (False, True)]
                assert by_pad[1] - by_pad[0] == int(first or second)
    for modulus in range(2, 513):
        phi = sum(gcd(a, modulus) == 1 for a in range(1, modulus))
        weight = (pow(3, phi, modulus) + pow(4, phi, modulus)) % modulus
        assert pow(weight, phi, modulus) == 1


def main():
    verify_modular_pads()
    verify_ordinary_model_minima()
    product_pairs = verify_two_point_product_spaces()
    structures = verify_structural_optimum()
    profiles, filtering = verify_two_row_projections()
    planes = verify_affine_planes()
    histories = verify_composed_affine_spaces()
    rows = [tuple(v * s for v, s in zip((1, 2, 3), signs))
            for signs in product((-1, 1), repeat=3)]
    sources = [(), *((row,) for row in rows), *combinations_with_replacement(rows, 2),
               (rows[0], (2, -4, 5), (1, 4, -6))]
    for source, clean in product(sources, (False, True)):
        test_compiler(source, clean)
    print(f"{structures} structural subsets and two-row residual cores, {profiles} two-row profiles "
          f"({filtering} filtering), {planes} affine profiles, {histories} composed affine "
          f"spaces, {2 * len(sources)} compiler model counts, {product_pairs} product pairs")


if __name__ == '__main__':
    main()
