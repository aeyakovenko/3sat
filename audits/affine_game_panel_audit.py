"""Check coordinate deletion for the simplex-with-private-spaces examples over F₂."""

from itertools import combinations


def span(generators):
    points = {0}
    for v in generators:
        points.update(tuple(z ^ v for z in points))
    return points


def encode_in_basis(basis):
    # Each eliminated vector keeps its coefficient mask in the original basis.
    pivots = {}
    for i, v in enumerate(basis):
        coeffs = 1 << i
        while v:
            lead = v.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = v, coeffs
                break
            w, wc = pivots[lead]
            v, coeffs = v ^ w, coeffs ^ wc
        else:
            raise ValueError('dependent basis')

    def coordinates(v):
        coeffs = 0
        while v:
            w, wc = pivots[v.bit_length() - 1]
            v, coeffs = v ^ w, coeffs ^ wc
        return coeffs

    assert [coordinates(v) for v in basis] == [1 << i for i in range(len(basis))]
    return coordinates


def examples(m, a):
    assert 2 <= m <= a + 2
    simplex = [0, *(1 << i for i in range(m - 1))]
    private_dim = a - m + 2
    basis = list(simplex[1:])
    rows = []
    for i, excluded in enumerate(simplex):
        facet = simplex[:i] + simplex[i+1:]
        base = facet[0]
        directions = [v ^ base for v in facet[1:]]
        for j in range(private_dim):
            v = 1 << (m - 1 + i*private_dim + j)
            directions.append(v)
            basis.append(excluded ^ base ^ v)
        rows.append({base ^ z for z in span(directions)})
    assert all(len(row) == 1 << a for row in rows)
    return basis, rows


def compatible(rows, mask):
    if not rows:
        return True
    images = [{p & mask for p in row} for row in rows]
    return bool(set.intersection(*images))


def sharp_checks():
    examples_checked = 0
    one_missing = 0
    full_subsets = 0
    for a in range(8):
        for m in range(2, a + 3):
            basis, raw = examples(m, a)
            d = m - 1 + m*(a-m+2)
            assert len(basis) == d
            coords = encode_in_basis(basis)
            rows = [{coords(v) for v in row} for row in raw]
            full = (1 << d) - 1
            assert not compatible(rows, full)
            for i in range(m):
                assert compatible(rows[:i] + rows[i+1:], full)
            for k in range(d):
                assert compatible(rows, full ^ (1 << k))
            examples_checked += 1
            one_missing += d + m
            if d + m <= 11:
                for rmask in range(1 << m):
                    for cmask in range(1 << d):
                        any_missing = rmask != (1 << m)-1 or cmask != full
                        selected = [row for i, row in enumerate(rows) if rmask >> i & 1]
                        assert compatible(selected, cmask) == any_missing
                        full_subsets += 1
    return examples_checked, one_missing, full_subsets


def all_affine_flats(d, a):
    allowed = range(1 << d)
    linear = {frozenset({0})}
    for _ in range(a):
        linear = linear | {frozenset(U | {u ^ x for u in U}) for U in linear for x in allowed}
    return {frozenset(u ^ x for u in U) for U in linear for x in allowed}


def small_pairs():
    checked = 0
    for d in range(1, 5):
        flats = all_affine_flats(d, min(2, d))
        masks = sorted(range(1 << d), key=int.bit_count)
        images = {U: [{x & mask for x in U} for mask in masks] for U in flats}
        for U, V in combinations(flats, 2):
            if not U.isdisjoint(V):
                continue
            s = next(mask.bit_count() for mask, u, v in zip(masks, images[U], images[V])
                     if u.isdisjoint(v))
            assert s <= (len(U).bit_length()-1) + (len(V).bit_length()-1) + 1
            checked += 1
    return checked


def wrong_coordinate_example():
    basis, rows = examples(2, 1)
    # Dot products with basis vectors do not in general read their coefficients.
    as_queries = lambda v: sum(((v & b).bit_count() % 2) << i for i, b in enumerate(basis))
    wrong = [{as_queries(v) for v in row} for row in rows]
    assert not compatible(wrong, 1)
    assert compatible([{encode_in_basis(basis)(v) for v in row} for row in rows], 1)


if __name__ == '__main__':
    instances, deletion_tests, restrictions = sharp_checks()
    print(f'{instances} sharp examples; {deletion_tests} single deletions; '
          f'{restrictions} full row/column restrictions on small examples')
    print(f'{small_pairs()} disjoint affine-flat pairs of dimension ≤2 in up to four bits')
    wrong_coordinate_example()
    print('Basis-vector queries fail at (m,a)=(2,1); dual queries pass.')
