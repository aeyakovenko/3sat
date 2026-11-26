"""Affine-test/affine-output Boolean decision lists on at most four bits.

Truth table bit x is the value on the binary coordinate vector x. A test
returns its affine leaf on one hyperplane and continues on the other.
The census generates all truth tables this way. A separate restriction
recurrence checks membership and the minimum number of tests on every table.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations


def bit(i):
    return 1 << i


def parity(x):
    return x.bit_count() & 1


def cube(d):
    return bit(bit(d)) - 1


@lru_cache(None)
def affines(d):
    return frozenset(sum(parity(x & a) << x for x in range(bit(d))) ^ (cube(d) if b else 0)
                     for a in range(bit(d)) for b in (0, 1))


@lru_cache(None)
def side_points(d, normal, side):
    """A chart onto one hyperplane, retaining all coordinates except the pivot."""
    pivot = normal & -normal
    out = []
    for t in range(bit(d-1)):
        x = (t & (pivot-1)) | ((t & ~(pivot-1)) << 1)
        out.append(x | (pivot if parity(x & normal) != side else 0))
    return tuple(out)


def scatter(table, points):
    return sum(((table >> i) & 1) << x for i, x in enumerate(points))


def gather(table, points):
    return sum(((table >> x) & 1) << i for i, x in enumerate(points))


def generate(d, smaller_depths):
    valid = {a: 0 for a in affines(d)}
    for normal in range(1, bit(d)):
        for side in (0, 1):
            leave = side_points(d, normal, side)
            cont = side_points(d, normal, 1-side)
            leaves = [scatter(a, leave) for a in affines(d-1)]
            for old, depth in smaller_depths.items():
                branch = scatter(old, cont)
                for leaf in leaves:
                    table = branch | leaf
                    if table not in valid or valid[table] > depth+1:
                        valid[table] = depth+1
    return valid


@lru_cache(None)
def small_gather_tables(points):
    """Gather at most a sixteen-bit truth table in two byte lookups."""
    return ([gather(b, points) for b in range(256)],
            [gather(b << 8, points) for b in range(256)])


def check_census(d, values, expected_smaller):
    # A distinct direction: classify every subset, including all rejected
    # tables. A side is affine iff its ANF has no coefficient above degree 1.
    def direct_affine(f):
        for i in range(d-1):
            for j in range(i):
                for z in range(bit(d-1)):
                    if ((f >> z) ^ (f >> (z ^ bit(i))) ^
                            (f >> (z ^ bit(j))) ^ (f >> (z ^ bit(i) ^ bit(j)))) & 1:
                        return False
        return True

    is_aff = [direct_affine(f) for f in range(bit(bit(d-1)))]
    assert {i for i, yes in enumerate(is_aff) if yes} == affines(d-1)
    splits = [(small_gather_tables(side_points(d, n, 0)), small_gather_tables(side_points(d, n, 1)))
              for n in range(1, bit(d))]
    for f in range(bit(bit(d))):
        depth = 0 if f in affines(d) else None
        low, high = f & 255, f >> 8
        if depth is None:
            for (l0,h0), (l1,h1) in splits:
                left, right = l0[low] | h0[high], l1[low] | h1[high]
                for leaf, remainder in ((left, right), (right, left)):
                    if is_aff[leaf] and remainder in expected_smaller:
                        candidate = 1 + expected_smaller[remainder]
                        depth = candidate if depth is None else min(depth, candidate)
                if depth == 1:
                    break
        assert depth == values.get(f), (d, f, depth, values.get(f))


def affine_flats(d):
    """Generate all binary linear spaces from independent coordinate vectors
    (the candidates extend by arbitrary new vectors), then all their cosets."""
    values = range(bit(d))
    linear = {frozenset((0,))}
    while linear:
        next_linear = set()
        for space in linear:
            remaining = set(values)
            while remaining:
                v = min(remaining)
                shifted = {v ^ x for x in space}
                remaining.difference_update(shifted)
                yield sum(bit(x) for x in shifted)
                if v:
                    next_linear.add(space | shifted)
        linear = next_linear


def affine_span_dim(points):
    points = list(points)
    if not points:
        return -1
    span = {0}
    for x in points:
        dx = x ^ points[0]
        if dx not in span:
            span.update([y ^ dx for y in span])
    return len(span).bit_length()-1


def proper_clauses(d):
    return [cube(d) ^ sum(bit(x) for x in range(bit(d)) if (x & scope) == falsifying)
            for positions in combinations(range(d), 3)
            for scope in [sum(bit(i) for i in positions)]
            for falsifying in range(bit(d)) if not (falsifying & ~scope)]


def check_four(d4):
    missing = [f for f in range(bit(16)) if f not in d4]
    by_weight = Counter(f.bit_count() for f in missing)
    least = min(by_weight)
    simplex = sum(bit(x) for x in (0,1,2,4,8))
    assert least == 5 and simplex not in d4
    for support in combinations(range(16), 5):
        f = sum(bit(x) for x in support)
        assert (f not in d4) == (affine_span_dim(support) == 4)
    assert by_weight[5] == 2688
    cs = proper_clauses(4)
    bad_counts = []
    for count in range(4):
        rejected = 0
        for rows in combinations(cs, count):
            table = cube(4)
            for row in rows:
                table &= row
            rejected += table not in d4
        bad_counts.append(rejected)
    assert bad_counts == [0,0,0,768]
    # The three forbidden edges below have a five-point affine simplex as
    # their union. Each edge fixes three coordinates, hence gives one clause.
    edges = [(0,1), (0,2), (8,12)]
    witness = cube(4)
    for a,b in edges:
        row = cube(4) ^ (bit(a) | bit(b))
        assert row in cs
        witness &= row
    signed_example = [(2,3,4), (1,3,4), (1,2,-4)]
    direct = sum(bit(x) for x in range(16)
                 if all(any(bool(x & bit(abs(t)-1)) == (t>0) for t in row)
                        for row in signed_example))
    assert direct == witness and witness not in d4 and (cube(4) ^ witness).bit_count() == 5
    assert affine_span_dim(x for x in range(16) if not witness & bit(x)) == 4
    return dict(sorted(by_weight.items())), bad_counts


def restriction_depth(table, d, censuses):
    if d <= 4:
        return censuses[d].get(table)
    if table in affines(d):
        return 0
    possible = []
    for n in range(1, bit(d)):
        pair = [gather(table, side_points(d, n, s)) for s in (0,1)]
        for leaf, rest in (pair, reversed(pair)):
            if leaf in affines(d-1):
                result = restriction_depth(rest, d-1, censuses)
                if result is not None:
                    possible.append(result + 1)
    return min(possible) if possible else None


def clause_overlap(censuses):
    # Every pair of proper clauses up to variable permutations, sign flips,
    # and omission of unused variables. A is positive on three named bits;
    # B shares t of those names and disagrees on k signs in the overlap.
    result = {}
    for t in range(4):
        d = 6-t
        first, second = 7, (bit(t)-1) | ((bit(3-t)-1) << 3)
        for k in range(t+1):
            raw = 0
            for x in range(bit(d)):
                if (x & first) and ((x ^ (bit(k)-1)) & second):
                    raw |= bit(x)
            result[t,k] = restriction_depth(raw, d, censuses)
    assert {key for key, dep in result.items() if dep is None} == {(0,0), (1,0), (1,1)}
    return result


def six_bit_flats():
    d = 6
    accepted = sum(bit(x) for x in range(64) if (x & 7) and (x >> 3))
    dimensions, accept_flats, slices = Counter(), Counter(), Counter()
    for flat in affine_flats(d):
        dim = flat.bit_count().bit_length()-1
        dimensions[dim] += 1
        inside = (accepted & flat).bit_count()
        if inside == flat.bit_count():
            accept_flats[dim] += 1
        if dim == 5:
            slices[inside] += 1
    # Gaussian binomial [6 k]_2 times the number of cosets.
    assert [dimensions[i] for i in range(7)] == [64,2016,10416,11160,2604,126,1]
    assert max(accept_flats) == 4
    assert slices == {21:14,28:14,24:49,25:49}
    return dict(sorted(accept_flats.items())), dict(sorted(slices.items()))


def main():
    censuses = [{a:0 for a in affines(0)}]
    for d in range(1,5):
        result = generate(d, censuses[-1])
        check_census(d, result, censuses[-1])
        censuses.append(result)
    for d, valid in enumerate(censuses):
        print(f"{d} bits: {len(valid)}/{bit(bit(d))} lists; "
              f"minimum test counts {dict(sorted(Counter(valid.values()).items()))}")
    weight, bad = check_four(censuses[4])
    print("Excluded four-bit functions by weight:", weight)
    print("Excluded conjunctions of k distinct proper clauses, k=0,1,2,3:", bad)
    print("A minimum four-variable obstruction has signed clauses (2,3,4), (1,3,4), (1,2,-4).")
    print("Two-clause minimum tests by (shared variables, opposed shared signs):", clause_overlap(censuses))
    flats, slices = six_bit_flats()
    print("Two disjoint positive clauses: contained flats by dimension:", flats)
    print("Hyperplanes by number of accepted points:", slices)


if __name__ == '__main__':
    main()
