"""Exhaust affine binary flats with a missing weight residue modulo three.

Each direction space is generated once in reduced row echelon form. Vectors
whose pivot coordinates are zero give exactly one representative per coset.
All dimensions below refer to the direction space of a nonempty affine flat.
"""

from itertools import combinations, product


def span(basis):
    points = [0]
    for row in basis:
        points += [v ^ row for v in points]
    return points


def echelon_spaces(m, dimension):
    for pivots in combinations(range(m), dimension):
        free = [j for j in range(m) if j not in pivots]
        representatives = span([1 << j for j in free])
        possible_rows = []
        for i in pivots:
            tails = span([1 << j for j in free if i < j])
            possible_rows.append([1 << i | tail for tail in tails])
        for basis in product(*possible_rows):
            yield basis, representatives


def gaussian_binomial(n, k):
    count = 1
    for i in range(k):
        count *= (1 << (n - i)) - 1
    for i in range(k):
        count //= (1 << (k - i)) - 1
    return count


def residue_mask(origin, points):
    mask = 0
    for v in points:
        mask |= 1 << ((origin ^ v).bit_count() % 3)
        if mask == 7:
            break
    return mask


def explicit_extremizer(m):
    """Return an origin and independent generators for the sharp examples."""
    if m == 0:
        return 0, []
    if m == 2:
        return 0, [3]
    if m % 2:
        origin, basis, start = 0, [1], 1
    else:
        # The odd coset of the even-weight subspace on four coordinates.
        origin, basis, start = 1, [3, 5, 9], 4
    for i in range(start, m, 2):
        origin |= 1 << i
        basis.append(3 << i)
    return origin, basis


def extremal_dimension(m):
    return {0: 0, 2: 1}.get(m, m // 2 + 1)


def census(m):
    flat_count = 0
    missing_by_dimension = []
    for d in range(m + 1):
        spaces = 0
        failures = 0
        for basis, representatives in echelon_spaces(m, d):
            spaces += 1
            directions = span(basis)
            flat_count += len(representatives)
            for origin in representatives:
                if residue_mask(origin, directions) != 7:
                    failures += 1
        assert spaces == gaussian_binomial(m, d)
        missing_by_dimension.append(failures)
    maximum = max(d for d, count in enumerate(missing_by_dimension) if count)
    assert maximum == extremal_dimension(m)
    return flat_count, maximum, missing_by_dimension[maximum]


def audit():
    for m in range(9):
        total, dimension, maximizers = census(m)
        print(
            f"m={m}: {total} affine flats; maximum {dimension}, "
            f"{maximizers} flats attain it"
        )
    for m in range(10):
        origin, basis = explicit_extremizer(m)
        directions = span(basis)
        assert len(set(directions)) == 1 << extremal_dimension(m)
        assert max(origin ^ v for v in directions) < 1 << m
        mask = residue_mask(origin, directions)
        assert mask != 7
        if m >= 8:
            print(
                f"m={m}: origin {origin}, basis {basis}, "
                f"missing residues {[r for r in range(3) if not (mask >> r) & 1]}"
            )


if __name__ == "__main__":
    audit()
