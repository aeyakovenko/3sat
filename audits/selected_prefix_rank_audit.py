"""Finite checks for private coordinate assignments after a fixed input prefix."""

from itertools import combinations
from math import comb


def cube_masks(width):
    """Group monomial and cylinder truth tables by their degree."""
    points = range(1 << width)
    monomials = [[] for _ in range(width + 1)]
    cylinders = [[] for _ in range(width + 1)]
    for mask in points:
        degree = mask.bit_count()
        cells = {}
        for point in points:
            value = point & mask
            cells[value] = cells.get(value, 0) | (1 << point)
        monomials[degree].append(cells[mask])
        cylinders[degree].extend(cells.values())
    return monomials, cylinders


def reduce_vector(vector, basis):
    """Reduce a bit-packed column by an echelon basis over the two-element field."""
    while vector:
        leader = vector.bit_length() - 1
        if not basis[leader]:
            break
        vector ^= basis[leader]
    return vector


def check_cells(width):
    monomials, cylinders = cube_masks(width)
    npoints = 1 << width
    rank_limits = [sum(comb(width, j) for j in range(r + 1))
                   for r in range(width + 1)]
    for cell in range(1 << npoints):
        basis = [0] * npoints
        rank = 0
        private = 0
        for degree in range(width + 1):
            for monomial in monomials[degree]:
                residual = reduce_vector(monomial & cell, basis)
                if residual:
                    basis[residual.bit_length() - 1] = residual
                    rank += 1
            for cylinder in cylinders[degree]:
                restriction = cylinder & cell
                if restriction.bit_count() == 1:
                    # A private assignment gives its point's unit vector.
                    assert reduce_vector(restriction, basis) == 0
                    private |= restriction
            assert private.bit_count() <= rank <= rank_limits[degree]
        assert private == cell
    return 1 << npoints


def check_weight_layers(width):
    points = range(1 << width)
    for weight in range(width + 1):
        layer = [p for p in points if p.bit_count() == weight]
        for p in layer:
            smallest = min(mask.bit_count() for mask in points
                           if all((p ^ q) & mask for q in layer if p != q))
            assert smallest == min(weight, width - weight)
    return 1 << width


def affine_code():
    """Truth tables of the affine functions on three bits, the [8,4,4] code."""
    return {sum((constant ^ ((linear & x).bit_count() % 2)) << x
                for x in range(8))
            for linear in range(8) for constant in (0, 1)}


def run_weight_then_suffix(word, width, suffix_lookup):
    """Input is available only through read(). The live cut state is the weight."""
    reads = []

    def read(i):
        reads.append(i)
        return (word >> i) & 1

    weight = sum(read(i) for i in range(width))
    suffix = sum(read(i) << (i - width) for i in range(width, 8))
    expected = suffix_lookup.get(suffix)
    if expected is None or expected.bit_count() != weight:
        return False, weight, reads
    minority = int(weight <= width - weight)
    for i in range(width):
        if ((expected >> i) & 1) == minority and read(i) != minority:
            return False, weight, reads
    return True, weight, reads


def check_code_runs():
    code = affine_code()
    assert len(code) == 16
    assert min((x ^ y).bit_count() for x, y in combinations(code, 2)) == 4
    assert all((x & y).bit_count() % 2 == 0 for x in code for y in code)
    # Self-orthogonality and dimension four imply dual distance four as well.
    runs = 0
    for width in (1, 2, 3):
        prefix_mask = (1 << width) - 1
        suffix_lookup = {x >> width: x & prefix_mask for x in code}
        assert len(suffix_lookup) == len(code)
        for prefix in range(1 << width):
            assert sum((x & prefix_mask) == prefix for x in code) == 16 >> width
        for word in range(256):
            accepted, weight, reads = run_weight_then_suffix(word, width, suffix_lookup)
            assert accepted == (word in code)
            assert reads[:8] == list(range(8))
            if accepted:
                rereads = set(reads[8:])
                assert len(rereads) == len(reads) - 8 == min(weight, width - weight)
                prefix = word & prefix_mask
                probe_mask = sum(1 << i for i in rereads)
                assert all((prefix ^ q) & probe_mask for q in range(1 << width)
                           if q != prefix and q.bit_count() == weight)
            runs += 1
    return runs


def greedy_linear_cover(width, radius):
    points = set(range(1 << width))
    ball = {p for p in points if p.bit_count() <= radius}
    centers = {0}
    uncovered = points - ball
    while uncovered:
        def remainder(shift):
            return {p for p in uncovered if p ^ shift in uncovered}

        shift = min(sorted(points), key=lambda v: len(remainder(v)))
        remaining = remainder(shift)
        assert len(remaining) * len(points) <= len(uncovered) ** 2
        assert shift not in centers and len(remaining) < len(uncovered)
        centers |= {c ^ shift for c in centers}
        uncovered = remaining
        assert uncovered == points - {c ^ error for c in centers for error in ball}
    return sorted(centers)


def check_center_verification(width):
    """A center ID and distance suffice with at most radius post-cut rereads."""
    points = range(1 << width)
    pairs = 0
    for radius in range(width + 1):
        centers = greedy_linear_cover(width, radius)
        for prefix in points:
            center_id = min(range(len(centers)),
                            key=lambda i: (prefix ^ centers[i]).bit_count())
            center = centers[center_id]
            distance = (prefix ^ center).bit_count()
            assert distance <= radius
            for predicted in points:
                mismatches = predicted ^ center
                accepted = mismatches.bit_count() == distance
                reads = 0
                if accepted:
                    for bit in range(width):
                        if mismatches >> bit & 1:
                            reads += 1
                            if (prefix ^ predicted) >> bit & 1:
                                accepted = False
                                break
                assert accepted == (predicted == prefix)
                assert reads <= distance
                if accepted:
                    assert reads == distance
                pairs += 1
    return pairs


if __name__ == "__main__":
    cells = sum(check_cells(width) for width in range(5))
    layer_points = sum(check_weight_layers(width) for width in range(9))
    runs = check_code_runs()
    center_pairs = sum(check_center_verification(width) for width in range(7))
    print(f"{cells} cells, {layer_points} weight-layer points, {runs} code runs, "
          f"{center_pairs} center/prefix comparisons checked")
