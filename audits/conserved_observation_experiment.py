"""Exhaustively check sparse conserved parities on small binary vector spaces."""

from itertools import combinations_with_replacement, product
from math import comb


def dot(left, right):
    return (left & right).bit_count() % 2


def extend(space, vector):
    return space.union(point ^ vector for point in space)


def all_subspaces(width):
    spaces = [frozenset({0})]
    seen = set(spaces)
    for space in spaces:
        for vector in range(1, 1 << width):
            if vector in space:
                continue
            larger = extend(space, vector)
            if larger not in seen:
                seen.add(larger)
                spaces.append(larger)
    return spaces


def conserved_parities(width, differences):
    return [mask for mask in range(1 << width)
            if all(dot(mask, difference) == 0 for difference in differences)]


def check_subspaces():
    # Independent totals from the Gaussian binomial coefficients at q = 2.
    expected_counts = (1, 2, 5, 16, 67, 374)
    outside_pairs = 0
    for width, expected in enumerate(expected_counts):
        spaces = all_subspaces(width)
        assert len(spaces) == expected
        for space in spaces:
            rank = len(space).bit_length() - 1
            assert len(space) == 1 << rank
            parities = conserved_parities(width, space)
            assert len(parities) == 1 << (width - rank)
            for contrast in range(1 << width):
                weights = [mask.bit_count() for mask in parities if dot(mask, contrast)]
                assert bool(weights) == (contrast not in space)
                if weights:
                    assert min(weights) <= rank + 1
                    outside_pairs += 1
    print(f"Checked {sum(expected_counts)} subspaces and {outside_pairs} outside contrasts")


def check_adjacent_differences():
    for width in range(1, 11):
        # Adjacent differences span the even-weight subspace. Separating
        # the first unit vector requires the parity of all coordinates.
        differences = [3 << j for j in range(width - 1)]
        space = frozenset({0})
        for vector in differences:
            space = extend(space, vector)
        assert len(space) == 1 << (width - 1)
        parities = conserved_parities(width, differences)
        separators = [mask for mask in parities if dot(mask, 1)]
        assert separators == [(1 << width) - 1]
    print("Adjacent differences attain rank + 1 in each width from 1 to 10")


def check_one_accept():
    # An arbitrary decoder sees only the answers to its conserved parities.
    # It can isolate 0 from every nonzero point exactly when their common
    # kernel is trivial. Check every possible row space of these parities.
    for width in range(6):
        for rows in all_subspaces(width):
            kernel = conserved_parities(width, rows)
            assert (kernel == [0]) == (len(rows) == 1 << width)
    print("Isolating zero from all other points requires full parity rank through width 5")


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def check_equality():
    for size in range(1, 33):
        equal_rows = [1 << i for i in range(size)]
        unequal_rows = [((1 << size) - 1) ^ row for row in equal_rows]
        assert binary_rank(equal_rows) == size
        assert binary_rank(unequal_rows) == size - size % 2
    print("Checked binary ranks of equality and its complement at matrix sizes 1 to 32")


def project(vector, direction):
    """Quotient by a one-dimensional kernel, dropping its pivot coordinate."""
    pivot = 1 << (direction.bit_length() - 1)
    if vector & pivot:
        vector ^= direction
    low_bits = pivot - 1
    return (vector & low_bits) | ((vector >> 1) & ~low_bits)


def span_coordinates(contrasts):
    coordinates = {0: 0}
    for vector in sorted(contrasts):
        if vector not in coordinates:
            next_bit = len(coordinates)
            coordinates.update({v ^ vector: z | next_bit for v, z in coordinates.items()})
    dimension = len(coordinates).bit_length() - 1
    return dimension, {coordinates[v] for v in contrasts}


def route_by_merging(dimension, contrasts):
    while len(contrasts) < (1 << dimension) - 1:
        missing = next(a ^ b for a in contrasts for b in contrasts
                       if a < b and a ^ b not in contrasts)
        previous_surplus = len(contrasts) - dimension
        contrasts = {project(v, missing) for v in contrasts}
        dimension -= 1
        assert all(0 < v < 1 << dimension for v in contrasts)
        assert binary_rank(contrasts) == dimension
        assert len(contrasts) - dimension <= previous_surplus
    return dimension


def surplus_bound(dimension, count):
    return max(h for h in range(dimension + 1) if (1 << h) - 1 - h <= count - dimension)


def check_terminal_routing():
    checked = 0
    worst_rank = {}
    for width in range(5):
        nonzero = range(1, 1 << width)
        kernels = [(sum(1 << (v - 1) for v in space if v),
                    width - (len(space).bit_length() - 1)) for space in all_subspaces(width)]
        for subset in range(1 << len(nonzero)):
            contrasts = {v for v in nonzero if subset & (1 << (v - 1))}
            dimension, coordinates = span_coordinates(contrasts)
            count = len(contrasts)
            achieved = route_by_merging(dimension, coordinates)
            # Check the minimum independently over kernels in the original ambient space.
            optimum = min(codim for mask, codim in kernels if mask & subset == 0)
            assert optimum <= achieved <= surplus_bound(dimension, count)
            key = (dimension, count)
            worst_rank[key] = max(worst_rank.get(key, 0), optimum)
            checked += 1
    for dimension in range(5):
        for count in range(dimension, 1 << dimension):
            assert worst_rank[dimension, count] == surplus_bound(dimension, count)
    print(f"Checked merging quotients and optimal kernel ranks for all {checked} contrast sets")
    print(f"Exact worst-case surplus bound attained for all {len(worst_rank)} dimension/count pairs")


def gf8_multiply(left, right):
    result = 0
    while right:
        if right & 1:
            result ^= left
        left <<= 1
        if left & 8:
            left ^= 0b1011  # x³ + x + 1
        right >>= 1
    return result


def specialized_rank(diagonal, common, products, inverses):
    size = len(diagonal)
    rows = [[common] * size for _ in diagonal]
    for i, value in enumerate(diagonal):
        rows[i][i] ^= value
    rank = 0
    for column in range(size):
        pivot = next((j for j in range(rank, size) if rows[j][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = inverses[rows[rank][column]]
        for j in range(rank + 1, size):
            factor = products[inverse][rows[j][column]]
            for k in range(column, size):
                rows[j][k] ^= products[factor][rows[rank][k]]
        rank += 1
    return rank


def evaluated_forms(dimension):
    # Homogeneity allows the first nonzero coordinate to be normalized to 1.
    for point in product(range(8), repeat=dimension):
        if next((x for x in point if x), 0) == 1:
            values = [0]
            for x in point:
                values += [value ^ x for value in values]
            yield values


def check_generic_rank():
    products = [[gf8_multiply(a, b) for b in range(8)] for a in range(8)]
    inverses = [0] + [row.index(1) for row in products[1:]]
    checked = [0, 0]
    singular = 0
    for dimension in (2, 3):
        form_count = 1 << dimension
        evaluations = list(evaluated_forms(dimension))
        for size in range(1, 5):
            for diagonal in combinations_with_replacement(range(1, form_count), size):
                odd_forms = {d for d in diagonal if diagonal.count(d) % 2}
                for common in range(form_count):
                    best = 0
                    for values in evaluations:
                        rank = specialized_rank([values[d] for d in diagonal],
                                                values[common], products, inverses)
                        best = max(best, rank)
                        if best == size:
                            break
                    # Every minor has individual degrees <= 4 < |GF(8)|.
                    # A nonzero minor therefore survives at a field point.
                    deficient = odd_forms == {common}
                    assert best == size - int(deficient)
                    if size % 2 == 0:
                        assert best == size
                    checked[size % 2] += 1
                    singular += deficient
    print(f"Generic rank via GF(8): {checked[0]} even cases and {checked[1]} odd cases,"
          f" including {singular} singular matrices")


def check_terminal_matrix_bounds():
    systems = separated = common_reject = tight_common_reject = 0
    for width in (2, 3):
        points = range(1 << width)
        quotients = [(space, [min(value ^ w for w in space) for value in points])
                     for space in all_subspaces(width)]
        for table in product(points, repeat=4):
            # Row-major table entries are the feature vectors at 00, 01, 10, 11.
            matrices = []
            for coordinate in range(width):
                a, b, c, d = ((value >> coordinate) & 1 for value in table)
                matrices.append([a | (b << 1), c | (d << 1)])
            local_rank = max(binary_rank(rows) for rows in matrices)
            contrasts = [value ^ table[0] for value in table[1:]]
            for space, coset in quotients:
                systems += 1
                accepts = {coset[table[0]], coset[table[3]]}
                rejects = {coset[table[1]], coset[table[2]]}
                if accepts & rejects:
                    continue
                separated += 1
                pivots = binary_rank([*space, *contrasts])
                degree = (len(rejects) + 1).bit_length() - 1
                assert 2 <= sum(comb(pivots, j) * local_rank ** j
                                for j in range(1, degree + 1))
                if len(rejects) == 1:
                    assert 2 <= pivots * local_rank
                    common_reject += 1
                    tight_common_reject += pivots * local_rank == 2
    print(f"Checked {systems} two-by-two tables with transition subspaces,"
          f" including {separated} with disjoint verdict cosets")
    print(f"The common-rejection bound holds on {common_reject} systems,"
          f" with equality on {tight_common_reject}")


if __name__ == "__main__":
    check_subspaces()
    check_adjacent_differences()
    check_one_accept()
    check_equality()
    check_terminal_routing()
    check_generic_rank()
    check_terminal_matrix_bounds()
