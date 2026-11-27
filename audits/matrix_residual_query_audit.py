"""Finite checks for witnesses and signed line queries of binary matrix residuals."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb


def rows_of(matrix, d):
    mask = (1 << d) - 1
    return [(matrix >> (i * d)) & mask for i in range(d)]


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row
                break
            row ^= pivots[p]
    return len(pivots)


def common_first_markers(rows):
    occupied_columns = 0
    markers = []
    for i, row in enumerate(rows):
        first = row & -row
        if first and not (first & occupied_columns):
            markers.append((i, first.bit_length() - 1))
        occupied_columns |= row
    return markers


def right_answer(rows, column_vector):
    result = 0
    for i, row in enumerate(rows):
        result |= ((row & column_vector).bit_count() % 2) << i
    return result


def left_answer(rows, row_vector):
    result = 0
    for i, row in enumerate(rows):
        if (row_vector >> i) & 1:
            result ^= row
    return result


def subset_sizes(items):
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def zero_rank_interpolant(ranks, freivalds):
    value = Fraction(1)
    for r in ranks:
        root = Fraction(1, 2**r)
        value *= (freivalds - root) / (1 - root)
    return value


def exhaustive_residuals():
    matrices = markers_seen = interpolation_checks = 0
    max_markers_by_rank = {}
    for d in range(1, 5):
        output_at_rank = {}
        for r in range(d + 1):
            p0 = Fraction(1, 2**r)
            output_at_rank[r] = []
            for subset in subset_sizes(tuple(range(1, d + 1))):
                if r == 0 or r in subset:
                    value = zero_rank_interpolant(subset, p0)
                    assert value == int(r == 0)
                    output_at_rank[r].append(value)
        max_markers = [0] * (d + 1)
        for matrix in range(1 << (d*d)):
            rows = rows_of(matrix, d)
            markers = common_first_markers(rows)
            direct = [(i, j) for i, row in enumerate(rows) for j in range(d)
                      if (row >> j) & 1 and row % (1 << j) == 0
                      and all(not ((prior >> j) & 1) for prior in rows[:i])]
            assert markers == direct
            k = len(markers)
            rank = binary_rank(rows)
            assert (k > 0) == bool(matrix) and k <= rank
            # Binomial coefficients count the canonically ordered guessed subsets.
            assert sum((-1)**j * comb(k, j) for j in range(k+1)) == int(not matrix)
            zero_answers = sum(right_answer(rows, v) == 0 for v in range(1 << d))
            assert zero_answers == 1 << (d-rank)
            max_markers[rank] = max(max_markers[rank], k)
            interpolation_checks += len(output_at_rank[rank])
            markers_seen += k
            matrices += 1
        assert max_markers == list(range(d+1))
        max_markers_by_rank[d] = max_markers
    print(f"residuals {matrices}, common-first markers {markers_seen}, "
          f"promised interpolation evaluations {interpolation_checks}")
    print(f"largest marker counts by rank {max_markers_by_rank}")


def block_measure(size):
    if size == 1:
        return {0: 1, 1: -1}
    coefficients = {1: 1, 2: 1, 3: -1}
    weights = {0: 1}
    for u, a in coefficients.items():
        for v, b in coefficients.items():
            matrix = sum(v << (2*i) for i in range(2) if (u >> i) & 1)
            assert matrix not in weights
            weights[matrix] = -a*b
    return weights


def tensor_measure(d, sizes):
    weights = {0: 1}
    offset = 0
    for size in sizes:
        local = block_measure(size)
        following = {}
        for block, coefficient in local.items():
            embedded = sum(row << (d*(offset+i)+offset)
                           for i, row in enumerate(rows_of(block, size)))
            for matrix, weight in weights.items():
                assert (matrix | embedded) not in following
                following[matrix | embedded] = weight*coefficient
        weights = following
        offset += size
    return weights


def cylinder_checks():
    subsets_checked = cylinders_with_support = 0
    for d in range(1, 6):
        for k in range(1, d+1):
            target = min(d, 2*k)
            blocks = [2] * (target // 2) + [1] * (target % 2)
            measure = tensor_measure(d, blocks)
            assert measure[0] == 1 and sum(measure.values()) == 0
            lines = {}
            for matrix in measure:
                rows = rows_of(matrix, d)
                assert binary_rank(rows) <= k
                lines[matrix] = rows + [right_answer(rows, 1 << j) for j in range(d)]
            # Every adaptive leaf is one such fixed cylinder. Check all its nonempty fibers.
            for count in range(target):
                for selected in combinations(range(2*d), count):
                    marginals = Counter()
                    for matrix, weight in measure.items():
                        marginals[tuple(lines[matrix][j] for j in selected)] += weight
                    assert all(value == 0 for value in marginals.values())
                    subsets_checked += 1
                    cylinders_with_support += len(marginals)
    print(f"coordinate line sets {subsets_checked}, occupied cylinder fibers {cylinders_with_support}")


def vector_cylinder_parities():
    line_sets = occupied = 0
    for d in range(1, 5):
        # All direction sets through d=3. At d=4 use one representative per
        # pair of dimensions after invertible changes of row and column bases.
        if d < 4:
            directions = [(query, v) for query in (left_answer, right_answer)
                          for v in range(1, 1 << d)]
            selected = [idx for count in range(d)
                        for idx in combinations(range(len(directions)), count)]
        else:
            directions = [(query, 1 << i) for query in (left_answer, right_answer)
                          for i in range(d)]
            selected = [tuple(range(a)) + tuple(range(d, d+b))
                        for a in range(d) for b in range(d-a)]
        domain = []
        for m in range(1 << (d*d)):
            rows = rows_of(m, d)
            domain.append((binary_rank(rows), [query(rows, v) for query, v in directions]))
        for k in range(1, d+1):
            support = [answers for rank, answers in domain if rank <= k]
            for idx in selected:
                if len(idx) >= min(d, 2*k):
                    continue
                counts = Counter(tuple(answers[j] for j in idx) for answers in support)
                assert all(value % 2 == 0 for value in counts.values())
                line_sets += 1
                occupied += len(counts)
    print(f"characteristic-two vector line sets {line_sets}, occupied even fibers {occupied}")


@lru_cache(maxsize=None)
def gaussian_binomial(n, j):
    if j < 0 or j > n:
        return 0
    if j == 0:
        return 1
    return gaussian_binomial(n-1, j) + 2**(n-j)*gaussian_binomial(n-1, j-1)


def solve_mod_prime(matrix, rhs, prime):
    rows = [[x % prime for x in row+[b]] for row, b in zip(matrix, rhs)]
    for j in range(len(rows)):
        pivot = next(i for i in range(j, len(rows)) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        factor = pow(rows[j][j], -1, prime)
        rows[j] = [factor*x % prime for x in rows[j]]
        for i, row in enumerate(rows):
            if i != j:
                scale = row[j]
                rows[i] = [(x-scale*y) % prime for x, y in zip(row, rows[j])]
    return [row[-1] for row in rows]


def kernel_subspace_checks():
    # Enumerate the actual subspaces, including zero and the whole space.
    d = 3
    vectors = range(1 << d)
    subspaces = []
    for mask in range(1 << (1 << d)):
        members = [v for v in vectors if (mask >> v) & 1]
        if 0 in members and all((mask >> (x ^ y)) & 1 for x in members for y in members):
            subspaces.append((mask, len(members).bit_length()-1))
    assert len(subspaces) == 16
    for m in range(1 << (d*d)):
        rows = rows_of(m, d)
        kernel = sum(1 << v for v in vectors if not right_answer(rows, v))
        n = d-binary_rank(rows)
        moments = Counter(j for space, j in subspaces if not (space & ~kernel))
        assert all(moments[j] == gaussian_binomial(n, j) for j in range(d+1))

    solved = 0
    for d in range(1, 10):
        for k in range(1, d+1):
            D = d-k
            matrix = [[gaussian_binomial(D+i, j) for j in range(k+1)]
                      for i in range(k+1)]
            for i, row in enumerate(matrix):
                for j, coefficient in enumerate(row):
                    # Group j-subspaces of F2^D + F2^i by projection dimension h.
                    factored = sum(gaussian_binomial(i, h)*gaussian_binomial(D, j-h)
                                   * 2**((D-j+h)*h) for h in range(max(0, j-D), j+1))
                    assert factored == coefficient
            rhs = [int(i == k) for i in range(k+1)]
            for p in (3, 5, 7, 11):
                weights = solve_mod_prime(matrix, rhs, p)
                assert [sum(a*b for a, b in zip(row, weights)) % p for row in matrix] == rhs
                solved += 1
    print(f"kernel subspaces on 512 matrices; odd-prime moment interpolation systems {solved}")


def fourier_coefficients(values):
    output = list(values)
    width = 1
    while width < len(output):
        for start in range(0, len(output), 2*width):
            for offset in range(width):
                lo = start+offset
                hi = lo+width
                x, y = output[lo], output[hi]
                output[lo], output[hi] = x+y, x-y
        width *= 2
    return output


def fourier_checks():
    d = 3
    domain = [rows_of(m, d) for m in range(1 << (d*d))]
    ranks = [binary_rank(rows) for rows in domain]
    checked = 0

    def check_support(values, t):
        nonlocal checked
        coefficients = fourier_coefficients(values)
        assert all(not c or r <= t for c, r in zip(coefficients, ranks))
        checked += 1
        return {r for c, r in zip(coefficients, ranks) if c}

    for query in (left_answer, right_answer):
        for direction in range(1, 1 << d):
            answers = [query(rows, direction) for rows in domain]
            for response in range(1 << d):
                check_support([int(a == response) for a in answers], 1)

    # Choose the second (column) direction from the reply to a first (row) query.
    for direction in range(1, 1 << d):
        leaf_predicate = []
        for rows in domain:
            answer = left_answer(rows, direction)
            second_direction = (answer % ((1 << d)-1)) + 1
            second_answer = right_answer(rows, second_direction)
            leaf_predicate.append(int(second_answer == answer))
        check_support(leaf_predicate, 2)

    # The j-query radial moment has a nonzero component of exact rank j.
    for j in range(d+1):
        assert check_support([2**(j*(d-r)) for r in ranks], j) == set(range(j+1))
    delta = [int(r == 0) for r in ranks]
    assert fourier_coefficients(delta) == [1] * len(domain)
    print(f"rank-bounded Fourier support checks {checked}, full-rank delta coefficients "
          f"{sum(r == d for r in ranks)}")


if __name__ == "__main__":
    exhaustive_residuals()
    cylinder_checks()
    vector_cylinder_parities()
    kernel_subspace_checks()
    fourier_checks()
