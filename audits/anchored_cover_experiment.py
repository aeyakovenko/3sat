"""Check two-sided rank factorizations and certify the numerical entropy margins."""

from fractions import Fraction as F
from itertools import product
from random import Random


def codewords(basis):
    words = [0]
    for vector in basis:
        words += [word ^ vector for word in words]
    return words


def nearest(words, target):
    return min(range(len(words)), key=lambda index: (target ^ words[index]).bit_count())


def two_arms(rows, width, stages, dyadic):
    """Use the same local codes with either immediate or dyadic updates."""
    residual = rows.copy()
    left = [0] * len(rows)
    right = [0] * width
    row_cuts, col_cuts, rank_cuts = [0], [0], [0]
    for a, b, vertical, horizontal in stages:
        assert len(vertical) == len(horizontal)
        row_cuts.append(row_cuts[-1] + a)
        col_cuts.append(col_cuts[-1] + b)
        rank_cuts.append(rank_cuts[-1] + len(vertical))
    assert row_cuts[-1] == len(rows) and col_cuts[-1] <= width
    error_bound = 0

    def decode(stage):
        nonlocal error_bound
        a, b, vertical, horizontal = stages[stage]
        start_i, end_i = row_cuts[stage:stage + 2]
        start_j, end_j = col_cuts[stage:stage + 2]
        rank_offset = rank_cuts[stage]
        up, across = codewords(vertical), codewords(horizontal)
        for i in range(start_i, end_i):
            bits = sum(((word >> (i - start_i)) & 1) << j for j, word in enumerate(vertical))
            left[i] |= bits << rank_offset
        for j in range(start_j, end_j):
            bits = sum(((word >> (j - start_j)) & 1) << i for i, word in enumerate(horizontal))
            right[j] |= bits << rank_offset
        for j in range(end_j, width):
            target = sum(((residual[i] >> j) & 1) << (i - start_i) for i in range(start_i, end_i))
            right[j] |= nearest(up, target) << rank_offset
        for i in range(end_i, len(rows)):
            target = (residual[i] >> start_j) & ((1 << b) - 1)
            left[i] |= nearest(across, target) << rank_offset
        rv = max((x ^ up[nearest(up, x)]).bit_count() for x in range(1 << a))
        rh = max((x ^ across[nearest(across, x)]).bit_count() for x in range(1 << b))
        error_bound += a * b + rv * (width - end_j) + rh * (len(rows) - end_i)

    def update(row_range, column_range, first_stage, stop_stage):
        mask = (1 << rank_cuts[stop_stage]) - (1 << rank_cuts[first_stage])
        for i in row_range:
            for j in column_range:
                residual[i] ^= ((left[i] & right[j] & mask).bit_count() % 2) << j

    def process(first, stop):
        if stop == first + 1:
            decode(first)
            return
        middle = (first + stop) // 2
        process(first, middle)
        update(range(row_cuts[middle], row_cuts[stop]), range(col_cuts[middle], width), first, middle)
        update(range(row_cuts[stop], len(rows)), range(col_cuts[middle], col_cuts[stop]), first, middle)
        process(middle, stop)

    if dyadic:
        process(0, len(stages))
    else:
        for stage in range(len(stages)):
            decode(stage)
            update(range(row_cuts[stage + 1], len(rows)), range(col_cuts[stage + 1], width), stage, stage + 1)
    errors = 0
    for i, target in enumerate(rows):
        decoded = sum(((left[i] & v).bit_count() % 2) << j for j, v in enumerate(right))
        errors += (decoded ^ target).bit_count()
    assert errors <= error_bound
    return left, right


def compare_schedules(rows, width, stages):
    assert two_arms(rows, width, stages, True) == two_arms(rows, width, stages, False)


def log_bounds_normalized(x):
    """Bounds for ln x, 1 <= x <= 2, from the atanh series."""
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    power = z
    lower = F(0)
    for i in range(16):
        lower += 2 * power / (2 * i + 1)
        power *= z * z
    return lower, lower + 2 * power / (33 * (1 - z * z))


def log2_bounds(x):
    assert x >= 1
    n = 0
    while x > 2:
        x /= 2
        n += 1
    lower, upper = log_bounds_normalized(x)
    lower_ln2, upper_ln2 = log_bounds_normalized(F(2))
    return n + lower / upper_ln2, n + upper / lower_ln2


def entropy_bounds(distortion):
    first = log2_bounds(1 / distortion)
    second = log2_bounds(1 / (1 - distortion))
    return tuple(distortion * x + (1 - distortion) * y for x, y in zip(first, second))


def covering_margin(rate, distortion):
    assert rate + entropy_bounds(distortion)[0] > 1


def verify_constants():
    budget = F(1, 16)
    remaining_rows = F('0.2816')
    remaining_columns = F(1)
    phases = [
        (F('0.1408'), F('0.0525'), F('0.0343'), F('0.21795'), F('0.06492')),
        (F('0.1408'), F('0.04525'), F('0.0282'), F('0.24284'), F('0.07294')),
    ]
    constructive_error = 0
    assert sum(p[2] for p in phases) == budget
    for height, width, rank, vertical, horizontal in phases:
        covering_margin(rank / height, vertical)
        covering_margin(rank / width, horizontal)
        constructive_error += height * (remaining_columns - width / 2) * vertical
        constructive_error += width * (remaining_rows - height / 2) * horizontal
        remaining_rows -= height
        remaining_columns -= width
    assert remaining_rows == 0 and constructive_error < budget
    height, width = F('0.2881'), F('0.0947')
    vertical, horizontal = F('0.23292'), F('0.06321')
    covering_margin(budget / height, vertical)
    covering_margin(budget / width, horizontal)
    anchored_error = height * (width * horizontal + (1 - width) * vertical)
    assert anchored_error < budget
    height, late_rate, slab_ratio = F('0.2883'), F('0.032'), F('1.516')
    horizontal, vertical, triple = F('0.0634'), F('0.2331'), F('0.4122')
    rate = budget / height
    early_rate = rate - late_rate
    early_width = slab_ratio * (budget - height * late_rate)
    coverage = early_width + 3 * height * late_rate
    assert early_rate > 0 and coverage <= 1
    assert entropy_bounds(horizontal)[0] + 1 / slab_ratio - 1 > F('0.000426')
    lower, upper = entropy_bounds(vertical)
    assert lower + rate - 1 > F('0.000164') and 1 - early_rate - upper > F('0.03183')
    assert entropy_bounds(triple)[0] + triple * log2_bounds(F(3))[0] - 2 * (1 - early_rate) > F('0.000538')
    triple_error = height * (early_width * horizontal + height * late_rate * triple + (1 - coverage) * vertical)
    assert triple_error == F(1952743120382103, 31250000000000000) < budget
    print(f"Certified normalized errors: two-sided={float(constructive_error):.12f}, "
          f"anchored={float(anchored_error):.12f}, triples={float(triple_error):.12f}")


def main():
    small_stages = [(2, 1, (3,), (1,)), (1, 1, (1,), (1,))]
    for rows in product(range(16), repeat=3):
        compare_schedules(list(rows), 4, small_stages)
    rng = Random(11)
    stages = [(3, 3, (7,), (7,)), (3, 4, (3, 6), (3, 12)), (4, 3, (5, 10), (3, 5))]
    for _ in range(200):
        compare_schedules([rng.getrandbits(15) for _ in range(10)], 15, stages)
    print("Verified factors and error bounds on all 4,096 small matrices and 200 larger cases.")
    verify_constants()


if __name__ == "__main__":
    main()
