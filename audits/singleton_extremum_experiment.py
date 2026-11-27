"""Compare the designated-singleton formula with the full joint-law LP.

Run with Python 3, NumPy and SciPy. Each variable in the LP is the weight
of one bucket. All individual and pair probabilities are constrained directly.
"""

from fractions import Fraction
from itertools import combinations
from math import floor

import numpy as np
from scipy.optimize import linprog


def designated_singleton_maximum(competitors, marginal):
    if competitors == 1:
        return marginal * (1 - marginal)
    mean = competitors * marginal
    variance = mean * (1 - marginal)
    fraction = mean - floor(mean)
    min_variance = fraction * (1 - fraction)
    conditional_variance = min(
        mean * (competitors - mean),
        (variance - (1 - marginal) * min_variance) / marginal,
    )
    second_moment = mean**2 + conditional_variance
    lower_count = min(competitors - 1, floor(second_moment / mean))
    upper_count = lower_count + 1
    chance_lower = (upper_count * mean - second_moment) / lower_count
    chance_upper = (second_moment - lower_count * mean) / upper_count
    chance_zero = 1 - chance_lower - chance_upper
    assert min(chance_lower, chance_upper, chance_zero) >= 0
    assert lower_count * chance_lower + upper_count * chance_upper == mean
    assert lower_count**2 * chance_lower + upper_count**2 * chance_upper == second_moment
    return marginal * chance_zero


def compare_joint_laws():
    marginals = sorted({Fraction(i, d) for d in range(2, 10) for i in range(1, d)})
    tests = 0
    for competitors in range(1, 9):
        items = competitors + 1
        buckets = np.arange(2**items)
        membership = [(buckets >> i) & 1 for i in range(items)]
        pairs = [a * b for a, b in combinations(membership, 2)]
        constraints = np.array([np.ones_like(buckets), *membership, *pairs])
        objective = -(buckets == 1).astype(float)
        for marginal in marginals:
            rhs = [1] + [float(marginal)] * items + [float(marginal**2)] * len(pairs)
            result = linprog(objective, A_eq=constraints, b_eq=rhs, method="highs")
            exact = designated_singleton_maximum(competitors, marginal)
            assert result.success, result.message
            assert abs(-result.fun - float(exact)) < 2e-8, (competitors, marginal, exact)
            tests += 1
    print(f"All {tests} full joint-law optima agree with the formula.")


def compare_affine_buckets():
    checked = 0
    for dimension in range(1, 5):
        universe = 2**dimension
        full = (1 << universe) - 1
        subspaces = {frozenset([0])}
        for rank in range(dimension + 1):
            cosets = {
                sum(1 << (x ^ shift) for x in space)
                for space in subspaces
                for shift in range(universe)
            }
            for easy_count in range(min(4, universe - 1) + 1):
                bound = max(Fraction(1, universe), Fraction(easy_count * (easy_count + 1),
                                                           universe * (universe - 1)))
                for easy in combinations(range(universe), easy_count):
                    hard = full ^ sum(1 << x for x in easy)
                    counts = [0] * universe
                    for bucket in cosets:
                        intersection = bucket & hard
                        if intersection.bit_count() == 1:
                            counts[intersection.bit_length() - 1] += 1
                    assert Fraction(max(counts), len(cosets)) <= bound
                    checked += 1
            if rank < dimension:
                subspaces = {
                    space.union(x ^ direction for x in space)
                    for space in subspaces
                    for direction in range(universe) if direction not in space
                }
    print(f"The symmetric bound holds in {checked} affine size and easy-set cases.")


if __name__ == "__main__":
    compare_joint_laws()
    compare_affine_buckets()
