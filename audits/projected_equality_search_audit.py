"""Exhaust affine and projective subspace decision trees on small prime fields."""

from functools import cache
from itertools import product


def query_family(points, prime, projective):
    """Generate every nonconstant affine/projective flat by hyperplane intersections."""
    dimension = len(points[0])
    full = (1 << len(points)) - 1
    family = {full}
    right_sides = [0] if projective else range(prime)
    for normal in product(range(prime), repeat=dimension):
        if not any(normal):
            continue
        # Use only one representative of each nonzero normal up to scale.
        if next(value for value in normal if value) != 1:
            continue
        values = [sum(a * b for a, b in zip(normal, point)) % prime for point in points]
        for rhs in right_sides:
            hyperplane = sum(1 << i for i, value in enumerate(values) if value == rhs)
            family.update({flat & hyperplane for flat in family})
    return sorted(family - {0, full}), full


def optimal_success_profile(points, prime):
    flats, full = query_family(points, prime, projective=False)

    @cache
    def successes(mask, negative_budget):
        if negative_budget < 0:
            return 0
        size = mask.bit_count()
        if size <= 1 or negative_budget >= size - 1:
            return size
        best = 1  # Guess a single point and halt.
        for flat in flats:
            inside = mask & flat
            if inside == 0 or inside == mask:
                continue
            total = successes(inside, negative_budget) + successes(mask ^ inside, negative_budget - 1)
            best = max(best, total)
            if best == size:
                break
        return best

    degree = len(points[0]) * (prime - 1)
    profile = [successes(full, h) for h in range(degree + 1)]
    predicted = [sum(sum(exponent) <= h for exponent in points) for h in range(degree + 1)]
    assert profile == predicted, (prime, profile, predicted)
    return profile


def minimax_depth(flats, full):
    @cache
    def depth(mask):
        if mask.bit_count() <= 1:
            return 0
        best = mask.bit_count() - 1
        lower = (mask.bit_count() - 1).bit_length()
        for flat in flats:
            inside = mask & flat
            if inside == 0 or inside == mask:
                continue
            best = min(best, 1 + max(depth(inside), depth(mask ^ inside)))
            if best == lower:
                break
        return best

    return depth(full)


def optimal_projective_depth(dimension, prime):
    points = [
        point
        for point in product(range(prime), repeat=dimension)
        if any(point) and next(value for value in point if value) == 1
    ]
    flats, full = query_family(points, prime, projective=True)
    result = minimax_depth(flats, full)
    assert result == (dimension - 1) * (prime - 1) + 1
    return len(points), result


def small_binary_product_projections():
    # For d=2 there are three one-dimensional row spaces and one full row
    # space. Another basis in the same space just renames query outcomes.
    bases = {1: [(1,), (2,), (3,)], 2: [(1, 2)]}
    matrices = list(product(range(4), repeat=2))  # matrix given by its two columns
    depths = {}
    for left_rank, right_rank in product([1, 2], repeat=2):
        queries = set()
        for left in bases[left_rank]:
            for right in bases[right_rank]:
                same_answer = {}
                for i, (first, second) in enumerate(matrices):
                    right_product = [(first if v & 1 else 0) ^ (second if v & 2 else 0) for v in right]
                    answer = tuple((u & col).bit_count() % 2 for u in left for col in right_product)
                    same_answer[answer] = same_answer.get(answer, 0) | (1 << i)
                queries.update(same_answer.values())
        depths[left_rank, right_rank] = minimax_depth(sorted(queries), (1 << len(matrices)) - 1)
    assert depths == {(1, 1): 4, (1, 2): 6, (2, 1): 6, (2, 2): 15}
    return depths


if __name__ == "__main__":
    for dimension, prime in [(3, 2), (2, 3), (1, 5)]:
        grid = list(product(range(prime), repeat=dimension))
        print(f"Affine F_{prime}^{dimension}, optimal success counts {optimal_success_profile(grid, prime)}")
    for dimension, prime in [(3, 2), (4, 2), (3, 3)]:
        points, depth = optimal_projective_depth(dimension, prime)
        print(f"PG({dimension - 1},{prime}), {points} points, optimal worst-case depth {depth}")
    print(f"Binary 2x2 matrices, optimal depths by projection ranks {small_binary_product_projections()}")
