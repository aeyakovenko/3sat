"""Check projected DNF scores, certificate lengths, and the pinned XOR optional row."""

from fractions import Fraction
from itertools import combinations


def subcubes(dimension):
    cube_size = 1 << dimension
    cubes = []
    for width in range(dimension + 1):
        for coordinates in combinations(range(dimension), width):
            mask = sum(1 << i for i in coordinates)
            for value in range(cube_size):
                if value & ~mask == 0:
                    points = sum(1 << x for x in range(cube_size) if x & mask == value)
                    cubes.append((width, points))
    return cubes


def check_projected_scores():
    checked = 0
    results = []
    for dimension in range(1, 5):
        n = 1 << dimension
        even = sum(1 << x for x in range(n) if x.bit_count() % 2 == 0)
        cubes = subcubes(dimension)
        for width in range(1, dimension + 1):
            family = {0}
            for size, points in cubes:
                if size == width:
                    family.update({mask | points for mask in family})
            optimum = Fraction(0)
            optimal_mask = None
            for mask in family - {0}:
                lengths = {}
                for size, points in cubes:  # Nondecreasing certificate length.
                    if points & ~mask == 0:
                        for x in range(n):
                            if points & (1 << x):
                                lengths.setdefault(x, size)
                assert max(lengths.values()) <= width
                for correct in (mask & even, mask & ~even):
                    good = correct.bit_count()
                    errors = mask.bit_count() - good
                    cost = sum(c for x, c in lengths.items() if correct & (1 << x))
                    assert dimension * good - cost <= dimension * errors
                signed = abs(2 * (mask & even).bit_count() - mask.bit_count())
                ratio = Fraction(signed, mask.bit_count())
                if optimal_mask is None or ratio > optimum:
                    optimum, optimal_mask = ratio, mask
                checked += 1

            # Test the lower direction of the variational principle on each input.
            majority = int(2 * (optimal_mask & even).bit_count() < optimal_mask.bit_count())
            for x in range(n):
                kept = [s for s in range(n) if optimal_mask & (1 << (x ^ s))]
                wins = sum((majority ^ (s.bit_count() % 2)) == x.bit_count() % 2 for s in kept)
                assert Fraction(wins, len(kept)) == (1 + optimum) / 2
            if width == 1:
                assert optimum == Fraction(1, n - 1)
            if width == dimension - 1:
                assert optimum == Fraction(dimension - 1, dimension + 1)
            results.append((dimension, width, str(optimum)))
    return checked, results


def parity_formula(dimension, pins):
    def unit(literal):
        return (literal, literal, literal)

    clauses = [unit(i + 1 if pins & (1 << i) else -i - 1) for i in range(dimension)]
    a = 1
    for b in range(2, dimension + 1):
        z = dimension + b - 1
        clauses.extend(((a, b, -z), (a, -b, z), (-a, b, z), (-a, -b, -z)))
        a = z
    clauses.append(unit(a))
    return clauses


def check_formulas():
    cases = 0
    for dimension in range(1, 7):
        for pins in range(1 << dimension):
            formula = parity_formula(dimension, pins)
            for i in range(dimension):
                changed = parity_formula(dimension, pins ^ (1 << i))
                assert [j for j in range(len(formula)) if formula[j] != changed[j]] == [i]
            solutions = 0
            for assignment in range(1 << (2 * dimension - 1)):
                solutions += all(any(bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0)
                                     for lit in clause) for clause in formula)
            assert solutions == pins.bit_count() % 2
            cases += 1
    return cases


if __name__ == '__main__':
    count, optima = check_projected_scores()
    print(f'{count} nonempty width-bounded DNF sets checked with both possible colors.')
    print('Maximum absolute signed-to-total mass (dimension, width, ratio):', optima)
    print(f'{check_formulas()} explicit pinned 3-CNFs, including every one-pin neighbor.')
