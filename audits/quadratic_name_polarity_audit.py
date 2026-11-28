"""Finite checks for quadratic-name SAT reductions. Uses only the standard library."""
from itertools import combinations, combinations_with_replacement, permutations, product
from math import ceil, isqrt


def add_sparse(basis, row, prime):
    """Insert a sparse polynomial or vector, using its smallest index as pivot."""
    row = {key: value % prime for key, value in row.items() if value % prime}
    while row:
        pivot = min(row)
        if pivot not in basis:
            inv = pow(row[pivot], -1, prime)
            basis[pivot] = {key: value * inv % prime for key, value in row.items()}
            return True
        scale = row[pivot]
        for key, value in basis[pivot].items():
            residue = (row.get(key, 0) - scale * value) % prime
            if residue:
                row[key] = residue
            else:
                row.pop(key, None)
    return False


def graph_kernel(d, prime):
    m = d * d
    # Lists of monomials that a single formal variable becomes after C = AB.
    images = [[(i,)] for i in range(2 * m)]
    for i, j in product(range(d), repeat=2):
        images.append([(i * d + k, m + k * d + j) for k in range(d)])
    basis = {}
    columns = 0
    for degree in range(3):
        for indices in combinations_with_replacement(range(3 * m), degree):
            row = {}
            for parts in product(*(images[i] for i in indices)):
                key = tuple(sorted(x for term in parts for x in term))
                row[key] = row.get(key, 0) + 1
            add_sparse(basis, row, prime)
            columns += 1
    assert columns - len(basis) == m


def row_spaces(width, dimension, prime):
    """Exactly one reduced row-echelon basis for each subspace."""
    for pivots in combinations(range(width), dimension):
        free = [(i, j) for i, start in enumerate(pivots)
                for j in range(start + 1, width) if j not in pivots]
        for values in product(range(prime), repeat=len(free)):
            rows = [[int(j == start) for j in range(width)] for start in pivots]
            for (i, j), val in zip(free, values):
                rows[i][j] = val
            yield pivots, rows


def exact_rank(rows, prime):
    basis = {}
    for row in rows:
        add_sparse(basis, dict(enumerate(row)), prime)
    return len(basis)


def rotated_spans():
    # Cover each possible pivot shape in a 2-by-2 array with its row/col
    # permutations, then test exact base-field specializations for every subspace.
    p = 3
    perms = [tuple(2 * a[i] + b[j] for i, j in product(range(2), repeat=2))
             for a, b in product(permutations(range(2)), repeat=2)]
    spaces = 0
    for dim in range(1, 5):
        for pivots, rows in row_spaces(4, dim, p):
            choices = {}
            cover = []
            remaining = set(range(4))
            while remaining:
                perm = max(perms, key=lambda g: len(remaining.intersection(g[i] for i in pivots)))
                selected = [j for j, i in enumerate(pivots) if perm[i] in remaining]
                assert selected
                for j in selected:
                    remaining.remove(perm[pivots[j]])
                cover.append((perm, selected))
            for a, b in cover:
                options = []
                for r1, c1 in product(range(1, p), repeat=2):
                    scale = (1, c1, r1, r1 * c1)
                    outputs = []
                    for idx in b:
                        candidate = [0] * 4
                        for j, val in enumerate(rows[idx]):
                            candidate[a[j]] = val * scale[j] % p
                        outputs.append(candidate)
                    options.append(outputs)
                choices[len(choices)] = options
            assert any(exact_rank([row for block in candidate for row in block], p) == 4
                       for candidate in product(*choices.values()))
            spaces += 1
    assert spaces == 211  # 40 lines, 130 planes, 40 hyperplanes, full space
    return spaces


def check_pin_construction():
    cases = 0
    for p in (2, 3, 5, 7, 11, 17, 31):
        for m in (1, 2, 3):
            quotient = ceil(p / m)
            h = min(p - 1, isqrt(quotient - 1) + 1)
            low = set(range(h))
            high = set(range(h, p, h)) | {p - 1}
            assert not low & high
            assert {l - a for l in high for a in low if 1 <= l - a < p} == set(range(1, p))
            for residual in product(range(p), repeat=m):
                negative = {(x + a) % p for x in residual for a in low}
                assert high.isdisjoint(negative) == (not any(residual))
                cases += 1
    return cases


def quadratic_isolation():
    for p in (3, 5, 7, 11):
        squares = {z * z % p for z in range(p)}
        nonresidue = next(z for z in range(1, p) if z not in squares)
        roots = [(x, y) for x, y in product(range(p), repeat=2)
                 if (x * x - nonresidue * y * y) % p == 0]
        assert roots == [(0, 0)]  # the local dimension bound 2E is tight


def main():
    for d, p in product((1, 2, 3), (2, 3, 5, 7)):
        graph_kernel(d, p)
    spaces = rotated_spans()
    pins = check_pin_construction()
    quadratic_isolation()
    print(f"12 formal graph kernels, {spaces} exact F3 output spaces, "
          f"{pins} prime-field pin patterns, 4 sharp quadratic point isolations")


if __name__ == "__main__":
    main()
