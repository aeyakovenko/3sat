"""Check mixed differences and the one-division construction on small inputs."""

from itertools import permutations, product
from math import comb, factorial, prod
from random import Random


def simplex(dim, budget):
    if dim == 0:
        yield ()
        return
    for head in range(budget + 1):
        for tail in simplex(dim - 1, budget - head):
            yield (head,) + tail


def eval_poly(poly, x):
    return sum(c * prod(v ** j for v, j in zip(x, e)) for e, c in poly.items())


def check_jets():
    rng = Random(853)
    polynomials = [
        {tuple(rng.randrange(7) for _ in range(3)): rng.randrange(-11, 12)
         for _ in range(35)} for _ in range(4)
    ]
    count = 0
    for poly in polynomials:
        for a in simplex(3, 6):
            degree = sum(a)
            q = 2 ** degree * prod(factorial(j) for j in a)
            value = 0
            for b in product(*(range(j + 1) for j in a)):
                signed = (-1) ** (degree - sum(b)) * prod(comb(j, k) for j, k in zip(a, b))
                value += signed * eval_poly(poly, [2 * v for v in b])
            assert value % q == 0 and (value // q - poly.get(a, 0)) % 2 == 0
            count += 1
    return count


def determinant(a):
    return sum((-1) ** sum(p[i] > p[j] for j in range(len(p)) for i in range(j)) *
               prod(row[col] for row, col in zip(a, p)) for p in permutations(range(len(a))))


def check_division(m):
    count = 0
    for b in simplex(m * m, m):
        x = [[2 * b[i*m + j] for j in range(m)] for i in range(m)]
        # The directed out-Laplacian cofactor, with the last row/column deleted.
        minor = [[sum(x[i]) - x[i][i] if i == j else -x[i][j]
                  for j in range(m - 1)] for i in range(m - 1)]
        numerator = prod(map(sum, x)) * prod(map(sum, zip(*x))) * determinant(minor)
        cycles = ((0,) + rest for rest in permutations(range(1, m)))
        hc = sum(prod(x[c[i-1]][c[i]] for i in range(m)) for c in cycles)
        assert numerator == hc * 2 ** (2*m - 1)
        count += 1
    return count


if __name__ == '__main__':
    print(f'{check_jets()} normalized coefficient parities correct')
    print(f'{sum(check_division(m) for m in (2, 3))} sparse hosts correct after exact division')
