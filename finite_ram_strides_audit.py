"""Check the quotient-lattice memory coordinates with exact integer arithmetic (SymPy)."""

from itertools import product
from math import ceil
from random import Random

from sympy import Matrix
from sympy.polys.matrices import DomainMatrix


def check_group(modulus, strides):
    rank = len(strides)
    assert strides[0] == 1
    generators = Matrix.eye(rank)
    generators[0, 0] = modulus
    for j in range(1, rank):
        generators[0, j] = -strides[j]
    # SymPy reduces row lattices; the construction uses columns.
    basis = DomainMatrix.from_Matrix(generators.T).lll().to_Matrix().T
    assert abs(basis.det()) == modulus
    assert all(c % modulus == 0 for c in Matrix([strides]) * basis)
    inverse = basis.inv()
    denominators = [4 * rank * int(sum(map(abs, col))) for col in (basis.col(i) for i in range(rank))]
    dual_first = [int(x * modulus) for x in inverse[:, 0]]

    def physical(address):
        bins = [(num * address % modulus) * q // modulus
                for num, q in zip(dual_first, denominators)]
        folded = tuple(min(t, q-t) for t, q in zip(bins, denominators))
        signs = tuple(2*t > q for t, q in zip(bins, denominators))
        return folded, signs

    encoded = [physical(y) for y in range(modulus)]
    assert len(set(encoded)) == modulus
    checks = 0
    for j, stride in enumerate(strides):
        limits = [ceil(abs(q * inverse[i, j])) + 1 for i, q in enumerate(denominators)]
        for y, (origin, _) in enumerate(encoded):
            for orientation, sign in product((-1, 1), repeat=2):
                destination, _ = encoded[(orientation*y + sign*stride) % modulus]
                assert all(abs(a-b) <= limit for a, b, limit in zip(origin, destination, limits))
                checks += 1
    return checks


def main():
    groups = updates = 0
    rng = Random(1802)
    for width in range(2, 8):
        modulus = 1 << width
        palettes = [(1,), (1, 0, 0), (1, 1, 1), (1, modulus-1, modulus//2)]
        palettes.extend((1, step) for step in range(modulus))
        for rank in (3, 4, 5):
            for _ in range(4):
                palettes.append((1,) + tuple(rng.randrange(modulus) for _ in range(rank-1)))
        for strides in palettes:
            updates += check_group(modulus, strides)
            groups += 1
    print(f"{groups} stride lists checked for injectivity; {updates} signed translations checked")


if __name__ == "__main__":
    main()
