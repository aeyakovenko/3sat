"""Enumerate the nine absolute-color boundary states of arbitrary short tip tiles."""

from itertools import pairwise, permutations, product

U = (1, 2, 0, 5, 3, 6, 4)
A = (1, 2, 0, 4, 5, 3)
B = (1, 5, 3, 4, 2, 0)
STATES = tuple(product(range(3), repeat=2))


def matrix(order):
    m = [[0] * 9 for _ in STATES]
    for y in product(range(3), repeat=len(order) + 1):
        if y[0] or any(a == b for a, b in pairwise(y)):
            continue
        z = [3 - a - b for a, b in pairwise(y)]
        if any(z[i] == z[j] for i, j in pairwise(order)):
            continue
        start, last = z[order[0]], z[order[-1]]
        for base in range(3):
            for previous in range(3):
                if previous != (start + base) % 3:
                    a = 3 * previous + base
                    b = 3 * ((last + base) % 3) + (y[-1] + base) % 3
                    m[a][b] += 1
    return m


def product_matrix(a, b):
    return [[sum(x * y for x, y in zip(r, c)) for c in zip(*b)] for r in a]


def audit():
    total = 0
    for k in range(1, 7):
        for q in permutations(range(k)):
            m = matrix(q)
            total += 1
            assert not (any(m[0]) and all(row == m[0] for row in m))
    u = matrix(U)
    assert u == [[2 * int(p != y) for p, y in STATES] for _ in STATES]
    tiles = [matrix(A), matrix(B)]
    I = [[int(i == j) for j in range(9)] for i in range(9)]
    codes = 0
    for length in range(6):
        for bits in product(range(2), repeat=length):
            k = I
            x = 1
            for bit in reversed(bits):
                k = product_matrix(tiles[bit], k)
                x = (1 + bit) * x + 1
            count = 24 * 4**length * x
            assert product_matrix(product_matrix(u, k), u) == [
                [count * int(p != y) for p, y in STATES] for _ in STATES
            ]
            codes += 1
    print(
        f"{total} orders through six tips have no nonzero equal-row absolute transfer; the seven-tip reset matches all 81 entries."
    )
    print(
        f"All 81 entries of each of {codes} sandwich codes match 24*4^length*X on different-color outputs."
    )


if __name__ == "__main__":
    audit()
