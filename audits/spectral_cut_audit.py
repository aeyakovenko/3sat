"""Check the Walsh cut calculation and the partial-memory incidence spectrum."""
from itertools import combinations, product
from math import comb

import numpy as np


def sign(i):
    return 1 - 2 * (i.bit_count() % 2)


def walsh(size):
    return np.array([[sign(i & j) for j in range(size)] for i in range(size)],
                    dtype=np.int64)


def lift(table, left, right):
    """Order rows by (x,I) and columns by (y,J)."""
    return (table[:, None, :, None] * left.T[None, :, :, None]
            * right[:, None, None, :]).reshape(
                table.shape[0] * left.shape[1], table.shape[1] * right.shape[1])


def check_lifts():
    rng = np.random.default_rng(27)
    cases = 0
    for m in range(1, 5):
        L = 1 << m
        W = walsh(L)
        cube = np.arange(L)
        for r, p in product(range(min(2, m) + 1), repeat=2):
            Is = [i for i in range(L) if i.bit_count() <= r]
            Js = [i for i in range(L) if i.bit_count() <= p]
            left, right = W[:, Is], W[:, Js]
            assert np.array_equal(left.T @ left, L * np.eye(len(Is), dtype=int))
            assert np.array_equal(right.T @ right, L * np.eye(len(Js), dtype=int))
            f = rng.choice([-1, 1], size=(L, L))
            K = lift(f, left, right)
            a = rng.integers(-2, 3, (L, len(Is)))
            b = rng.integers(-2, 3, (L, len(Js)))
            A, B = a @ left.T, right @ b.T
            assert int(np.sum(f * A * B)) == int(a.ravel() @ K @ b.ravel())
            # At an inner-product sign table the row/column relabeling factors the lift.
            K = lift(W, left, right)
            idx_row = [(x ^ I) * len(Is) + i for x in cube.tolist() for i, I in enumerate(Is)]
            idx_col = [(y ^ J) * len(Js) + j for y in cube.tolist() for j, J in enumerate(Js)]
            assert np.array_equal(K[np.ix_(idx_row, idx_col)], np.kron(W, W[np.ix_(Is, Js)]))
            cases += 1
    return cases


def mul16(x, y):
    z = 0
    while y:
        if y & 1:
            z ^= x
        x <<= 1
        if x & 16:
            x ^= 0b10011
        y >>= 1
    return z


def polynomial_tables():
    # All low-bit projections of degree-<4 polynomials on GF(16).
    pool = {0}
    powers = [1] * 16
    for _ in range(4):
        for bit in (1, 2, 4, 8):
            column = sum((mul16(bit, val) & 1) << i for i, val in enumerate(powers))
            pool |= {s ^ column for s in pool}
        powers = [mul16(z, i) for i, z in enumerate(powers)]
    return sorted(pool)


def trace_and_subcube_moments(tables):
    indices = np.arange(16)
    chars = walsh(4)[:, :3]
    twist = np.array([sign((i*i + 3*i) & 39) for i in range(16)])
    total_trace = 0
    total_fourth = 0
    for offset in range(0, len(tables), 256):
        batch = np.array(tables[offset:offset + 256])[:, None]
        signs = (1 - 2 * ((batch >> indices) & 1)) * twist
        lifted = (signs.reshape(-1, 4, 1, 4, 1) * chars.T[None, None, :, :, None]
                  * chars[None, :, None, None, :]).reshape(-1, 12, 12)
        gram = lifted @ lifted.transpose(0, 2, 1)
        total_trace += int((gram * gram).sum())
        total_fourth += int((signs[:, :8].sum(axis=1)**4).sum())
    return total_trace, total_fourth


def check_independence():
    projected = polynomial_tables()
    size = len(projected)
    for positions in combinations(range(16), 4):
        mask = sum(1 << i for i in positions)
        assert sum(sign(t & mask) for t in projected) == 0
    small = trace_and_subcube_moments(projected)
    full = trace_and_subcube_moments(range(1 << 16))
    for x, y in zip(small, full):
        assert x * (1 << 16) == y * size
    return size


def check_partial_memory():
    tensors = 0
    for v in (2, 3, 4):
        for U in range(1, 5 if v == 2 else 4):
            C = list(product(range(v), repeat=U))
            for q in range(U + 1):
                proposals = [(Q, b) for Q in combinations(range(U), q)
                             for b in product(range(v), repeat=q)]
                M = np.array([[int(tuple(c[i] for i in Q) == b) for Q, b in proposals]
                              for c in C], dtype=np.int64)
                gram = M @ M.T
                # For each nonconstant label use the zero-mean vector e_j - e_0.
                for label in product(range(v), repeat=U):
                    i = sum(t != 0 for t in label)
                    row = np.array([np.prod([int(c[h] == b) - int(c[h] == 0)
                                             for h, b in enumerate(label) if b],
                                            dtype=np.int64) for c in C])
                    expected = len(C) * len(proposals) * (comb(q, i) if i <= q else 0)
                    assert np.array_equal((v**(2*q) * comb(U, i)) * (gram @ row),
                                          expected * row)
                    tensors += 1
    return tensors


def check_adaptive_oracle():
    # The native oracle words are two bits. The next input pin depends on the first
    # word, and the next word address depends on that pin. Check the two degrees separately.
    W = walsh(8)
    Z = walsh(64)
    count = 0
    for y in range(8):
        values = np.empty((8, 64), dtype=np.int64)
        for x, c in product(range(8), range(64)):
            first = (c >> (2 * (y % 3))) & 3
            bit = (x >> ((first + y) % 3)) & 1
            second = (c >> (2 * ((first + bit) % 3))) & 3
            values[x, c] = sign((first + second + bit) & 3)
        joint = W @ values @ Z
        for i, j in product(range(8), range(64)):
            address_support = sum(((j >> shift) & 3) != 0 for shift in (0, 2, 4))
            if i.bit_count() > 1 or address_support > 2:
                assert joint[i, j] == 0
            count += 1
    return count


if __name__ == '__main__':
    print(f'{check_lifts()} exact bilinear lifts and tensor relabelings')
    print(f'{check_independence()} polynomial sign tables match the fourth moments of all 65,536 tables')
    print(f'{check_partial_memory()} partial-memory incidence eigenvectors')
    print(f'{check_adaptive_oracle()} adaptive query Fourier coefficients')
