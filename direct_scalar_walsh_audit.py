"""Integer Walsh sums of the parity of AB paired entrywise with Z."""
from itertools import product
from math import prod


def gauss(n, k):
    if not 0 <= k <= n:
        return 0
    return prod(2**n - 2**i for i in range(k)) // prod(2**k - 2**i for i in range(k))


def full_frequency(d):
    outer = 0
    for r in range(1, d + 1):
        count = gauss(d - 1, r - 1)
        group = prod(2**r - 2**i for i in range(r))
        if d % 2:
            signed_maps = count**2 * (group // (2**r - 1))
        else:
            exceptional = gauss(d - 2, r - 1)
            generic_pairs = (count - exceptional)**2
            signed_maps = (count**2 - generic_pairs) * group - generic_pairs * (group // (2**r - 1))
        outer += 2**(d * (d - r)) * signed_maps
    return 2**(d * d) * outer


def parity(x):
    return x.bit_count() % 2


def dot_rows(rows, b):
    return sum(parity(row & b) << i for i, row in enumerate(rows))


def chosen_masks(d):
    u = 2**d - 1
    columns = [u ^ (1 << i) for i in range(d - 1)]
    last = 0
    for col in columns:
        last ^= col
    columns.append(last)
    wrows = [u ^ (1 << i) for i in range(d)]
    if d % 2:
        wrows[-1] ^= 1 << (d - 1)
    return columns, wrows


def sum_by_last_matrix(d):
    # No rank tests or Gauss sums. Group the first two input banks by their
    # common middle index and sum each pair of column/row vectors explicitly
    # after orthogonality on the first vector.
    q = 2**d
    u = q - 1
    columns, wrows = chosen_masks(d)
    signs = [(-1)**parity(b) for b in range(q)]
    full = dense = 0
    for rows in product(range(q), repeat=d):
        fibers = [0] * q
        for b in range(q):
            fibers[dot_rows(rows, b)] += signs[b]
        full += (-1)**sum(parity(v) for v in rows) * (q * fibers[u])**d
        dense += (-1)**sum(parity(v & w) for v, w in zip(rows, wrows)) * prod(q * fibers[col] for col in columns)
    return full, dense


def direct(d):
    q = 2**d
    banks = list(product(range(q), repeat=d))
    full = dense = 0
    columns, wrows = chosen_masks(d)
    for arows, brows in product(banks, repeat=2):
        abrows = []
        for row in arows:
            out = 0
            for k in range(d):
                if row & (1 << k):
                    out ^= brows[k]
            abrows.append(out)
        acols = [sum(((row >> j) & 1) << i for i, row in enumerate(arows)) for j in range(d)]
        for zrows in banks:
            g = sum(parity(v & z) for v, z in zip(abrows, zrows)) % 2
            full += (-1)**(g + sum(parity(v) for v in (*arows, *brows, *zrows)))
            dense += (-1)**(g + sum(parity(v & w) for v, w in zip(acols, columns)) +
                            sum(parity(v) for v in brows) + sum(parity(v & w) for v, w in zip(zrows, wrows)))
    return full, dense


def main():
    for d in range(1, 5):
        full, dense = sum_by_last_matrix(d)
        if d <= 2:
            assert (full, dense) == direct(d)
        assert full == full_frequency(d) > 0
        if d >= 2:
            assert dense == (-1)**(d-1) * 2**(d*d + d*(d-1)//2)
        print(f"d={d}, full-mask integer sum {full}, second mask {dense}")
    assert full_frequency(3) % 29 == 0
    for prime in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        order = next(e for e in range(1, prime) if pow(2, e, prime) == 1)
        d = 1 + 2 * order
        assert full_frequency(d) % prime != 0
    print("ten fixed odd fields checked at d = 1 + 2 ord_p(2)")


if __name__ == "__main__":
    main()
