"""Check the Toeplitz hash and subspace covering identities on small cubes."""

from itertools import combinations


def toeplitz(x, diagonals, width, rows):
    out = 0
    for r in range(rows):
        word = 0
        for c in range(width):
            word ^= (x >> c & 1) & (diagonals >> (width - 1 + r - c) & 1)
        out |= word << r
    return out


def check_hashes():
    pairs = 0
    for width in range(1, 5):
        for rows in range(1, width + 1):
            d = width + rows - 1
            for x, y in combinations(range(1 << width), 2):
                # An independent offset turns a uniform difference into a uniform pair.
                hist = [0] * (1 << rows)
                for diag in range(1 << d):
                    hist[toeplitz(x ^ y, diag, width, rows)] += 1
                assert set(hist) == {1 << (d - rows)}
                pairs += 1
    return pairs


def check_covers():
    tested = 0
    for dim in range(1, 4):
        size = 1 << dim
        cube = set(range(size))
        shifts = dim.bit_length()  # ceil(log2(dim + 1))
        for code in range(1 << size):
            accepted = {s for s in cube if code >> s & 1}
            if 2 * len(accepted) < size:
                continue
            missing = cube - accepted
            for _ in range(shifts):
                choices = [missing & {v ^ t for v in missing} for t in cube]
                next_missing = min(choices, key=len)
                assert len(next_missing) * size <= len(missing) ** 2
                missing = next_missing
            assert not missing
            tested += 1
    return tested


if __name__ == '__main__':
    print(f'{check_hashes()} hash input-pair cases; {check_covers()} dense cube subsets')
