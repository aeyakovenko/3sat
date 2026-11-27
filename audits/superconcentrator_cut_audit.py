"""Small binary-field networks and monochromatic rectangles after restrictions."""

from itertools import combinations, product
from random import Random


class Field:
    def __init__(self, modulus):
        self.size = 1 << (modulus.bit_length() - 1)
        self.bits = self.size.bit_length() - 1
        self.table = []
        for a in range(self.size):
            row = []
            for b in range(self.size):
                v, y, p = a, b, 0
                while y:
                    if y & 1:
                        p ^= v
                    y >>= 1
                    v <<= 1
                    if v & self.size:
                        v ^= modulus
                row.append(p)
            self.table.append(row)
        self.inverse = [0] + [self.table[a].index(1) for a in range(1, self.size)]

    def mul(self, a, b):
        return self.table[a][b]


def rank(rows, field):
    pivots = {}
    for original in rows:
        row = original[:]
        for pos in range(len(row)):
            coeff = row[pos]
            if not coeff:
                continue
            if pos not in pivots:
                pivots[pos] = [field.mul(field.inverse[coeff], y) for y in row]
                break
            row = [x ^ field.mul(coeff, y) for x, y in zip(row, pivots[pos])]
    return len(pivots)


def xor_sum(terms):
    answer = 0
    for term in terms:
        answer ^= term
    return answer


def benes_matrix(s, field, rng):
    rows = [[int(i == j) for j in range(s)] for i in range(s)]
    log = s.bit_length() - 1
    for bit in list(range(log)) + list(reversed(range(log-1))):
        new_rows = []
        for i in range(s):
            a, b = rng.randrange(field.size), rng.randrange(field.size)
            partner = i ^ (1 << bit)
            new_rows.append([field.mul(a, x) ^ field.mul(b, y)
                             for x, y in zip(rows[i], rows[partner])])
        rows = new_rows
    return rows


def all_pairs(s):
    for k in range(1, s//2+1):
        for left in combinations(range(s), k):
            for right in combinations((j for j in range(s) if j not in left), k):
                yield left, right


def audited_network(s, f, rng):
    pairs = list(all_pairs(s))
    for attempt in range(1, 10001):
        a = benes_matrix(s, f, rng)
        d = [rng.randrange(f.size) for _ in range(s)]
        ad = [[f.mul(value, d[j]) for j, value in enumerate(row)] for row in a]
        polar = [[ad[i][j] ^ ad[j][i] for j in range(s)] for i in range(s)]
        if all(2*rank([[polar[i][j] for j in right] for i in left], f) >= len(left)
               for left, right in pairs):
            return ad, polar, pairs
    raise AssertionError("No network passed the finite rank tests")


def bit_verdict(x, ad, f):
    return xor_sum(f.mul(xi, f.mul(ad[i][j], xj))
                   for i, xi in enumerate(x) for j, xj in enumerate(x)) & 1


def verify_singleton_rectangles(ad, polar, f):
    s = len(ad)
    checked = 0
    for left, right in all_pairs(s):
        if len(left) != 1:
            continue
        i, j = left[0], right[0]
        rest = [u for u in range(s) if u not in (i, j)]
        for values in product(range(f.size), repeat=len(rest)):
            x = [0]*s
            for u, v in zip(rest, values):
                x[u] = v
            matrix = []
            for x[i] in range(f.size):
                row = []
                for x[j] in range(f.size):
                    row.append(bit_verdict(x, ad, f))
                matrix.append(row)
            for z in (0, 1):
                for mask in range(1, 1 << f.size):
                    selected = [u for u in range(f.size) if mask >> u & 1]
                    cols = sum(all(matrix[u][v] == z for u in selected) for v in range(f.size))
                    assert len(selected)*cols <= f.size
                    checked += 1
            for u, v in product(range(f.size), repeat=2):
                assert matrix[u][v] ^ matrix[u][0] ^ matrix[0][v] ^ matrix[0][0] == (
                    f.mul(u, f.mul(polar[i][j], v)) & 1)
    return checked


def verify_binary_ranks(polar, pairs, field):
    binary = Field(0b11)
    for left, right in pairs:
        matrix = [[polar[i][j] for j in right] for i in left]
        expanded = [[field.mul(1 << a, field.mul(polar[i][j], 1 << b)) & 1
                     for j in right for b in range(field.bits)]
                    for i in left for a in range(field.bits)]
        assert rank(expanded, binary) == field.bits*rank(matrix, field)


if __name__ == "__main__":
    rng = Random(25112026)
    small = Field(0b111)
    ad, polar, pairs = audited_network(4, small, rng)
    verify_binary_ranks(polar, pairs, small)
    rectangles = verify_singleton_rectangles(ad, polar, small)
    larger = Field(0x11b)
    _, big_polar, other_pairs = audited_network(8, larger, rng)
    verify_binary_ranks(big_polar, other_pairs, larger)
    # Each complete level has s/2 private coordinates on one side of its siblings.
    for depth in range(1, 12):
        assert sum(2**j * 2**(depth-j-1) for j in range(depth)) == depth*2**(depth-1)
    print(f"Checked {len(pairs)+len(other_pairs)} disjoint submatrices and "
          f"{rectangles} conditional rectangle bounds.")
