"""Expand path choices literally and compare their signed sums to matrix products."""
from itertools import product
from math import prod


class Field:
    def __init__(self, p, extension_degree):
        self.p = p
        self.degree = extension_degree
        self.size = p**extension_degree

    def digits(self, a):
        return tuple((a // self.p**i) % self.p for i in range(self.degree))

    def decode(self, chunks):
        if len(chunks) != self.degree or any(c < 0 or c >= self.p for c in chunks):
            return None
        return sum(c * self.p**i for i, c in enumerate(chunks))

    def add(self, a, b):
        if self.p == 2:
            return a ^ b
        if self.degree == 1:
            return (a + b) % self.p
        return self.decode(tuple((x + y) % self.p for x, y in zip(self.digits(a), self.digits(b))))

    def multiply(self, a, b):
        if self.degree == 1:
            return a*b % self.p
        if self.size == 9:
            a0, a1 = self.digits(a)
            b0, b1 = self.digits(b)
            # Polynomial basis 1,x with x^2=-1 over F3.
            return self.decode(((a0 * b0 - a1 * b1) % 3, (a0 * b1 + a1 * b0) % 3))
        assert self.size == 4
        # Polynomial basis 1,x subject to x^2=x+1.
        result = (a if b & 1 else 0) ^ (a << 1 if b & 2 else 0)
        return result ^ 7 if result & 4 else result


def matrix_product(a, b, f):
    def entry(row, col):
        acc = 0
        for k, value in enumerate(a[row]):
            acc = f.add(acc, f.multiply(value, b[k][col]))
        return acc
    return [[entry(i, j) for j in range(len(b[0]))] for i in range(len(a))]


def as_square(bits):
    return [[bits >> (2*i+j) & 1 for j in range(2)] for i in range(2)]


def binary_squares():
    f = Field(2, 1)
    cases = positive = 0
    choices = tuple(product(range(4), repeat=4))
    for a, b, c in product((as_square(i) for i in range(16)), repeat=3):
        reference = matrix_product(a, b, f)
        banks = [(1, c[i][j], a[i][0] & b[0][j], a[i][1] & b[1][j])
                 for i, j in product(range(2), repeat=2)]
        witnesses = sum(all(banks[j][tag] for j, tag in enumerate(pick))
                        for pick in choices)
        assert (witnesses % 2) == (reference == c)
        positive += reference == c
        cases += 1
    return cases, cases*len(choices), positive


def signed_digit_sum(c, paths, field):
    banks = []
    for i, digit in enumerate(field.digits(c)):
        # One neutral branch and the expansion of -(C_i - sum paths_i)^(p-1).
        inner = [digit] + [-field.digits(path)[i] for path in paths]
        banks.append([1] + [-prod(term) for term in product(inner, repeat=field.p - 1)])
    return sum(prod(choices) for choices in product(*banks))


def path_value(factors, field, row, column, inner):
    endpoint = (row,) + tuple(inner) + (column,)
    value = 1
    for j, factor in enumerate(factors):
        value = field.multiply(value, factor[endpoint[j]][endpoint[j+1]])
    return value


def scalar_chains(field, shape):
    assert shape[0] == shape[-1] == 1
    count = sum(m*n for m, n in zip(shape, shape[1:]))
    paths = tuple(product(*(range(q) for q in shape[1:-1])))
    cases = positive = 0
    for entries in product(range(field.size), repeat=count):
        start = 0
        factors = []
        for m, n in zip(shape, shape[1:]):
            rows = [entries[start+i*n:start+(i+1)*n] for i in range(m)]
            factors.append(rows)
            start += m*n
        reference = factors[0]
        for factor in factors[1:]:
            reference = matrix_product(reference, factor, field)
        path_terms = [path_value(factors, field, 0, 0, k) for k in paths]
        for c in range(field.size):
            verdict = signed_digit_sum(c, path_terms, field) % field.p
            assert verdict == (reference[0][0] == c)
            positive += verdict
            cases += 1
    return cases, positive


def rank_mod(rows, p):
    pivots = {}
    for template in rows:
        row = [entry % p for entry in template]
        for j in range(len(row)):
            value = row[j]
            if value == 0:
                continue
            if j in pivots:
                row = [(x - value*y) % p for x, y in zip(row, pivots[j])]
            else:
                scale = pow(value, -1, p)
                pivots[j] = [(scale*x) % p for x in row]
                break
    return len(pivots)


def parity_matrix(d):
    universe = range(1, 1 << d)
    rows = [[(v & x).bit_count() % 2 for x in universe] for v in universe]
    ranks = tuple(rank_mod(rows, p) for p in (2, 3, 5))
    assert ranks == (d, len(universe), len(universe))
    for i, j in product(range(len(rows)), repeat=2):
        inner = sum(a*b for a, b in zip(rows[i], rows[j]))
        expected = 1 if d == 1 else (1 << (d-2))*(1+int(i == j))
        assert inner == expected
    # M times any nonzero linear form on the index bits is the
    # corresponding column of its Gram matrix, including the diagonal.
    return ranks


def packed_decoder(field, d, queries):
    blocks = queries * field.degree * (field.p - 1)
    cuts = [i * d // blocks for i in range(blocks + 1)]
    widths = [0] * queries
    tables = []
    for v in range(2**d):
        left = [[] for _ in widths]
        right = [[] for _ in widths]
        for i, (start, stop) in enumerate(zip(cuts, cuts[1:])):
            query, place = divmod(i, field.degree * (field.p - 1))
            digit = place // (field.p - 1)
            limit = 1 << (stop - start)
            block = (v >> start) % limit
            for pattern in range(1, limit):
                left[query].append(field.p**digit if block == pattern else 0)
                right[query].append((pattern & block).bit_count() % 2)
        tables.append((left, right))
    widths = [len(features) for features in tables[0][0]]
    assert max(widths) <= field.degree * (field.p - 1) * (2**((d + blocks - 1)//blocks) - 1)
    for v, (left, _) in enumerate(tables):
        for x, (_, right) in enumerate(tables):
            odd = 0
            for row, col in zip(left, right):
                value = 0
                for a, b in zip(row, col):
                    value = field.add(value, field.multiply(a, b))
                odd ^= sum(field.digits(value)) % 2
            assert odd == (v & x).bit_count() % 2
    return widths


if __name__ == '__main__':
    cases, witnesses, positive = binary_squares()
    print(f"GF(2) side-two graph: {cases} files, {witnesses} complete tag tuples, "
          f"{positive} positive files")
    for f in (Field(2,1), Field(3,1), Field(2,2)):
        width = (f.p-1).bit_length()
        domain = list(product(range(1 << width), repeat=f.degree))
        decoded = [f.decode(chunks) for chunks in domain]
        assert sorted(n for n in decoded if n is not None) == list(range(f.size))
        for n in range(f.size):
            assert f.decode(f.digits(n)) == n
        for shape in ((1, 2, 1), (1, 2, 1, 1)):
            cases, positive = scalar_chains(f, shape)
            print(f"GF({f.size}), {shape}: {cases} complete chains including the claim, "
                  f"{positive} positive")
    shape = (1, 2, 2, 1)
    cases, positive = scalar_chains(Field(2,1), shape)
    print(f"GF(2), {shape}: {cases} cases with 4 paths, {positive} positive")
    for d in range(1,6):
        print(f"d={d}: ranks of odd-dot matrix over 2,3,5 equal {parity_matrix(d)}")
    for field, queries in ((Field(3, 1), 1), (Field(5, 1), 1), (Field(3, 2), 1), (Field(3, 2), 2)):
        print(f"GF({field.size}) packed parity decoder, all 4096 vector pairs at d=6, "
              f"widths {packed_decoder(field, 6, queries)}")
