"""Check the bank changes of basis and a selector-decoded rank decomposition."""
from itertools import product
from random import Random


def parity(x):
    return x.bit_count() % 2


def multiply(a, b, side):
    value = 0
    for i, j in product(range(side), repeat=2):
        bit = sum(((a >> (i * side + k)) & (b >> (k * side + j)) & 1)
                  for k in range(side)) % 2
        value |= bit << (i * side + j)
    return value


def transform(values, pos, add):
    bit = 1 << pos
    for i in range(len(values)):
        if not i & bit:
            a, b = values[i], values[i | bit]
            if add:
                values[i | bit] = a ^ b
            else:
                values[i], values[i | bit] = a + b, a - b


def apply_matrix(matrix, vector, d):
    mask = (1 << d) - 1
    return sum(parity(vector & ((matrix >> (i*d)) & mask)) << i for i in range(d))


def mirabolic_arrows(d, p):
    # P_(d+1) consists of affine transforms x -> hx+b on d binary coordinates.
    # Coefficient field p=3 divides |GL_2(2)|, testing the modular case.
    q = 1 << d
    group = [h for h in range(1 << (d*d)) if
             len({apply_matrix(h, x, d) for x in range(q)}) == q]
    actions = {h: [apply_matrix(h, x, d) for x in range(q)] for h in group}
    dual = {(h, u): next(v for v in range(q) if
            all(parity(u & x) == parity(v & actions[h][x]) for x in range(q)))
            for h in group for u in range(q)}
    base = 1 << (d-1)
    transports = {v: next(h for h in group if dual[h, base] == v) for v in range(1, q)}
    identity = sum(1 << (i*d + i) for i in range(d))
    inverses = {h: next(k for k in group if multiply(h, k, d) == identity) for h in group}
    arrow = {(h,u): [pow(q, -1, p) * (-1)**parity(dual[h,u] & x) % p for x in range(q)]
             for h in group for u in range(q)}
    def label(h, u):
        if not u:
            return h
        v = dual[h,u]
        return v, u, multiply(inverses[transports[v]], multiply(h, transports[u], d), d)
    assert len({label(h,u) for h,u in arrow}) == len(arrow)
    for (h,u), (k,v) in product(arrow, repeat=2):
        hk = multiply(h,k,d)
        vals = [0] * q
        for i, coeff1 in enumerate(arrow[h,u]):
            for j, coeff2 in enumerate(arrow[k,v]):
                vals[i ^ actions[h][j]] += coeff1 * coeff2
        composes = u == dual[k,v]
        assert [w % p for w in vals] == (arrow[hk,v] if composes else [0]*q)
        if u and v and composes:
            a, b, c = label(h,u)
            e, f, g = label(k,v)
            assert b == e and label(hk,v) == (a,f,multiply(c,g,d))
    print(f"P_{d+1} over F_{p}: all {len(arrow)**2} arrow products and orbit transports")


def matrix_truth_tables():
    d = 2
    n = d * d
    alphabet = range(1 << n)
    values = []
    for a, b in product(alphabet, repeat=2):
        ab = multiply(a, b, d)
        block = [int(z == ab) for z in alphabet]
        for k in range(n):
            transform(block, k, add=False)
        assert block == [(-1) ** parity(ab & z) for z in alphabet]
        values.extend(parity(z & ab) for z in alphabet)
    # Unique multilinear coefficients are indexed by the masks of their support.
    for k in range(3 * n):
        transform(values, k, add=True)
    expected = {((1 << (d*i+k)) << (2*n)) | ((1 << (d*k+j)) << n) | (1 << (d*i+j))
                for i, k, j in product(range(d), repeat=3)}
    assert {idx for idx, bit in enumerate(values) if bit} == expected
    print(f"side {d}: all {len(values)} parity entries and subset coefficients, {len(expected)} triangles")


def tag_control(r):
    m = 1 << r
    words = list(product(range(m), repeat=6))
    # In order (u,v,x,y,z,w), transform one endpoint of each pair.
    values = [(-1) ** (parity(y & z) ^ parity(u & w) ^ parity(v & x))
              for u, v, x, y, z, w in words]
    for slot in (2, 4, 5):
        for k in range(r):
            transform(values, (5 - slot) * r + k, add=False)
    expected = [m**3 * int(y == z and u == w and v == x) for u, v, x, y, z, w in words]
    assert values == expected
    assert sum(v != 0 for v in values) == m**3
    print(f"tagged control r={r}: all {len(values)} transformed triangle entries")


# Each row gives the coefficient masks in Strassen's decomposition over F2.
# In all three banks the four entries are labeled 00,01,10,11.
TERMS = [
    (0b1001, 0b1001, 0b1001), (0b1100, 0b0001, 0b1100),
    (0b0001, 0b1010, 0b1010), (0b1000, 0b0101, 0b0101),
    (0b0011, 0b1000, 0b0011), (0b0101, 0b0011, 0b1000),
    (0b1010, 0b1100, 0b0001),
]


def order_entries(encoded, depth):
    d = 1 << depth
    values = []
    for digits in product(range(4), repeat=depth):
        i = j = 0
        for x in digits:
            i, j = i * 2 + x // 2, j * 2 + x % 2
        values.append((encoded >> (i * d + j)) & 1)
    return values


def selected_value(values, bank, selector):
    for digit in reversed(selector):
        if digit >= len(TERMS):
            return 0
        coefficients = TERMS[digit][bank]
        values = [sum(values[start+k] for k in range(4) if coefficients & (1 << k)) % 2
                  for start in range(0, len(values), 4)]
    assert len(values) == 1
    return values[0]


def test_selection(depth, examples):
    d = 1 << depth
    selectors = list(product(range(8), repeat=depth))
    for a, b, z in examples:
        banks = [order_entries(value, depth) for value in (a, b, z)]
        answer = 0
        for digits in selectors:
            answer ^= int(all(selected_value(x, k, digits) for k, x in enumerate(banks)))
        assert answer == parity(multiply(a, b, d) & z)
    print(f"side {d}: {len(selectors)} selector codes on {len(examples)} matrix triples")


if __name__ == "__main__":
    mirabolic_arrows(2, 3)
    mirabolic_arrows(2, 5)
    matrix_truth_tables()
    tag_control(1)
    tag_control(2)
    test_selection(1, list(product(range(16), repeat=3)))
    rng = Random(123)
    test_selection(2, [tuple(rng.getrandbits(16) for _ in range(3)) for _ in range(64)])
