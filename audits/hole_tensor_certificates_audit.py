"""Exhaustive binary cut tests and small higher-bond span contractions."""
from itertools import product
from random import Random


def matrix_full(rows):
    nonzero = {row for row in rows if row}
    return len(nonzero) >= 2  # two columns over F_2


def rows_on_bit(word, arity, bit):
    """Fix all other indices, leaving the two values on one bit as a row."""
    step = 1 << bit
    return [((word >> a) & 1) | (((word >> (a | step)) & 1) << 1)
            for a in range(1 << arity) if not a & step]


def transform_middle(middle, left, right):
    result = 0
    for a, y, b in product(range(2), repeat=3):
        entry = 0
        for u, w in product(range(2), repeat=2):
            entry ^= ((left >> (2 * a + u)) & (middle >> (4 * u + 2 * y + w))
                      & (right >> (2 * b + w)) & 1)
        result |= entry << (4 * a + 2 * y + b)
    return result


def path_cut_checks():
    cut_full = [matrix_full(rows_on_bit(s, 3, 0)) and matrix_full(rows_on_bit(s, 3, 2))
                for s in range(256)]
    endpoint_full = [matrix_full(rows_on_bit(e, 2, 0)) for e in range(16)]
    pairs = 0
    for mid, left, right in product(range(256), range(16), range(16)):
        expected = cut_full[mid] and endpoint_full[left] and endpoint_full[right]
        actual = transform_middle(mid, left, right)
        assert cut_full[actual] == expected
        if actual.bit_count() == 1:
            assert not expected
        elif actual.bit_count() == 2:
            support = [i for i in range(8) if actual >> i & 1]
            if support[0] ^ support[1] == 7:
                assert expected
        pairs += 1
    return pairs


def row_basis(rows):
    pivots = {}
    for row in rows:
        while row:
            i = row.bit_length() - 1
            if i not in pivots:
                pivots[i] = row
                break
            row ^= pivots[i]
    return list(pivots.values())


def span(rows):
    found = {0}
    for row in rows:
        found |= {x ^ row for x in found}
    return found


def contract(rows, left, right):
    out = 0
    for i, line in enumerate(rows):
        if left >> i & 1:
            for j, row in enumerate(line):
                if right >> j & 1:
                    out ^= row
    return out


def choose_three_state_path(bits, word):
    # States 0,1,2 are the zero-only state and the two parity states.
    states = {0, 1}
    for step, bit in enumerate(bits):
        if word >> step & 1:
            states = {1 + ((s - 1) ^ bit) for s in states if s != 0}
        else:
            states &= {0}
    return bool(states & {0, 2})


def cycle_table(bits):
    v = len(bits) + 1
    allowed = []
    for word in range(1 << v):
        if any(((word >> i) ^ (word >> (i + 1))) & 1 != bit for i, bit in enumerate(bits)):
            continue
        if (word >> (v - 1), word & 1) != (1, 0):
            allowed.append(word)
    return allowed


def hidden_parity():
    checked = 0
    for v in range(2, 7):
        full = (1 << v) - 1
        for bits in product(range(2), repeat=v):
            expected = {0, full} if sum(bits) % 2 else {0}
            assert {y for y in range(1 << v) if choose_three_state_path(bits, y)} == expected
            checked += 1
        for bits in product(range(2), repeat=v - 1):
            support = cycle_table(bits)
            if sum(bits) % 2:
                assert len(support) == 1
            else:
                assert len(support) == 2 and support[0] ^ support[1] == full
            checked += 1
    return checked


def region_checks():
    rng = Random(26273)
    for _ in range(3000):
        ldim, rdim = rng.randrange(2, 6), rng.randrange(2, 6)
        left = [rng.randrange(1 << ldim) for _ in range(rng.randrange(1, 13))]
        right = [rng.randrange(1 << rdim) for _ in range(rng.randrange(1, 13))]
        matrices = [[[rng.randrange(4) for _ in range(rdim)] for _ in range(ldim)]
                    for _ in range(2)]
        actual = [contract(m, l, r) for m, l, r in product(matrices, left, right)]
        using_basis = [contract(m, l, r)
                       for m, l, r in product(matrices, row_basis(left), row_basis(right))]
        assert span(actual) == span(using_basis)
    return 3000


def gauge_decoder():
    bases = [(a, b) for a, b in product(range(1, 4), repeat=2) if a != b]

    def dot(u, v):
        return (u & v).bit_count() % 2

    def trilinear(vectors):
        return sum(1 << (4 * i + 2 * j + k)
                   for i, j, k in product(range(2), repeat=3)
                   if vectors[0] >> i & vectors[1] >> j & vectors[2] >> k & 1)

    decompositions = {}
    for ports in product(bases, repeat=3):
        terms = tuple(sorted(zip(*ports)))
        tensor = trilinear(terms[0]) ^ trilinear(terms[1])
        assert decompositions.setdefault(tensor, terms) == terms
    assert len(decompositions) == 108

    rng = Random(627)
    # Six visible leaves and four trivalent hidden vertices.
    neighbors = [(6,), (6,), (7,), (8,), (9,), (9,),
                 (0, 1, 7), (6, 2, 8), (7, 3, 9), (8, 4, 5)]
    full = (1 << 6) - 1
    for trial in range(500):
        first_word = rng.randrange(full + 1)
        gauges = {}
        for a, near in enumerate(neighbors):
            for b in near:
                if a < b:
                    pair = rng.choice(bases)
                    dual = next(q for q in bases if all(dot(x, y) == (i == j)
                                for i, x in enumerate(pair) for j, y in enumerate(q)))
                    gauges[a, b], gauges[b, a] = pair, dual
        local = {}
        for v in range(6, len(neighbors)):
            ports = [gauges[v, dest] for dest in neighbors[v]]
            terms = tuple(zip(*ports))
            local[v] = decompositions[trilinear(terms[0]) ^ trilinear(terms[1])]

        def leaf_rows(leaf):
            bit = first_word >> leaf & 1
            vectors = gauges[leaf, neighbors[leaf][0]]
            return vectors[bit], vectors[1 - bit]

        def walk(v, prev, incoming):
            if v < 6:
                y, = [b for b, row in enumerate(leaf_rows(v)) if dot(row, incoming)]
                return y << v
            port = neighbors[v].index(prev)
            term, = [t for t in local[v] if dot(t[port], incoming)]
            result = 0
            for i, w in enumerate(neighbors[v]):
                if w != prev:
                    result |= walk(w, v, term[i])
            return result

        tag_zero = walk(neighbors[0][0], 0, leaf_rows(0)[0])
        assert tag_zero == (first_word ^ (full if first_word & 1 else 0))
    return len(decompositions), trial + 1


if __name__ == '__main__':
    print(f"{path_cut_checks():,} arbitrary path representations checked across both cuts")
    print(f"{region_checks():,} higher-bond region span recursions checked")
    print(f"{hidden_parity()} hidden-parity path and cycle supports checked")
    basis_types, trees = gauge_decoder()
    print(f"{basis_types} trivalent factor types and {trees} gauged tree reconstructions checked")
