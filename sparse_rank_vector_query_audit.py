"""Exact two-sided signed vector-query costs over GF(2) through dimension four."""

from itertools import combinations


def binary_basis(vectors):
    basis = {}
    for word in vectors:
        insert(basis, word)
    return tuple(basis.values())


def reduce_word(basis, word):
    while word:
        pivot = word.bit_length() - 1
        if pivot not in basis:
            break
        word ^= basis[pivot]
    return word


def insert(basis, word):
    word = reduce_word(basis, word)
    if word:
        basis[word.bit_length() - 1] = word


def pack(vectors, d):
    return sum(value << (i * d) for i, value in enumerate(vectors))


def columns(matrix, d):
    return [(matrix >> (i * d)) & ((1 << d) - 1) for i in range(d)]


def times(matrix, x, d):
    result = 0
    while x:
        bit = x & -x
        result ^= (matrix >> (d * (bit.bit_length() - 1))) & ((1 << d) - 1)
        x ^= bit
    return result


def transpose(matrix, d):
    return sum(((matrix >> (d * i + j)) & 1) << (d * j + i)
               for i in range(d) for j in range(d))


def field_times(x, y, d):
    modulus = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011}[d]
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x >> d:
            x ^= modulus
    return result


def space(basis):
    elements = [0]
    for x in basis:
        elements += [v ^ x for v in elements]
    return tuple(sorted(elements))


def subspace_reps(d, action):
    reps = []
    for k in range(d + 1):
        pending = {space(xs) for xs in combinations(range(1, 1 << d), k)
                   if len(binary_basis(xs)) == k}
        layer = []
        while pending:
            subspace = min(pending)
            layer.append(binary_basis(subspace))
            for permutation in action:
                pending.discard(tuple(sorted(permutation[x] for x in subspace)))
        reps.append(layer)
    return reps


def singer_data(d):
    size = 1 << d
    multipliers = [[field_times(a, x, d) for x in range(size)] for a in range(1, size)]
    mats = [pack([p[1 << i] for i in range(d)], d) for p in multipliers]
    duals = [[times(transpose(m, d), x, d) for x in range(size)] for m in mats]
    orbit = [-1] * (size ** d)
    ranks = []
    for matrix, oid in enumerate(orbit):
        if oid != -1:
            continue
        oid = len(ranks)
        ranks.append(len(binary_basis(columns(matrix, d))))
        for right in mats:
            middle = [times(matrix, x, d) for x in columns(right, d)]
            for left in multipliers:
                orbit[pack([left[x] for x in middle], d)] = oid
    return orbit, ranks, subspace_reps(d, duals), subspace_reps(d, multipliers)


def promise_masks(ranks, d):
    strata = [0] * (d + 1)
    for index, rank in enumerate(ranks):
        strata[rank] |= 1 << index
    return {s: strata[0] | sum(strata[r] for r in range(1, d + 1) if s & (1 << (r - 1)))
            for s in range(1, 1 << d)}


def census(d, ranks, layers, certificate=None):
    masks = promise_masks(ranks, d)
    bases = {s: {} for s in masks}
    costs = {}
    for q, generators in enumerate(layers):
        for word in generators:
            for s, basis in bases.items():
                insert(basis, word & masks[s])
        if certificate is not None:
            certificate(q, masks, bases)
        for s in list(bases):
            if reduce_word(bases[s], 1) == 0:
                costs[s] = q
                del bases[s]
    assert costs.keys() == masks.keys()
    return costs


def averaged_layer(d, q, orbit, transposes, left, right, answers):
    for a in range(q + 1):
        b = q - a
        for xs in left[a]:
            for ys in right[b]:
                left_answers, right_answers = answers[xs], answers[ys]
                fibers = {}
                for matrix, oid in enumerate(orbit):
                    key = (left_answers[transposes[matrix]] << (d * b)) | right_answers[matrix]
                    fibers[key] = fibers.get(key, 0) ^ (1 << oid)
                yield from set(fibers.values())


def individual_answers(d, matrices):
    # Direct row and column sums, independent of the field action and of times().
    packets = []
    for left in (False, True):
        for v in range(1, 1 << d):
            packet = []
            for matrix in matrices:
                answer = 0
                for i in range(d):
                    indices = (d * i + j if left else d * j + i
                               for j in range(d) if v & (1 << j))
                    answer |= (sum((matrix >> index) & 1 for index in indices) % 2) << i
                packet.append(answer)
            packets.append(packet)
    return packets


def raw_layer(d, q, packets):
    count = 1 << (d * d)
    for queries in combinations(packets, q):
        fibers = {}
        for i in range(count):
            signature = tuple(p[i] for p in queries)
            fibers[signature] = fibers.get(signature, 0) | (1 << i)
        yield from fibers.values()


def verify_pair_certificate(d, support):
    assert 0 in support and len(support) % 2 == 0
    packets = individual_answers(d, support)
    for p, r in combinations(packets, 2):
        parity = set()
        for responses in zip(p, r):
            if responses in parity:
                parity.remove(responses)
            else:
                parity.add(responses)
        assert not parity


def run(d):
    orbit, ranks, left, right = singer_data(d)
    transposes = [transpose(matrix, d) for matrix in range(len(orbit))]
    probes = {xs for group in (left, right) for level in group for xs in level}
    answers = {xs: [pack([times(matrix, x, d) for x in xs], d) for matrix in range(len(orbit))]
               for xs in probes}

    def certify(q, masks, bases):
        if (d, q) != (4, 2):
            return
        s = 0b1001  # allowed positive ranks 1 and 4
        basis = bases[s]
        # Back-substitute an annihilator with coordinate zero prescribed to be 1.
        dual = 1
        assert 0 not in basis
        for pivot, row in sorted(basis.items()):
            if (row & dual).bit_count() % 2:
                dual |= 1 << pivot
        dual &= masks[s]
        assert all((row & dual).bit_count() % 2 == 0 for row in basis.values())
        support = [matrix for matrix, i in enumerate(orbit) if dual & (1 << i)]
        verify_pair_certificate(d, support)
        print("  {1,4} lower certificate: orbit mask", hex(dual), "matrices", len(support))

    layers = (averaged_layer(d, q, orbit, transposes, left, right, answers) for q in range(d + 1))
    costs = census(d, ranks, layers, certify)
    if d <= 3:
        matrices = range(1 << (d * d))
        raw_ranks = [len(binary_basis(columns(m, d))) for m in matrices]
        packets = individual_answers(d, matrices)
        raw_layers = (raw_layer(d, q, packets) for q in range(d + 1))
        assert census(d, raw_ranks, raw_layers) == costs
    expected = {1: [1], 2: [2, 1, 2], 3: [2, 2, 3, 1, 2, 2, 3],
                4: [2, 3, 4, 2, 3, 3, 4, 1, 3, 3, 4, 2, 4, 3, 4]}
    assert [costs[s] for s in range(1, 1 << d)] == expected[d]
    for rank in range(1, d + 1):
        assert costs[1 << (rank - 1)] == min(2 * rank, d - rank + 1)
    print("d =", d, "orbits by rank =", [ranks.count(i) for i in range(d + 1)])
    for q in range(1, d + 1):
        sets = [tuple(r for r in range(1, d + 1) if s & (1 << (r - 1)))
                for s in sorted(costs) if costs[s] == q]
        print(" ", q, "queries:", sets)


if __name__ == "__main__":
    for dimension in range(1, 5):
        run(dimension)
