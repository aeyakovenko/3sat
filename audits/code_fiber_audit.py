"""Exact checks of a two-lane simplex-code fiber and a total certified-reply rule."""

from collections import Counter, defaultdict
from itertools import combinations


def simplex_syndrome(raw):
    """Columns of the 3-by-7 binary generator are the nonzero three-bit vectors."""
    value = 0
    for i in range(7):
        if (raw >> i) & 1:
            value ^= i + 1
    return value


def two_lane_syndrome(raw):
    return simplex_syndrome(raw & 127) | (simplex_syndrome(raw >> 7) << 3)


def audit_fibers():
    fibers = defaultdict(list)
    for raw in range(1 << 14):
        fibers[two_lane_syndrome(raw)].append(raw)
    assert set(fibers) == set(range(64))
    nonzero_weights = [
        sum((word & column).bit_count() % 2 for column in range(1, 8)) for word in range(1, 8)
    ]
    assert nonzero_weights == [4] * 7
    checks = 0
    for width in range(4):
        for positions in combinations(range(14), width):
            mask = sum(1 << p for p in positions)
            for words in fibers.values():
                assert len(words) == 256
                histogram = Counter(word & mask for word in words)
                assert len(histogram) == 1 << width
                assert set(histogram.values()) == {256 >> width}
                checks += 1
    return fibers, checks


def audit_transpose():
    # Nodes 0,1,2 are a,b,c. Each later node is the XOR of its two predecessors.
    gates = [(0, 1), (0, 2), (1, 2), (3, 2)]
    output_nodes = [0, 1, 3, 2, 4, 5, 6]
    for weight in range(128):
        adjoint = [0] * 7
        for idx, node in enumerate(output_nodes):
            adjoint[node] ^= (weight >> idx) & 1
        for offset in reversed(range(len(gates))):
            left, right = gates[offset]
            adjoint[left] ^= adjoint[offset + 3]
            adjoint[right] ^= adjoint[offset + 3]
        result = sum(adjoint[i] << i for i in range(3))
        assert result == simplex_syndrome(weight)
        for word in range(8):
            node_values = [(word >> i) & 1 for i in range(3)]
            for left, right in gates:
                node_values.append(node_values[left] ^ node_values[right])
            encoded = sum(node_values[node] << j for j, node in enumerate(output_nodes))
            assert (weight & encoded).bit_count() % 2 == (result & word).bit_count() % 2


def next_native(syndrome, prefix):
    # Which syndrome bit the machine needs depends on its preceding replies.
    lane = (len(prefix) + sum(prefix)) % 2
    column = (len(prefix) + (prefix[-1] if prefix else 0)) % 3
    return (syndrome >> (3 * lane + column)) & 1


def verifier(prefix, reply, certificate, probe):
    """Certificate zero supplies a legal reply for every prefix and raw word."""
    step = len(prefix)
    history = sum((i + 1) * bit for i, bit in enumerate(prefix))
    first = (4 * step + history) % 14
    if certificate == 0:
        return reply == probe(first)
    gate = probe((first + 2) % 14)
    selector = probe((first + 5 + gate) % 14)
    return gate == 1 and reply == selector


def allowed_replies(raw, prefix):
    probe = lambda i: (raw >> i) & 1
    return [reply for reply in (0, 1)
            if any(verifier(prefix, reply, cert, probe) for cert in (0, 1))]


def forbidding_clauses(prefix, wrong, certificate):
    """Each accepting decision-tree leaf contributes the clause negating its path."""
    clauses = []

    def explore(answers):
        try:
            accepted = verifier(prefix, wrong, certificate, answers.__getitem__)
        except KeyError as request:
            address = request.args[0]
            for bit in (0, 1):
                explore({**answers, address: bit})
        else:
            if accepted:
                clauses.append(tuple((i, 1 - b) for i, b in answers.items()))

    explore({})
    return clauses


def all_histories(raw, steps):
    histories = [()]
    saw_ambiguity = False
    for _ in range(steps):
        next_histories = []
        for prefix in histories:
            replies = allowed_replies(raw, prefix)
            assert replies
            saw_ambiguity |= len(replies) > 1
            next_histories.extend(prefix + (bit,) for bit in replies)
        histories = next_histories
    return histories, saw_ambiguity


def audit_no_wrong(fibers):
    counts = Counter()
    for syndrome, words in fibers.items():
        prefix = ()
        cnf = []
        for _ in range(3):
            expected = next_native(syndrome, prefix)
            for certificate in (0, 1):
                cnf.extend(forbidding_clauses(prefix, 1 - expected, certificate))
            prefix += (expected,)
        assert all(len(clause) <= 2 for clause in cnf)
        for raw in words:
            cnf_accepts = all(any((raw >> i) & 1 == b for i, b in clause) for clause in cnf)
            histories, ambiguous = all_histories(raw, len(prefix))
            assert cnf_accepts == (histories == [prefix])
            counts['success' if cnf_accepts else 'failure'] += 1
            counts['ambiguous'] += ambiguous
    assert min(counts.values()) > 0
    return counts


def audit_tensor():
    # The [3,2,2] single-parity-check code, tensored with itself.
    basis = [0b101, 0b110]
    rows = [sum(((u >> i) & (v >> j) & 1) << (3 * i + j)
                for i in range(3) for j in range(3)) for u in basis for v in basis]
    weights = []
    for coefficients in range(1, 16):
        combination = 0
        for i, row in enumerate(rows):
            if coefficients & (1 << i):
                combination ^= row
        weights.append(combination.bit_count())
    assert min(weights) == 4
    fibers = defaultdict(list)
    for raw in range(512):
        y = sum(((raw & row).bit_count() % 2) << i for i, row in enumerate(rows))
        fibers[y].append(raw)
    assert len(fibers) == 16 and all(len(xs) == 32 for xs in fibers.values())
    for positions in combinations(range(9), 3):
        mask = sum(1 << j for j in positions)
        for words in fibers.values():
            assert set(Counter(x & mask for x in words).values()) == {4}
    print("Tensor code [9,4,4]: all 16 fibers have uniform three-bit projections")


if __name__ == '__main__':
    audit_tensor()
    all_fibers, marginals = audit_fibers()
    audit_transpose()
    outcomes = audit_no_wrong(all_fibers)
    print(f'64 fibers of size 256; {marginals} uniform marginal histograms of width at most 3.')
    print('All 128 transposed outputs and 1,024 bilinear identities passed.')
    print(f'No-wrong CNF agreed on all 16,384 raw words: {outcomes["success"]} unique '
          f'correct histories, {outcomes["failure"]} failures, {outcomes["ambiguous"]} '
          'words with multiple legal histories.')
