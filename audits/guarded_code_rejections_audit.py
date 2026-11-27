"""Finite audit of the Reed–Solomon guard on GF(4), with a one-bit radius.

Four points and degree < 2 make positive and negative arrays pairwise independent.
The scale is too small for the asymptotic rare-event estimates in the note.
"""

from collections import Counter
from itertools import combinations, product


FIELD = range(4)
POINTS = range(4)
BITS = range(8)
RADIUS = 1
# Polynomial basis modulo x²+x+1. Field addition is binary XOR.
MULTIPLY = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))


def pack(symbols):
    return sum(value << (2 * i) for i, value in enumerate(symbols))


def raw_laws(code):
    arrays = list(product(FIELD, repeat=4))
    positive = [word + fill for word, fill in product(code, arrays)]
    negative = [tuple(y ^ z for y, z in zip(fill, word)) + fill
                for fill, word in product(arrays, code)]
    return positive, negative


def audit_marginals_and_moments(positive, negative):
    pairs = list(combinations(range(8), 2))
    for law in (positive, negative):
        for i, j in pairs:
            counts = Counter((row[i], row[j]) for row in law)
            assert len(counts) == 16 and set(counts.values()) == {len(law) // 16}

    for shift in FIELD:
        def one_probe_score(array):
            return sum((array[(4 + coin + shift) % 8] ^ coin) & 1 for coin in FIELD)

        # Two independent fresh challenges disclose at most two raw entries.
        assert (sum(one_probe_score(row) ** 2 for row in positive) ==
                sum(one_probe_score(row) ** 2 for row in negative))

        def empirical_score(array):
            return sum(array[(coin + shift) % 8] == coin for coin in array)

        # One empirical trial discloses its selected raw challenge and one further address.
        assert (sum(empirical_score(row) for row in positive) ==
                sum(empirical_score(row) for row in negative))
    print(f'{len(pairs)} two-symbol marginals per law and four fresh/empirical moment comparisons passed')


def audit_distance(positive, negative, codewords):
    close = {x for x in range(256) if any((x ^ word).bit_count() <= RADIUS for word in codewords)}
    for array in negative:
        difference = pack(array[:4]) ^ pack(array[4:])
        assert difference in codewords
        for position in range(16):
            # Changing either raw partner toggles the same bit in the XOR.
            assert difference ^ (1 << (position % 8)) in close
    positives_in_guard = sum((pack(row[:4]) ^ pack(row[4:])) in close for row in positive)
    assert positives_in_guard * 256 == len(positive) * len(close)
    print(f'{16 * len(negative)} single-bit negative modifications stayed inside the guard')


def audit_partial_reads(codewords):
    # A paired bit is either unseen, fixed to XOR zero, or fixed to XOR one.
    deleted_masks = [0] + [3 << (2 * point) for point in POINTS]
    checked = 0
    excluding = 0
    for transcript in product((None, 0, 1), repeat=8):
        observed = sum(1 << i for i in BITS if transcript[i] is not None)
        values = sum(1 << i for i in BITS if transcript[i] == 1)
        mismatch = {word: ((word ^ values) & observed).bit_count() for word in codewords}
        excludes_guard = min(mismatch.values()) > RADIUS
        excluding += excludes_guard
        for deleted in deleted_masks:
            # Missing XOR bits at a deleted point are filled by zero before interpolation.
            fiber = [word for word in codewords if (word ^ values) & deleted == 0]
            outside = (observed & ~deleted).bit_count()
            assert fiber and 2 * sum(mismatch[word] for word in fiber) == outside * len(fiber)
            if excludes_guard:
                assert outside > 2 * RADIUS
            checked += 1
    assert excluding > 0
    print(f'{checked} partial transcript/interpolation fibers passed, {excluding} transcripts exclude the guard')


if __name__ == '__main__':
    code = [tuple(a ^ MULTIPLY[b][i] for i in POINTS) for a, b in product(FIELD, repeat=2)]
    positive, negative = raw_laws(code)
    assert len(positive) == len(negative) == 4096
    codewords = {pack(word) for word in code}
    assert len(codewords) == 16
    print(f'{len(positive)} raw arrays per law')
    audit_marginals_and_moments(positive, negative)
    audit_distance(positive, negative, codewords)
    audit_partial_reads(codewords)
