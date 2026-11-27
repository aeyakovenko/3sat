"""Finite checks of the transcript collision count and binary error detection."""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb
from operator import xor
from functools import reduce


def balanced_pairs(population, signatures):
    size, excess = divmod(population, signatures)
    return signatures * size * (size - 1) + 2 * size * excess


def replace_rows(seed, first, second):
    result = list(seed)
    for i, j in zip(sorted(first - second), sorted(second - first), strict=True):
        result[i] = seed[j]
    return tuple(result)


def query_transcript(rows, coin):
    """One named probe then one modular sum and a transcript-dependent OR."""
    address = coin % len(rows)
    observed = rows[address]
    summed = sum((v * (coin + 1) + observed) // 2 for v in rows) % 2
    bound = (observed + coin + summed) % 5
    flag = any(v <= bound for v in rows)
    return observed, summed, flag


def adaptive_edits():
    tested = 0
    for seed in permutations(range(6), 5):
        all_sets = [frozenset(s) for s in combinations(range(len(seed)), 2)]
        failures = Counter()
        for coin in range(5):
            original = query_transcript(seed, coin)
            count = 0
            for first, second in permutations(all_sets, 2):
                altered = replace_rows(seed, first, second)
                assert len(set(altered)) < len(seed)
                if query_transcript(altered, coin) == original:
                    failures[first, second] += 1
                    count += 1
                tested += 1
            minimum = balanced_pairs(comb(len(seed) - 1, 2), 4)
            assert count >= minimum
        assert max(failures.values()) * len(all_sets) * (len(all_sets) - 1) >= 5 * minimum
    return tested


def field_product(x, y):
    """F_8 with modulus z^3+z+1."""
    value = 0
    while y:
        if y & 1:
            value ^= x
        x <<= 1
        if x & 8:
            x ^= 0b1011
        y >>= 1
    return value


def field_power(x, degree):
    value = 1
    for _ in range(degree):
        value = field_product(value, x)
    return value


def syndromes():
    tests = 0
    for h in range(1, 4):
        for weight in range(1, 2 * h + 1):
            for labels in combinations(range(1, 8), weight):
                signature = [
                    reduce(xor, (field_power(a, j) for a in labels), 0)
                    for j in range(1, 2 * h, 2)
                ]
                assert any(signature)
                tests += 1
    return tests


def arbitrary_stamped_tags():
    n = 5
    tests = 0
    for tag_choices in product(range(4), repeat=n):
        def digest(word):
            return reduce(xor, ((tag_choices[i] >> ((word >> i) & 1)) & 1
                                for i in range(n)), 0)
        for x in range(1 << n):
            probe = (digest(x) + x.bit_count()) % n
            masks = [0] + [1 << i for i in range(n) if i != probe]
            equal_pairs = sum(digest(x ^ a ^ b) == digest(x)
                              for a, b in permutations(masks, 2))
            assert equal_pairs >= balanced_pairs(len(masks), 2)
            tests += 1
    return tests


if __name__ == "__main__":
    print(f"{adaptive_edits():,} edited adaptive transcripts checked")
    print(f"{arbitrary_stamped_tags():,} tagged local fingerprint bounds checked")
    print(f"{syndromes()} nonempty error patterns detected by the odd syndromes")
