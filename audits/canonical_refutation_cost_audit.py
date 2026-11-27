"""Enumerate witness-label distributions and compare with the stated counts."""

from collections import Counter
from itertools import product
from math import comb


def audit(width=5):
    tested_patterns = 0
    checked_equalities = 0
    tables = tuple(product((0, 1), repeat=width))
    # A mask chooses the available labels {0}, {1}, neither, or both.
    for masks in product(range(4), repeat=width):
        both = masks.count(3)
        single = masks.count(1) + masks.count(2)
        absent = masks.count(0)
        observed = Counter()
        for table in tables:
            score = sum(bool(mask & (1 << bit)) for mask, bit in zip(masks, table))
            observed[score] += 1
            if not both:
                # Use mask 2 for SAT, 1 for refutable UNSAT, 0 for hard UNSAT.
                agreement = sum((mask == 2) == bool(bit) for mask, bit in zip(masks, table))
                hard = sum(mask == 0 and bit == 0 for mask, bit in zip(masks, table))
                assert agreement - score == hard
                checked_equalities += 1
        predicted = {both + k: comb(single, k) * (1 << (both + absent)) for k in range(single + 1)}
        assert observed == predicted
        tested_patterns += 1
    return tested_patterns, checked_equalities


def audit_translated_coins():
    # The mask records whether some Merlin response accepts this coin. Thus
    # its entries may come from different responses, even inside one batch.
    count = 0
    for mask in range(1 << 4):
        accepts = [(mask >> i) & 1 for i in range(4)]
        for sample in product(range(4), repeat=3):
            scores = [sum(accepts[x ^ shift] for x in sample) for shift in range(4)]
            assert sum(scores) == len(sample) * sum(accepts)
            assert 4 * max(scores) >= len(sample) * sum(accepts)
            count += 1
    return count


if __name__ == '__main__':
    patterns, equalities = audit()
    print(f'{patterns} full label distributions and {equalities} hard-negative counts matched')
    print(f'{audit_translated_coins()} sampled public-coin games preserved the shift identity')
