"""Small complete tests of block reconstruction, agreement, and covering shifts."""

from itertools import combinations, product

from unread_word_avoidance_audit import output as moments


def agreement(a, b):
    return len(a) - sum(v != w for v, w in zip(a, b))


def table_counts():
    words = list(product(range(2), repeat=3))
    cases = 0
    for population in combinations(words, 2):
        for blocks in product(words, repeat=3):
            can_copy = [word in population for word in blocks]
            if all(can_copy):
                tags = [population.index(word) for word in blocks]
                assert tuple(population[i] for i in tags) == blocks
            best = [max(agreement(word, entry) for entry in population) for word in blocks]
            for threshold in (2, 3):
                close = [score >= threshold for score in best]
                count = sum(
                    score if used else max(sum(word), len(word) - sum(word))
                    for word, score, used in zip(blocks, best, close)
                )
                assert 2 * count >= 3 * len(blocks) + sum(close) * (2 * threshold - 3)
            cases += 1
    return cases


def coverage_check():
    labels = tuple(range(8))
    cases = 0
    for size in range(9):
        for accepted in combinations(labels, size):
            # Three sampled shifts. Check both sufficient bounds for the cube.
            shifts_needed = 3
            density_complement = 8 - size
            enough = 8 * density_complement**shifts_needed < 8**shifts_needed
            too_sparse = shifts_needed * size < 8
            if enough or too_sparse:
                covers = any(
                    all(any((z ^ shift) in accepted for shift in shifts) for z in labels)
                    for shifts in combinations(labels, shifts_needed)
                )
                assert covers == enough
                cases += 1
    return cases


def shared_masks_check():
    """One global set of masks is reused by all three target blocks."""
    length = 3
    words = list(product(range(2), repeat=length))
    checked = 0
    for mask_count in (1, 2):
        lists = list(product(words, repeat=mask_count))
        expected = {}
        for word in words:
            expected[word] = [
                max(abs(2 * agreement(word, mask) - length) for mask in masks)
                for masks in lists
            ]
        for blocks in product(words, repeat=3):
            gains = [sum(scores) for scores in zip(*(expected[b] for b in blocks))]
            separate_sum = sum(sum(expected[b]) for b in blocks)
            assert sum(gains) == separate_sum
            assert max(gains) * len(lists) >= separate_sum
            checked += 1
    return checked


def unread_masks_check():
    """One external seed bit plus t unread field words parametrizes the cover."""
    indices = list(product(range(4), repeat=3))
    tests = 0
    for t, expected_radius in enumerate((2, 1, 0)):
        for unread in combinations(range(3), t):
            images = {}
            for index in indices:
                fixed = tuple(value for i, value in enumerate(index) if i not in unread)
                image = images.setdefault(fixed, set())
                hidden = moments(index, 2 * t)
                for bit in range(2):
                    if t == 0:
                        value = 15 * bit
                    elif t == 1:
                        data = (hidden << 1) | bit
                        value = (data << 1) | (data.bit_count() % 2)
                    else:
                        value = hidden
                    image.add(value)
            for image in images.values():
                radius = max(min((candidate ^ pred).bit_count() for pred in image) for candidate in range(16))
                assert radius == expected_radius
                tests += 1
    return tests


if __name__ == "__main__":
    print(f"{table_counts()} complete three-block tables and ranges checked.")
    print(f"{coverage_check()} Boolean sample predicates in the two promised density tails checked.")
    print(f"{shared_masks_check()} shared-mask block targets and mask counts checked.")
    print(f"{unread_masks_check()} actual GF(4) read restrictions and worst target radii checked.")
