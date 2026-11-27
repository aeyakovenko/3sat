"""Finite optimal adaptive probes, and a constructive strategy for omitting words."""

from functools import cache
from itertools import product
from math import comb
from random import Random


def parity(value):
    return value.bit_count() % 2


def coordinate(value, index, width):
    return (value >> (index * width)) & ((1 << width) - 1)


def audit_fibers(words, width, labelings):
    """Optimize the number of sound early outputs independently for each label and query."""
    alphabet = 1 << width
    universe = alphabet**words
    full = (1 << universe) - 1
    coordinate_classes = [
        [
            sum(1 << x for x in range(universe) if coordinate(x, i, width) == v)
            for v in range(alphabet)
        ]
        for i in range(words)
    ]
    per_labeling = [[0] * words for _ in labelings]
    for query in range(universe):
        odd = sum(1 << x for x in range(universe) if parity(x & query))

        @cache
        def early_outputs(fiber, remaining):
            if not (fiber & odd) or not (fiber & (full ^ odd)):
                return fiber.bit_count()
            if remaining == 0:
                return 0
            return max(
                sum(early_outputs(fiber & mask, remaining - 1) for mask in classes)
                for classes in coordinate_classes
            )

        for counts, fibers in zip(per_labeling, labelings):
            for d in range(1, words + 1):
                counts[d - 1] += sum(early_outputs(fiber, words - d) for fiber in fibers)

    for counts, fibers in zip(per_labeling, labelings):
        for d, mass in enumerate(counts, 1):
            assert mass * alphabet**d <= universe**2 * comb(words, d) * len(fibers)
    return len(labelings) * words


def check_constructive_strategy(words, width, sketch_bits):
    alphabet = 1 << width
    universe = alphabet**words
    labels = 1 << sketch_bits
    saved_masks = range(labels)
    omission_counts = [0] * (words + 1)
    for query in range(universe):
        coeff = [coordinate(query, i, width) for i in range(words)]
        chosen = max(saved_masks, key=coeff.count)
        omitted = coeff.count(chosen)
        for d in range(1, omitted + 1):
            omission_counts[d] += 1
        adjusted = sum((v ^ chosen) << (i * width) for i, v in enumerate(coeff))
        for x in range(universe):
            # Form the sketch directly from the data. Only the changed coefficients
            # access x at query time, since the other coefficients vanish.
            word_xor = 0
            for i in range(words):
                word_xor ^= coordinate(x, i, width)
            sketch = word_xor & (labels - 1)
            answer = parity(sketch & chosen) ^ parity(x & adjusted)
            assert answer == parity(x & query)
    for d in range(1, words + 1):
        lower = comb(words, d) * labels * (alphabet - labels)**(words - d)
        assert lower <= omission_counts[d]
        assert omission_counts[d] <= comb(words, d) * labels * alphabet**(words - d)
    return universe**2


def audit_broadcast_history():
    # The first two coordinates receive the same query coefficient. Condition
    # on the preceding query but keep its answer as a function of the raw data.
    width = 2
    alphabet = 1 << width
    words = 3
    universe = alphabet**words
    masks = [a | (a << width) | (b << (2 * width))
             for a, b in product(range(alphabet), repeat=2)]
    checked = 0
    for previous in masks:
        for omitted in ((0,), (1,), (2,), (0, 2), (1, 2)):
            omitted_bits = sum((alphabet - 1) << (width * i) for i in omitted)
            fibers = {}
            for x in range(universe):
                old_answer = parity(x & previous)
                label = old_answer ^ ((x & 3) == 1)
                key = (x & ~omitted_bits, label)
                fibers.setdefault(key, []).append(x)
            possible = 0
            for query in masks:
                for fiber in fibers.values():
                    if len({parity(x & query) for x in fiber}) == 1:
                        possible += len(fiber)
            # One label bit, even though it depends on the previous answer.
            assert possible * alphabet**len(omitted) <= 2 * len(masks) * universe
            checked += 1
    return checked


def main():
    # Every partition of the 3-bit input into at most two labeled classes.
    full = (1 << 8) - 1
    labelings = [tuple(f for f in (f0, full ^ f0) if f) for f0 in range(1 << 8)]
    inequalities = audit_fibers(3, 1, labelings)

    # Nonlinear, uneven, and sometimes empty fibers using full two-bit words.
    rng = Random(1729)
    labelings = []
    for size in (1, 2, 3, 4):
        for _ in range(32):
            fibers = [0] * size
            for x in range(16):
                fibers[rng.randrange(size)] |= 1 << x
            labelings.append(tuple(f for f in fibers if f))
    inequalities += audit_fibers(2, 2, labelings)
    pairs = sum(
        check_constructive_strategy(words, width, s)
        for words, width in ((3, 1), (2, 2), (3, 2), (2, 3))
        for s in range(width + 1)
    )
    broadcasts = audit_broadcast_history()
    print(f"{inequalities} optimal adaptive omission inequalities; "
          f"{broadcasts} broadcast/history bounds; "
          f"{pairs} full input/query pairs in the matching construction.")


if __name__ == "__main__":
    main()
