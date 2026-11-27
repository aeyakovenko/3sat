"""Exhaust small bundle relations and the offset convention for transpose equality."""

from itertools import product


def check_filters(bundles, prime):
    labelings = list(product(range(2), repeat=bundles))
    masks = list(product(range(2), repeat=2 * bundles))
    kept = [
        sum(
            1 << j
            for j, labeling in enumerate(labelings)
            if all(mask[2 * e + value] for e, value in enumerate(labeling))
        )
        for mask in masks
    ]
    floor = len(masks) // (2**bundles)
    minimum = len(masks)
    for relation in range(1, 1 << len(labelings)):
        survivors = sum((relation & labels).bit_count() % prime != 0 for labels in kept)
        assert survivors >= floor
        minimum = min(minimum, survivors)
    assert minimum == floor  # A single compatible labeling attains it.
    return (1 << len(labelings)) - 1


def check_offsets():
    # Exhaust all pairs at t=2, including both verdicts.
    h = 1
    t = 1 << h
    arrays = list(product(range(2), repeat=t * t))
    for a, b in product(arrays, repeat=2):
        payload = a + b
        unmatched = any(
            payload[(i << h) | j] != payload[(1 << (2 * h)) | (j << h) | i]
            for i, j in product(range(t), repeat=2)
        )
        assert unmatched == (tuple(b) != tuple(a[i * t + j] for j in range(t) for i in range(t)))
    return len(arrays) ** 2


if __name__ == "__main__":
    for e in range(4):
        checked = [check_filters(e, p) for p in (2, 3, 5)]
        print(f"{e} bundles: {checked[0]} nonempty relations per field, tight fraction 1/{2**e}")
    print(f"Transpose offsets agree on all {check_offsets()} ordered array pairs at side 2.")
