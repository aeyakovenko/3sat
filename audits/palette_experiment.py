"""Small finite checks for the interval excess and adjacent-swap estimates."""

from itertools import permutations


def subsets(mask):
    part = mask
    while True:
        yield part
        if part == 0:
            break
        part = (part - 1) & mask


def check_intervals(labels, m):
    full = (1 << m) - 1
    excess = {}
    for top in subsets(full):
        for bottom in subsets(top):
            free = top ^ bottom
            palette = {labels[bottom | delta] for delta in subsets(free)}
            excess[bottom, top] = len(palette) - free.bit_count() - 1
            assert excess[bottom, top] >= 0
    for (bottom, top), outer in excess.items():
        for delta in subsets(top ^ bottom):
            middle = bottom | delta
            assert outer >= excess[bottom, middle] + excess[middle, top]


def active_positions(labels, order):
    active = []
    base = 0
    for i, (left, right) in enumerate(zip(order, order[1:])):
        if labels[base | (1 << left)] != labels[base | (1 << right)]:
            active.append(i)
        base |= 1 << left
    return active


def main():
    m = 6
    labels = [m + 1 - x.bit_count() - (x & 1) for x in range(1 << m)]
    check_intervals(labels, m)
    maximum = 0
    for order in permutations(range(m)):
        changed = active_positions(labels, order)
        assert len(changed) <= 2
        if len(changed) == 2:
            assert changed[1] == changed[0] + 1
        maximum = max(maximum, len(changed))
    assert maximum == 2
    for rank in range(1, m):
        assert len({v for x, v in enumerate(labels) if x.bit_count() == rank}) == 2

    m = 4
    middle = [x for x in range(1 << m) if x.bit_count() == 2]
    for split in range(1 << len(middle)):
        high = {x for i, x in enumerate(middle) if split & (1 << i)}
        labels = [5 - x.bit_count() - int(x.bit_count() > 2 or x in high)
                  for x in range(1 << m)]
        check_intervals(labels, m)
    print("720 chains checked at m=6, maximum 2 active swaps; "
          "all intervals checked for 64 middle-layer splits at m=4.")


if __name__ == "__main__":
    main()
