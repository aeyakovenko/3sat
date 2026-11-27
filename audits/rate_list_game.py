"""Solve the finite delayed forbidden-list game for small lookahead horizons."""

def extend_one_bit(mask):
    """Turn each live suffix into the adjacent pair of its two children."""
    children = 0
    while mask:
        bit = mask & -mask
        children |= 3 << (2 * (bit.bit_length() - 1))
        mask -= bit
    return children


def chooser_wins(horizon, budget):
    leaves = 1 << (horizon - 1)
    full = (1 << leaves) - 1
    children = []
    for mask in range(full + 1):
        extended = extend_one_bit(mask)
        children.append((extended & full, extended >> leaves))

    # A state lists viable suffixes of length horizon - 1. Empty viability
    # already guarantees an eventual loss even if no further word is forbidden.
    losing = bytearray(full + 1)
    losing[0] = 1
    while True:
        # Distance to the losing family by removing live suffixes.
        cost = bytearray(full + 1)
        for mask in range(1, full + 1):
            if losing[mask]:
                continue
            candidates = mask
            best = leaves
            while candidates:
                bit = candidates & -candidates
                best = min(best, 1 + cost[mask ^ bit])
                candidates -= bit
            cost[mask] = best

        added = [
            mask
            for mask, (left, right) in enumerate(children)
            if not losing[mask] and cost[left] + cost[right] <= budget
        ]
        if not added:
            return True
        if full in added:
            return False
        for mask in added:
            losing[mask] = 1


if __name__ == "__main__":
    for horizon in range(1, 6):
        limit = 0
        while chooser_wins(horizon, limit + 1):
            limit += 1
        print(f"lookahead {horizon}: maximum winning list size {limit}")
