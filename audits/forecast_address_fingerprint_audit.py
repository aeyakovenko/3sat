"""Exhaust three-bit memory claims with two shared simplex-code coordinates."""

from itertools import combinations, product


# The seven nonzero parity masks are the coordinates of the binary simplex code.
COORDINATES = tuple(combinations(range(1, 8), 2))


def fingerprint(address, masks):
    return tuple((address & mask).bit_count() % 2 for mask in masks)


def consistent(records):
    memory = {}
    for active, address, bit in records:
        if active and memory.setdefault(address, bit) != bit:
            return False
    return True


def adjacent_checks(ordered):
    for left, right in zip(ordered, ordered[1:]):
        a, x, u = left
        b, y, v = right
        if a and b and x == y and u != v:
            return False
    return True


def shared_trial(records, masks):
    hashed = [(a, fingerprint(x, masks), u) for a, x, u in records]
    return adjacent_checks(sorted(hashed, key=lambda row: (not row[0], row[1])))


def main():
    counts = {False: 0, True: 0}
    claims = [(True, x, bit) for x in range(8) for bit in (0, 1)]
    for records in product(claims, repeat=3):
        result = any(shared_trial(records, pair) for pair in COORDINATES)
        assert result == consistent(records), records
        counts[result] += 1
    assert counts == {False: 720, True: 3376}

    # An inactive filler with the same fingerprint can separate opposite bits
    # when the activity class is omitted from the sort key.
    padded = [(True, 1, 0), (False, 1, 0), (True, 1, 1)]
    assert not consistent(padded)
    for pair in COORDINATES:
        hashed = [(a, fingerprint(x, pair), u) for a, x, u in padded]
        assert adjacent_checks(sorted(hashed, key=lambda row: row[1]))
        assert not shared_trial(padded, pair)

    # Independent choices map the same address 1 to (1,0) and (0,0).
    opposite = [(True, 1, 0), (True, 1, 1)]
    independent = [(True, fingerprint(1, (1, 2)), 0),
                   (True, fingerprint(1, (2, 4)), 1)]
    assert not any(shared_trial(opposite, pair) for pair in COORDINATES)
    assert adjacent_checks(sorted(independent, key=lambda row: row[1]))

    print('4096 triples passed (3376 consistent, 720 inconsistent); '
          'inactive filler and independent-selector counterexamples checked')


if __name__ == '__main__':
    main()
