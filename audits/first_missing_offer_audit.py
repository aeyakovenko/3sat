"""Exhaust finite offer relations for the two common-instance constructions."""

from itertools import permutations, product


def first_deficient_prefix(rows, pool_size):
    """Use matchings, independent of the Hall-witness test."""
    for h in range(len(rows)):
        if not any(
            all(rows[i] & (1 << c) for i, c in enumerate(codes))
            for codes in permutations(range(pool_size), h + 1)
        ):
            return h
    raise AssertionError("more rows than codes")


def hall_witness(rows):
    for subset in range(1, 1 << len(rows)):
        neighbors = 0
        for h, row in enumerate(rows):
            if subset & (1 << h):
                neighbors |= row
        if neighbors.bit_count() < subset.bit_count():
            return subset
    return None


def check_chains(pool_size):
    boundaries = [0] * (pool_size + 1)
    for rows in product(range(1 << pool_size), repeat=pool_size + 1):
        first = first_deficient_prefix(rows, pool_size)
        boundaries[first] += 1
        assert hall_witness(rows[:first]) is None
        assert hall_witness(rows[: first + 1]) is not None
        unsound = 0
        for row in rows[:first]:
            unsound |= row
        assert rows[first] & ~unsound == 0
    assert all(boundaries)
    print(f"{pool_size} codes, {sum(boundaries)} offer graphs, boundary histogram {boundaries}")


def check_signed(seed_count, pool_size):
    """Each two-bit cell gives the pins at which a code offers the pin sign."""
    seed_mask = (1 << (2 * seed_count)) - 1
    tables = 0
    worst = 0
    for codes in product(range(seed_mask + 1), repeat=pool_size):
        flipped = 0
        for offers in codes:
            if offers:
                first_bit = (offers & -offers).bit_length() - 1
                flipped |= offers & (3 << (2 * (first_bit // 2)))
        bad_count = sum(bool(flipped & (3 << (2 * r))) for r in range(seed_count))
        assert bad_count <= pool_size
        for offers in codes:
            if offers & flipped == 0:
                assert offers == 0
        worst = max(worst, bad_count)
        tables += 1
    assert worst == min(seed_count, pool_size)
    print(f"{seed_count} seeds, {pool_size} codes, {tables} signed tables, maximum {worst} bad seeds")


if __name__ == "__main__":
    for count in range(1, 4):
        check_chains(count)
    check_signed(3, 2)
    check_signed(2, 3)
