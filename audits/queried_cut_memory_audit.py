"""Check sparse interpolation, actual differing reads, and the diagonal row bound."""

from itertools import combinations, product


def multiply(a, b):
    """Multiply in F_2[z]/(z^4 + z + 1)."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 16:
            a ^= 0b10011
    return result


def interpolate(keys, stored):
    nodes = sorted(keys)
    weights = {}
    for node in nodes:
        if not stored.get(node, 0):
            continue
        denom = 1
        for other in nodes:
            if other != node:
                denom = multiply(denom, node ^ other)
        inv = next(i for i in range(1, 16) if multiply(denom, i) == 1)
        weights[node] = multiply(stored[node], inv)

    def evaluate(address):
        result = 0
        for node, weight in weights.items():
            value = weight
            for other in nodes:
                if node != other:
                    value = multiply(value, address ^ other)
            result ^= value
        return result

    return evaluate


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pos = row.bit_length() - 1
            if pos not in pivots:
                pivots[pos] = row
                break
            row ^= pivots[pos]
    return len(pivots)


def row_bound(rows):
    n = len(rows)
    assert all(row >> i & 1 for i, row in enumerate(rows))
    dim = rank(rows)
    for size in range(1, n + 1):
        assert sum(row.bit_count() <= size for row in rows) <= dim * size


def suffix(read, key, tag, delay, cutoff):
    # One inherited word is addressed by the query. The second load has a
    # suffix writer; it must see the new word, including when its value is zero.
    inherited = read(key)
    overlay = {12 + tag: inherited}
    value = overlay[12 + tag]
    miss = value == 0
    return (None if delay + int(miss) > cutoff else miss), {key: inherited}


def decide(left, right, equal):
    if left is True or right is True:
        return False
    if left is False:
        return equal[1]
    return equal[0]


def check_interpolation():
    false_positives = 0
    correction_only = 0
    correct_timeouts = 0
    for extra, cutoff in product(combinations(range(8), 2), range(3)):
        matrix = []
        for x in range(16):
            halves_x = (x & 3, x >> 2)
            stored = {halves_x[0]: 1, 4 + halves_x[1]: 1}
            bank = set(extra) | stored.keys()
            guessed = interpolate(bank, stored)
            def actual(address, memory=stored):
                return memory.get(address, 0)
            assert all(guessed(a) == actual(a) for a in bank)
            row = 0
            for y in range(16):
                halves_y = (y & 3, y >> 2)
                equal = tuple(a == b for a, b in zip(halves_x, halves_y))
                keys = (halves_y[0], 4 + halves_y[1])
                delays = (halves_y[1] & 1, halves_y[0] & 1)
                truth = [suffix(actual, key, t, delays[t], cutoff)
                         for t, key in enumerate(keys)]
                sim = [suffix(guessed, key, t, delays[t], cutoff)
                       for t, key in enumerate(keys)]
                prediction = decide(sim[0][0], sim[1][0], equal)
                if not prediction:
                    assert x != y
                    continue
                row |= 1 << y
                if x == y:
                    continue
                assert equal[0] != equal[1]
                both_slow = all(report is None for report, _ in truth)
                discrepancies = {addr for (_, reads), (_, hints) in zip(truth, sim)
                                 for addr in reads if reads[addr] != hints[addr]}
                assert both_slow or discrepancies
                assert not (discrepancies & bank)
                assert all(actual(a) == 0 and guessed(a) != 0 for a in discrepancies)
                false_positives += 1
                correction_only += not both_slow
                correct_timeouts += both_slow and not discrepancies
            matrix.append(row)
        row_bound(matrix)
    assert correction_only > 0 and correct_timeouts > 0
    return false_positives, correction_only, correct_timeouts


def check_rank():
    n = 4
    slots = [(i, j) for i in range(n) for j in range(n) if i != j]
    for mask in range(1 << len(slots)):
        rows = [1 << i for i in range(n)]
        for k, (i, j) in enumerate(slots):
            if mask >> k & 1:
                rows[i] |= 1 << j
        row_bound(rows)
    return 1 << len(slots)


def check_nearby_words():
    # A length-seven Hamming parity check: distinct nonzero columns ensure
    # detection of every weight-one and weight-two error. A weight-three error
    # can have zero syndrome and therefore must pass to the exact fallback.
    columns = tuple(range(1, 8))

    def syndrome(payload):
        value = 0
        for j, column in enumerate(columns):
            if payload >> j & 1:
                value ^= column
        return value

    certified = 0
    fallback = 0
    for x, y in product(range(128), repeat=2):
        old = syndrome(x)
        query = syndrome(y)
        # A native scanner may store the pieces in separate one-hot banks.
        banks = {(0, old & 3), (1, old >> 2)}
        equal_pieces = ((0, query & 3) in banks, (1, query >> 2) in banks)
        if any(not equal for equal in equal_pieces):
            assert x != y
            certified += 1 <= (x ^ y).bit_count() <= 2
        else:
            assert x == y or (x ^ y).bit_count() >= 3
            fallback += x != y
    assert certified == 128 * (7 + 21)
    assert fallback
    return certified, fallback


if __name__ == "__main__":
    count, corrections, slow = check_interpolation()
    print(f"{count} off-diagonal positives on sparse memories, including "
          f"{corrections} requiring a differing old read and {slow} with two timeouts "
          f"and exact reads; {check_rank()} unit-diagonal matrices exhausted.")
    certified, fallback = check_nearby_words()
    print(f"{certified} nearby errors detected by packed syndrome pieces; "
          f"{fallback} nonzero distant errors correctly require fallback.")
