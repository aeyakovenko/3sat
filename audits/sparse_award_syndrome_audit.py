"""Exact counts for sparse alternatives, independent directions and parity checks."""

from itertools import combinations


def xor_basis(words):
    rows = {}
    for word in words:
        while word:
            pivot = word.bit_length() - 1
            if pivot not in rows:
                rows[pivot] = word
                break
            word ^= rows[pivot]
    return tuple(rows.values())


def parity(word):
    return word.bit_count() % 2


def field_multiply(a, b, modulus):
    result = 0
    order = 1 << (modulus.bit_length() - 1)
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & order:
            a ^= modulus
    return result


def moments(word, width, count, modulus):
    degree = modulus.bit_length() - 1
    powers = [1] * width
    result = 0
    for e in range(count):
        symbol = 0
        for pos in range(width):
            if word >> pos & 1:
                symbol ^= powers[pos]
            powers[pos] = field_multiply(powers[pos], pos + 1, modulus)
        result |= symbol << (e * degree)
    return result


def audit_syndromes():
    counts = 0
    for width in range(1, 11):
        modulus = (0b11 if width == 1 else 0b111 if width <= 3
                   else 0b1011 if width <= 7 else 0b10011)
        for cap in range(1, min(4, width) + 1):
            sparse = [word for word in range(1 << width) if word.bit_count() <= cap]
            signatures = {moments(word, width, 2 * cap, modulus) for word in sparse}
            assert len(signatures) == len(sparse)
            counts += len(sparse)
    return counts


def audit_alternatives():
    lists = directions = 0
    for width in range(1, 4):
        points = range(1 << width)
        for mask in range(1 << (1 << width)):
            candidates = [y for y in points if mask >> y & 1]
            for actual in candidates:
                for lag in range(1, width + 1):
                    selected = []
                    for i in range(lag - 1, width, lag):
                        prefix = (1 << (i + 1 - lag)) - 1
                        other = next((y for y in candidates if (y ^ actual) & prefix == 0
                                      and (y ^ actual) >> i & 1), None)
                        if other is not None:
                            selected.append(other ^ actual)
                    assert len(xor_basis(selected)) == len(selected)
                    assert len(candidates) >= 1 + len(selected)
                    for word in selected:
                        assert word.bit_count() <= 2 * max(y.bit_count() for y in candidates)
                    lists += 1
                    directions += len(selected)
    return lists, directions


def audit_missing_directions():
    cases = choices = 0
    width = 7
    modulus = 0b1011
    measurements = 6
    sparse = [v for v in range(1 << width) if v.bit_count() <= 1]
    synd = {v: moments(v, width, 2, modulus) for v in sparse}
    seed_checks = (3, 5, 9, 17, 33, 42, 56)
    for count in range(len(seed_checks) + 1):
        for checks in combinations(seed_checks, count):
            rank = len(xor_basis(checks))
            for actual in sparse:
                allowed = [v for v in sparse if all(parity(q & (synd[v] ^ synd[actual])) == 0
                                                    for q in checks)]
                assert len(allowed) <= 1 << (measurements - rank)
                augmented = [q * 2 + parity(q & synd[actual]) for q in checks]
                assert rank == len(xor_basis(augmented))
                cases += 1
                choices += len(allowed)
    return cases, choices


def audit_zone_shrinkage():
    width = 3
    zones = [range(0, 3), range(6, 9)]
    population = [v for v in range(1 << 9) if v.bit_count() <= 2]
    checks = survivors = empty = 0
    for coeffs in range(1 << 9):
        for bit in (0, 1):
            initial = [v for v in population if parity(v & coeffs) == bit]
            candidates = initial
            chosen_mask = 0
            for index, zone in enumerate(zones, 1):
                next_bit = min(zone, key=lambda pos: sum(v >> pos & 1 for v in candidates))
                chosen_mask |= 1 << next_bit
                candidates = [v for v in candidates if v >> next_bit & 1]
                assert width**index * len(candidates) <= 2**index * len(initial)
            assert candidates == [v for v in initial if v & chosen_mask == chosen_mask]
            checks += 1
            survivors += len(candidates)
            empty += not candidates
    return checks, survivors, empty


if __name__ == '__main__':
    print(f"{audit_syndromes()} sparse words had collision-free finite-field syndromes")
    lists, directions = audit_alternatives()
    print(f"{lists} list/actual/lag combinations yielded {directions} independent differences")
    cases, choices = audit_missing_directions()
    print(f"{cases} partial parity sketches bounded the number of candidates ({choices} total)")
    zones, survivors, empty = audit_zone_shrinkage()
    print(f"{zones} sparse zone filters retained {survivors} joint witnesses; {empty} exhausted")
