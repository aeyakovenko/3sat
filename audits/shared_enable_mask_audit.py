"""Verify the signed and modular isolation calculations on a unique seven-clause file."""
from itertools import product


def live_occurrences():
    # At 111 the clause forbidding pattern k is true precisely at its zero coordinates.
    clauses = []
    offset = 0
    for forbidden in range(7):
        live = (7 ^ forbidden).bit_count()
        clauses.append(((1 << live) - 1) << offset)
        offset += live
    return clauses, offset


def lattice_transform(table, bits, inverse):
    result = table[:]
    for k in range(bits):
        bit = 1 << k
        for mask in range(len(result)):
            if mask & bit:
                value = result[mask ^ bit]
                result[mask] += -value if inverse else value
    return result


def audit():
    clauses, bits = live_occurrences()
    is_sat = [int(all(mask & c for c in clauses)) for mask in range(1 << bits)]
    mu = lattice_transform(is_sat, bits, inverse=True)
    assert set(mu) == {-1, 0, 1}
    assert [mu.count(1), mu.count(-1)] == [95, 94]
    assert lattice_transform(mu, bits, inverse=False) == is_sat

    # Ordinary shared witnesses are minimal true masks.
    minima = [int(bool(sat) and all((mask & c).bit_count() == 1 for c in clauses))
              for mask, sat in enumerate(is_sat)]
    ordinary = lattice_transform(minima, bits, inverse=False)
    assert ordinary[-1] == 24
    for p in (2, 3, 5, 7):
        physical = lattice_transform([value % p for value in mu], bits, inverse=False)
        for mask, count in enumerate(physical):
            h = 1
            for c in clauses:
                h *= (1 << (mask & c).bit_count()) - 1
            assert count == (1 + p * ((h - 1) // 2) if h else 0)
            assert count % p == is_sat[mask]
        assert physical[-1] == 1 + 94 * p

    # Directly maximize the first-enabled-or-unsigned witness count in each
    # clause on all local masks and multiply over independently chosen masks.
    best = [None] * (bits + 1)
    for signed in range(1 << bits):
        worst = 1
        for c in clauses:
            live_positions = [i for i in range(bits) if c & (1 << i)]
            local_maximum = 0
            for flags in product((0, 1), repeat=len(live_positions)):
                enabled = sum(flag << i for flag, i in zip(flags, live_positions))
                count = 1 if enabled & signed else enabled.bit_count()
                local_maximum = max(local_maximum, count)
            worst *= local_maximum
        h = signed.bit_count()
        best[h] = worst if best[h] is None else min(best[h], worst)
    assert best[:6] == [24, 12, 6, 3, 2, 1]
    print(f"{len(is_sat)} live masks, {sum(is_sat)} satisfiable, {sum(minima)} minimal.")
    print("Mobius coefficients: 95 positive, 94 negative; modulo-two minimum: 189.")
    print(f"Best worst-case ambiguity with 0 through 5 signed enables: {best[:6]}.")


if __name__ == "__main__":
    audit()
