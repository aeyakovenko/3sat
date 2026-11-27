"""Finite checks for the local list restriction and witness residue tensors."""

from itertools import permutations, product
from math import comb, prod


def signed_filters():
    count = 0
    for p in (2, 3, 5, 7):
        for q in (p, p**2, p**3):
            for m in range(3 * q + 2):
                # Coefficients from the exact integer binomial recurrence.
                coeff = 1
                total = 0
                for r in range(min(q, m + 1)):
                    total += coeff if r % 2 == 0 else -coeff
                    coeff = coeff * (m - r) // (r + 1)
                assert total % p == int(m % q == 0)
                count += 1
    return count


def tuple_encodings():
    checks = 0
    alphabet = range(4)
    q = 4
    slots = q - 1
    for mask in range(1 << len(alphabet)):
        accepted = {w for w in alphabet if mask & (1 << w)}
        counts = [0] * q
        for active in product((False, True), repeat=slots):
            if any(b and not a for a, b in zip(active, active[1:])):
                continue
            r = sum(active)
            for words in product(alphabet, repeat=slots):
                if any(w != 0 for w in words[r:]):
                    continue
                if any(w not in accepted for w in words[:r]):
                    continue
                if any(a >= b for a, b in zip(words[:r], words[1:r])):
                    continue
                counts[r] += 1
        assert counts == [comb(len(accepted), r) for r in range(q)]
        checks += 1
    return checks


def binomial_basis(s, r, prime):
    return prod(comb(v, k) for v, k in zip(s, r)) % prime


def joint_lookups():
    checked = 0
    for prime, moduli in ((2, (2, 4)), (3, (3, 3)), (5, (5,))):
        ranks = list(product(*(range(q) for q in moduli)))
        basis = [[binomial_basis(s, r, prime) for r in ranks] for s in ranks]
        for m in product(*(range(2 * q + 2) for q in moduli)):
            residue = tuple(v % q for v, q in zip(m, moduli))
            row = [binomial_basis(m, r, prime) for r in ranks]
            assert row == basis[ranks.index(residue)]
        for truth in product((0, 1), repeat=len(ranks)):
            coefficients = []
            for value, row in zip(truth, basis):
                partial = sum(a * b for a, b in zip(coefficients, row))
                coefficients.append((value - partial) % prime)
            assert all(sum(a * b for a, b in zip(coefficients, row)) % prime == v
                       for row, v in zip(basis, truth))
            checked += 1
    return checked


def local_slices():
    # N=4, M=2. Visit every ordered distinct seed and both disjoint groups and all replacements.
    seeds = evaluations = 0
    for seed in permutations(range(16), 4):
        groups = {}
        for block in range(4):
            occupied = [i for i, v in enumerate(seed) if v // 4 == block]
            if len(occupied) <= 2 and len(groups) < 2:
                groups[block] = occupied
        reserved = {i for group in groups.values() for i in group}
        remaining = iter(i for i in range(4) if i not in reserved)
        for slots in groups.values():
            slots.extend(next(remaining) for _ in range(2 - len(slots)))
        assert sorted(i for group in groups.values() for i in group) == list(range(4))
        for block, slots in groups.items():
            for replacement in product(range(4), repeat=2):
                full = list(seed)
                for i, v in zip(slots, replacement):
                    full[i] = 4 * block + v
                assert (len(set(full)) == 4) == (replacement[0] != replacement[1])
                assert sum(a != b for a, b in zip(full, seed)) <= 2
                evaluations += 1
        seeds += 1
    return seeds, evaluations


if __name__ == "__main__":
    print(f"{signed_filters()} prime-power signed filters")
    print(f"{tuple_encodings()} accepting sets with canonical padded witness tuples")
    print(f"{joint_lookups()} Boolean readouts in mixed binomial bases")
    seeds, slices = local_slices()
    print(f"{seeds} distinct seeds, {slices} fixed-background slice evaluations")
