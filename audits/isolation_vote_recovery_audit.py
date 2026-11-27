"""Finite semantic audit of isolating-a-proof-with-negative-sat-votes.md.

Inner comparison keys model explicitly materializable files. Only the parity
keys enter the issued-query list. NO tables are deterministic, possibly wrong.
This checks projected relations and vote recovery, not a DIMACS or RAM compiler.
"""
from collections import Counter
from itertools import product
from random import Random


def field_masks(d, m):
    q = 1 << (8 * m * d - 1).bit_length()
    # x^5+x^2+1, x^6+x+1, x^7+x+1, x^8+x^4+x^3+x+1
    modulus = {32: 0x25, 64: 0x43, 128: 0x83, 256: 0x11B}[q]

    def multiply(a, b):
        total = 0
        while b:
            if b & 1:
                total ^= a
            b >>= 1
            a <<= 1
            if a & q:
                a ^= modulus
        return total

    masks = Counter()
    for alpha in range(q):
        powers = [1]
        for _ in range(d - 1):
            powers.append(multiply(powers[-1], alpha))
        for multiplier in range(q):
            mask = sum(((multiply(multiplier, value) & 1) << pos)
                       for pos, value in enumerate(powers))
            masks[mask] += 1
    for v in range(1, 1 << d):
        bias_count = sum(n * (-1 if (a & v).bit_count() % 2 else 1)
                         for a, n in masks.items())
        assert abs(bias_count) <= (d - 1) * q
    return masks


def inner(x):
    return ("comparison", x)


def outer(i, a, u):
    return ("issued-parity", i, a, u)


def parity(a, x):
    return (a & x).bit_count() % 2


def run(d, m, masks, passing, votes):
    """Exhaustive solution enumeration substitutes for binary Gaussian elimination."""
    assert passing
    universe = range(1 << d)
    voters = range(m)
    z = min(passing)
    projection = [{x for x in passing if votes.get(inner(x), 0) >> i & 1}
                  for i in voters]
    issued = tuple(outer(i, a, u) for i in voters for a in masks for u in (0, 1))
    truth = {inner(x): any(y < x for y in passing) for x in universe}
    truth.update({key: any(parity(key[2], x) == key[3] for x in projection[key[1]])
                  for key in issued})
    assert set(votes) <= set(truth)
    assert inner(z) not in issued and not truth[inner(z)]
    rows = {(i, j): [] for i in voters for j in voters}
    for key in issued:
        _, i, a, u = key
        for j in voters:
            if votes.get(key, 0) >> j & 1:
                rows[i, j].append((a, 1 - u))
    models = set()
    bad_rows = 0
    for equations in rows.values():
        candidates = [x for x in universe if all(parity(a, x) == u for a, u in equations)]
        bad_rows += not candidates
        if len(candidates) <= 2 * m:
            models.update(passing.intersection(candidates))

    honest = sum(1 << j for j in voters
                 if all(not sat or not (votes.get(key, 0) >> j & 1)
                        for key, sat in truth.items()))
    if models:
        return True, bad_rows, ("verified",), 0, 0

    branches = set()
    for h in range(1, 1 << m):
        if h & ~honest:
            continue
        covered_min = h & votes.get(inner(z), 0)
        if not covered_min:
            branches.add("implicit")
            continue
        for i in voters:
            if covered_min >> i & 1:
                assert projection[i] == {z}
                assert any(key[1] == i and not truth[key] and not h & votes.get(key, 0)
                           for key in issued)
        branches.add("issued")

    # Check the external receipt for every subportfolio, including dishonest ones.
    receipts = {}
    for i, projected in enumerate(projection):
        nonminimal = projected - {z}
        if nonminimal:
            receipts[i] = inner(min(nonminimal))
    removed_inner = len(receipts)
    isolated = [i for i in voters if i not in receipts and z in projection[i]]
    for i in isolated:
        for a in masks:
            key = outer(i, a, parity(a, z))
            for j in voters:
                if j not in receipts and votes.get(key, 0) >> j & 1:
                    receipts[j] = key
    survivors = sum(1 << j for j in voters if j not in receipts)
    remaining_isolators = [i for i in isolated if survivors >> i & 1]
    if remaining_isolators:
        i = remaining_isolators[0]
        miss = next(key for key in issued if key[1] == i
                    and not truth[key] and not survivors & votes.get(key, 0))
    else:
        miss = inner(z)
    assert not truth[miss] and not survivors & votes.get(miss, 0)
    for j, key in receipts.items():
        assert truth[key] and votes.get(key, 0) >> j & 1
    for subset in range(1 << m):
        assert any(truth[key] != (not (subset & votes.get(key, 0)))
                   for key in list(receipts.values()) + [miss])
    return False, bad_rows, tuple(sorted(branches)), removed_inner, len(receipts) - removed_inner


def main():
    d, m = 5, 3
    masks = field_masks(d, m)
    z = 13
    passing = {z, 18}

    # Every timely NO is sound. Three voters divide the false parity sides.
    split = {inner(z): 1}
    for a in masks:
        split[outer(0, a, 1 - parity(a, z))] = 1 << (a % m)
    assert run(d, m, masks, passing, split)[0]
    blank = run(d, m, masks, passing, {})
    assert not blank[0] and blank[2] == ("implicit",)

    # Voter 0 contaminates a comparison, voter 1 isolates, voter 2
    # contaminates the corresponding true side. Both removal phases matter.
    corrupt = {inner(18): 1, inner(z): 2, outer(1, 1, parity(1, z)): 4}
    found, _, branches, ni, no = run(d, m, masks, passing, corrupt)
    assert not found and branches == ("issued",) and (ni, no) == (1, 1)

    # Two contrary votes from the same voter give an inconsistent equation row.
    corrupt[outer(1, 1, 1 - parity(1, z))] = 4
    assert run(d, m, masks, passing, corrupt)[1] >= 1

    # Exhaust all nonempty tests on three bits. Try all four possible raw
    # comparator policies on passing strings (lex-min/other independently).
    d, m = 3, 1
    masks = field_masks(d, m)
    stats = Counter()
    rng = Random(17031)
    for support in range(1, 1 << (1 << d)):
        passing = {x for x in range(1 << d) if support >> x & 1}
        z = min(passing)
        for lo, hi in product((False, True), repeat=2):
            votes = {inner(x): 1 for x in passing if (lo if x == z else hi)}
            for a, u in product(masks, (0, 1)):
                if rng.randrange(7) == 0:
                    votes[outer(0, a, u)] = 1
            found, bad, _, _, _ = run(d, m, masks, passing, votes)
            stats["verified" if found else "miss"] += 1
            stats["inconsistent rows"] += bad
    print("Split coverage recovered a proof. Both missing-file alternatives passed.")
    print("Deliberate mixed case removed one inner and one outer wrong voter.")
    print(f"All 255 supports × 4 comparator policies passed: {dict(sorted(stats.items()))}")


if __name__ == "__main__":
    main()
