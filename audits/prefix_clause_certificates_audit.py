"""Check exact prefix witnesses, streaming bases, and inverse-permutation queries."""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from math import comb, factorial
from random import Random


def masks(n, size):
    return [sum(1 << i for i in items) for items in combinations(range(n), size)]


def false_at(row, assignment):
    negative, positive = row
    return assignment & negative == negative and not assignment & positive


def proposed_chain(n, k):
    seen = []
    for size in reversed(range(k + 1)):
        for negative in masks(n, size):
            available = [i for i in range(n) if not negative >> i & 1]
            positive = sum(1 << i for i in available[:k - size])
            row = negative, positive
            assert all(not false_at(old, negative) for old in seen)
            assert false_at(row, negative)
            for x in range(1 << n):
                if (x ^ negative) & (positive | negative) == 0:
                    assert false_at(row, x)
            seen.append(row)
    assert len(seen) == sum(comb(n, size) for size in range(k + 1))
    return len(seen)


def basis_test(n, k, random):
    monomials = [m for size in range(k + 1) for m in masks(n, size)]
    pos = {m: i for i, m in enumerate(monomials)}
    clauses = [(neg, scope ^ neg) for scope in masks(n, k) for neg in range(1 << n)
               if not neg & ~scope]
    random.shuffle(clauses)
    basis = {}
    all_solutions = set(range(1 << n))
    basis_solutions = all_solutions.copy()
    for neg, positive in clauses:
        all_solutions = {a for a in all_solutions if not false_at((neg, positive), a)}
        row = sum(1 << pos[neg | p] for p in range(1 << n) if not p & ~positive)
        while row:
            j = row.bit_length() - 1
            if j not in basis:
                basis[j] = row
                basis_solutions = {a for a in basis_solutions if not false_at((neg, positive), a)}
                break
            row ^= basis[j]
        assert all_solutions == basis_solutions
    assert len(basis) <= len(monomials)
    return len(clauses)


def permutations_recovered(n, k):
    triples = masks(n, k)
    bit_positions = {s: sum(1 << x for x in range(1 << n) if false_at((s, 0), x))
                     for s in triples}
    signatures = set()
    for ordering in permutations(triples):
        surviving = (1 << (1 << n)) - 1
        earliest = {}
        for time, item in enumerate(ordering, 1):
            surviving &= ~bit_positions[item]
            for key in triples:
                if not surviving & bit_positions[key]:
                    earliest.setdefault(key, time)
        for key, when in earliest.items():
            prefix_value = 0
            for bit in reversed(range((len(triples) - 1).bit_length())):
                midpoint = (prefix_value * 2 + 1) << bit
                has_appeared = when <= min(midpoint, len(triples))
                prefix_value = prefix_value * 2 + int(not has_appeared)
            assert prefix_value == when - 1
        assert tuple(sorted(earliest, key=earliest.get)) == ordering
        signatures.add(tuple(earliest[key] for key in triples))
    assert len(signatures) == factorial(len(triples))
    return len(signatures)


def exact_checksum_certificates():
    """Minimize reveal sets using every completion at small order."""
    rng = Random(18)
    checked = 0
    for n in range(2, 6):
        orders = list(permutations(range(n)))
        labels = (product(range(3), repeat=n) if n <= 4 else
                  [tuple(rng.randrange(3) for _ in range(n)) for _ in range(24)])
        for g in labels:
            largest_class = max(Counter(g).values())
            for threshold in range(n + 1):
                sums = [sum(g[i] for i in row[:threshold]) % 3 for row in orders]
                costs = [n] * len(orders)
                for mask in range(1 << n):
                    positions = [i for i in range(n) if mask >> i & 1]
                    views = [tuple(row[i] for i in positions) for row in orders]
                    possible = defaultdict(set)
                    for view, value in zip(views, sums):
                        possible[view].add(value)
                    for j, view in enumerate(views):
                        if len(possible[view]) == 1:
                            costs[j] = min(costs[j], len(positions))
                expected = min(threshold, n-threshold, n-largest_class)
                assert costs == [expected] * len(orders)
                checked += len(orders)
    return checked


def noisy_checksum_transcripts():
    """Exact hypergeometric bias conditioned on every feasible binary margin."""
    count = 0
    for m in (4, 8, 16, 32, 64):
        for q in range(m // 2):
            d = m // 2 - q
            pairs = d // 4
            for prefix_openings in range(q + 1):
                k = m // 2 - prefix_openings
                for ones_revealed in range(q + 1):
                    ones = m // 2 - ones_revealed
                    zeros = m - q - ones
                    signed = sum((-1)**i * comb(ones, i) * comb(zeros, k-i)
                                 for i in range(max(0, k-zeros), min(ones, k)+1))
                    total = comb(ones+zeros, k)
                    # Compare |bias| to (1-d/(2m))^pairs as an integer inequality.
                    assert abs(signed) * (2*m)**pairs <= total * (2*m-d)**pairs
                    n = ones + zeros
                    ell = min(k, n-k)
                    imbalance = abs(ones-zeros)
                    # Match keys of opposite colors. A designated smaller-side
                    # slot is unmatched or its partner must stay on that side.
                    not_split = imbalance*(n-1) + (n-imbalance)*(ell-1)
                    assert abs(signed)*n*(n-1) <= total*not_split
                    # Instead expose slot pairs on opposite sides.
                    rare_color = min(ones, zeros)
                    crossing_pairs = min(ell, rare_color // 4)
                    assert abs(signed)*(2*n)**crossing_pairs <= total*(2*n-rare_color)**crossing_pairs
                    count += 1
    return count


def last_row_advantage():
    checked = 0
    for m in (4, 8, 16):
        q = m // 2 - 1
        n = m - q
        for unobserved in combinations(range(m), n):
            walsh = [sum(1 - 2*((a & x).bit_count() & 1) for x in unobserved)
                     for a in range(1, m)]
            assert sum(w*w for w in walsh) == n*q
            assert max(w*w for w in walsh)*(m-1) >= n*q
            checked += 1
    return checked


def krawtchouk_bias_bound(limit):
    checked = 0
    for n in range(2, limit + 1):
        for a in range(n//2 + 1):
            imbalance = n - 2*a
            if imbalance == 0:
                continue
            for k in range(1, n):
                signed = sum((-1)**i * comb(a, i) * comb(n-a, k-i)
                             for i in range(max(0, k-(n-a)), min(a, k)+1))
                assert abs(signed)*n <= imbalance*comb(n, k)
                checked += 1
    return checked


if __name__ == "__main__":
    rng = Random(883)
    sizes = [(n, k) for n in range(1, 8) for k in range(1, n + 1)]
    print(f"{sum(proposed_chain(n, k) for n, k in sizes)} private prefix witnesses")
    print(f"{sum(basis_test(n, k, rng) for n, k in sizes)} simultaneous prefix bases checked by update")
    print(f"{sum(permutations_recovered(n,k) for n,k in [(4,2),(4,3),(5,4)])} permutations recovered via pinned SAT")
    print(f"{exact_checksum_certificates()} individual checksum certificate optima")
    print(f"{noisy_checksum_transcripts()} conditional hypergeometric checksum bias bounds")
    print(f"{last_row_advantage()} one-remaining-row Walsh advantages")
    print(f"{krawtchouk_bias_bound(104)} nonzero-imbalance Krawtchouk bounds through N=104")
