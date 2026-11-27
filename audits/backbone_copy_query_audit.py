"""Exhaustive small hidden-model query, witness-cover and proper-star checks."""
from functools import lru_cache
from itertools import combinations, product

from late_clause_support_audit import models


def members(mask):
    return [i for i in range(mask.bit_length()) if (mask >> i) & 1]


def profile_rank(values, variables):
    if not values:
        return 0
    rank = 0
    for j in range(variables):
        seen = {(x >> j) & 1 for x in values}
        digit = 2 if len(seen) == 2 else next(iter(seen))
        rank = 3 * rank + digit
    return rank + 1


def decision_thresholds(variables):
    u = 1 << variables
    profiles = set()
    maximum_queries = 0
    for mask in range(1 << u):
        values = members(mask)
        ranks = [profile_rank(chosen, variables)
                 for count in range(min(len(values), max(variables, 2)) + 1)
                 for chosen in combinations(values, count)]
        actual = profile_rank(values, variables)
        profiles.add(actual)
        low, high, calls = 0, 3 ** variables, 0
        while low < high:
            cutoff = (low + high + 1) // 2
            if any(rank >= cutoff for rank in ranks):
                low = cutoff
            else:
                high = cutoff - 1
            calls += 1
        assert low == actual == max(ranks)
        maximum_queries = max(maximum_queries, calls)
    assert len(profiles) == 3 ** variables + 1
    assert maximum_queries == (3 ** variables).bit_length()
    return len(profiles), maximum_queries


def optimal_single_copy(variables):
    """Full minimax: test every arbitrary first filter, every future legal reply."""
    u = 1 << variables
    universe = 1 << u
    target = [profile_rank(members(s), variables) for s in range(universe)]
    point = [sum(1 << s for s in range(universe) if (s >> x) & 1) for x in range(u)]
    branches = []
    for filt in range(1, universe):
        no = sum(1 << s for s in range(universe) if s & filt == 0)
        branches.append([no] + [point[x] for x in members(filt)])

    @lru_cache(None)
    def solvable(pool, depth):
        if len({target[i] for i in members(pool)}) <= 1:
            return True
        if depth == 0:
            return False
        return any(all(solvable(pool & branch, depth - 1) for branch in replies)
                   for replies in branches)
    inputs = (1 << universe) - 1
    assert not solvable(inputs, variables)
    assert solvable(inputs, variables + 1)
    return variables + 1


def check_batches(variables):
    calls = 0
    for mask in range(1, 1 << (1 << variables)):
        values = members(mask)
        for center in values:
            genuine = 0
            for x in values:
                genuine |= center ^ x
            for b in range(1, variables + 1):
                remaining = (1 << variables) - 1
                spent = 1

                def test(j):
                    nonlocal calls, spent, remaining
                    calls += 1
                    spent += j
                    best = None
                    # Repeated copies are allowed and can pad any shorter witness.
                    for count in range(1, min(j, len(values)) + 1):
                        for xs in combinations(values, count):
                            diff = 0
                            for x in xs:
                                diff |= x ^ center
                            seen = remaining & diff
                            if seen.bit_count() >= j and (best is None or seen.bit_count() < best.bit_count()):
                                best = seen
                    assert (best is not None) == ((remaining & genuine).bit_count() >= j)
                    if best is None:
                        return False
                    remaining &= ~best
                    return True

                while remaining and test(b):
                    pass
                j = 1 << ((b - 1).bit_length() - 1) if b > 1 else 0
                while remaining and j:
                    test(j)
                    j //= 2
                assert remaining == ((1 << variables) - 1) ^ genuine
                assert spent <= 1 + variables + 3 * b
    return calls


def stars(variables):
    anchors = [2 * variables + i for i in (1, 2, 3)]
    forced = [tuple(-v if x else v for x, v in zip(bits, anchors))
              for bits in product((0, 1), repeat=3) if any(bits)]
    n = 2 * variables + 3
    total = 0
    for center in range(1 << variables):
        base = list(forced)
        prior_name, prior_flip = anchors[0], 0
        for j in range(variables):
            present_name = variables + j + 1
            triple = (prior_name, j + 1, present_name)
            for a, x, y in product((0, 1), repeat=3):
                if a ^ x != y:
                    base.append(tuple(-v if z else v for v, z in zip(triple, (a, x, y))))
            flip = prior_flip ^ ((center >> j) & 1)
            before = -prior_name if prior_flip else prior_name
            after = -present_name if flip else present_name
            base.append((-before, after, anchors[2]))
            prior_name, prior_flip = present_name, flip
        for removed in range(1 << variables):
            clauses = base + [(j + 1 if center >> j & 1 else -(j + 1), *anchors[1:])
                              for j in members(removed)]
            assert all(len({abs(t) for t in c}) == 3 for c in clauses)
            expected = []
            for model in [center] + [center ^ (1 << j) for j in range(variables) if not removed >> j & 1]:
                prefix, auxiliary = 0, 0
                for j in range(variables):
                    prefix ^= (model >> j) & 1
                    auxiliary |= prefix << j
                expected.append(model | (auxiliary << variables))
            assert tuple(sorted(expected)) == models(clauses, n)
            total += 1
    return total


if __name__ == "__main__":
    counts = [decision_thresholds(v) for v in (1, 2, 3)]
    depths = [optimal_single_copy(v) for v in (1, 2)]
    formula_count = sum(stars(v) for v in (1, 2, 3))
    print(f"Decision profile counts and depths: {counts}; witness minimax depths: {depths}.")
    print(f"{check_batches(3)} threshold calls checked; {formula_count} proper star formulas exhaustively verified.")
