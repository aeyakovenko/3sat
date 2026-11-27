"""Exact checks of dyadic speed bins and of request order by work score."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from random import Random

from near_clock_code_experiment import approximate_batch, check_streams


def neg_log_ceiling(probability):
    """Smallest b with 2**(-b) <= probability, for 0 < probability <= 1."""
    b = max(0, probability.denominator.bit_length() - probability.numerator.bit_length())
    if (probability.numerator << b) < probability.denominator:
        b += 1
    return b


def speed_bins():
    # Four disjoint exact names, each with probability 1/4.
    outcomes = [None] + list(product(("0", "1"), (3, 5, 513)))
    cases = checks = discarded_tails = 0
    for result in product(outcomes, repeat=4):
        cases += 1
        for word in ("0", "1"):
            times = [entry[1] for entry in result if entry is not None and entry[0] == word]
            if not times:
                continue
            weight = sum(Fraction(1, 4 * time) for time in times)
            b = neg_log_ceiling(weight)
            Q = b + 2
            heaviest_bin = Fraction()
            for q in range(1, Q + 1):
                in_bin = [time for time in times if (q == 1 or time > 1 << (q - 1)) and time <= 1 << q]
                heaviest_bin = max(heaviest_bin, sum(Fraction(1, 4 * time) for time in in_bin))
            tail = sum(Fraction(1, 4 * time) for time in times if time > 1 << Q)
            assert tail <= weight / 4
            assert heaviest_bin >= weight / (2 * Q)
            best = max(Fraction(sum(time <= 1 << q for time in times), 4 << q)
                       for q in range(1, Q + 1))
            assert best >= weight / (4 * Q)
            discarded_tails += bool(tail)
            checks += 1
    assert discarded_tails > 0
    return cases, checks, discarded_tails


def scores():
    words = ("00", "01", "10", "11")
    # The estimates can fall although the actual masses only increase.
    checks = inversions = 0
    for shifts in product(range(3), repeat=3):
        atoms = ((2, 0, 2), (3, 1, 3), (5, 2, 4), (7, 0, 4), (9, 3, 3), (12, 2, 4))
        requests = {}
        source_depth = {}
        for q in range(1, 5):
            for i, word in enumerate(words):
                mass = sum(Fraction(1, 1 << length)
                           for time, target, length in atoms if target == i and time <= 1 << q)
                if not mass:
                    continue
                estimate = mass / (1 << ((q + i + shifts[q % 3]) % 6))
                source_depth[q, word] = neg_log_ceiling(mass) + 5
                for d in range(neg_log_ceiling(estimate), (1 << q) + 6):
                    requests.setdefault((word, d), q)

        def score(q, d):
            # (d+1).bit_length() = ceil(log2(d+2)).
            return q + 7 * (d + 1).bit_length()

        contents = defaultdict(list)
        for (word, d), q in requests.items():
            contents[q, d].append(word)
        order = sorted(contents, key=lambda key: (score(*key), *key))
        inversions += sum(order[i][0] < order[i-1][0] for i in range(1, len(order)))
        cursor = Fraction()
        batches = []
        for key in order:
            q, d = key
            counts = Counter(prefix for word in contents[key] for prefix in ("", word[:1], word))
            batch = approximate_batch(cursor, d, 2, contents[key],
                                      {prefix: Fraction(n) for prefix, n in counts.items()})
            cursor = batch.stop
            batches.append(batch)
        assert cursor <= Fraction(1, 4)
        check_streams(batches)
        for (q, word), d in source_depth.items():
            first = requests[word, d]
            assert score(first, d) <= score(q, d)
            checks += 1
    assert inversions > 0
    return checks, inversions


def locate_maximum():
    """Compare the stratified search with a full census of a finite prefix machine."""
    s = 4
    n0 = 1 << s
    mask_bits = 9
    # Program prefixes, explicit unary output lengths and integer completion times.
    names = [("0" + format(i, "04b"), n0 + i, 3 * (n0 + i))
             for i in range(n0)]
    names += [("10" + format(i, "05b"), n0 + 5, n0 + 8) for i in range(32)]
    names += [("110" + format(i, "06b"), n0 + 11, 65536) for i in range(64)]
    lookup = [None] * (1 << mask_bits)
    cost = {}
    weight = defaultdict(Fraction)
    for name, n, time in names:
        log_time = (time - 1).bit_length()
        candidate = len(name) + log_time
        cost[n] = min(cost.get(n, candidate), candidate)
        weight[n] += Fraction(1, (1 << len(name)) * time)
        start = int(name, 2) << (mask_bits - len(name))
        for address in range(start, start + (1 << (mask_bits - len(name)))):
            assert lookup[address] is None
            lookup[address] = n, log_time
    score = {n: (1 << cost[n]) * weight[n] for n in cost}
    true_max = max(score, key=score.get)
    bins = max(cost.values()) + 3
    trials = 16 * (s + 1) * (1 << bins)
    rng = Random(41899)
    hits = Counter()
    for j in range(1, bins + 1):
        for _ in range(trials >> j):
            outcome = lookup[rng.getrandbits(mask_bits)]
            if outcome is not None and outcome[1] == j:
                hits[outcome[0]] += 1
    estimates = {n: Fraction(hits[n], trials) for n in cost}
    assert all(weight[n] / 5 <= estimates[n] <= 2 * weight[n] for n in cost)
    found = max(cost, key=lambda n: (1 << cost[n]) * hits[n])
    assert true_max == found
    return found, score[found], trials - (trials >> bins)


if __name__ == "__main__":
    cases, bins, tails = speed_bins()
    checks, inversions = scores()
    print(f"{cases} publication tables, {bins} positive speed masses, {tails} nonempty discarded tails")
    print(f"{checks} word-deadline checks with {inversions} epoch reversals in score order")
    winner, score, trials = locate_maximum()
    print(f"Stratified search: length {winner}, exact cost-weight product {score}, {trials} trials")
