"""Check the best cumulative deadline and run the two-threshold block search."""

from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from random import Random

from discounted_mass_experiment import neg_log_ceiling


def deadline_envelope(rates, stretch):
    return max(
        Fraction(sum(value >= threshold for value in rates), len(rates))
        * min(1, stretch * threshold)
        for threshold in rates if threshold
    )


def compare_envelopes():
    alphabet = [Fraction(0), Fraction(1, 1024), Fraction(1, 13),
                Fraction(1, 4), Fraction(2, 3), Fraction(1)]
    profiles = 0
    for rates in combinations_with_replacement(alphabet, 8):
        mass = sum(rates) / len(rates)
        if not mass:
            continue
        stretch = neg_log_ceiling(mass) + 2
        assert 2 * deadline_envelope(rates, stretch) >= mass
        profiles += 1
    # For uniform publication at times t, 2t, ..., mt the sharp unscaled
    # envelope is exactly 1/m even as the harmonic sum grows.
    size = 256
    rates = [Fraction(1, i) for i in range(1, size + 1)]
    mass = sum(rates) / size
    for stretch in (1, 2, 3, 8, 17, size):
        assert deadline_envelope(rates, stretch) == Fraction(stretch, size)
    return profiles, float(size * mass)


def threshold_search():
    baseline, log_baseline, budget, depth = 16, 4, 5, 3
    programs = {
        '0' + format(i, '04b'): (16 + i, 512 if i in (5, 6) else 16)
        for i in range(16)
    }
    programs.update({'10' + format(i, '06b'): (21, 27) for i in range(64)})
    programs.update({'110': (24, 8), '1110': (19, 16384)})

    # Resolve the finite prefix sampler on all possible eight-bit input tapes.
    width = max(map(len, programs))
    sampler = [None] * (1 << width)
    for name, outcome in programs.items():
        start = int(name, 2) << (width - len(name))
        for i in range(start, start + (1 << (width - len(name)))):
            assert sampler[i] is None
            sampler[i] = outcome

    cheap = set()
    for length in range(budget + 1):
        for index in range(1 << length):
            name = format(index, f'0{length}b') if length else ''
            outcome = programs.get(name)
            if outcome and outcome[1] <= baseline << (budget - length):
                cheap.add(outcome[0])
    exact_mass = Counter()
    exact_cheap = set()
    for name, (word, time) in programs.items():
        exact_mass[word] += min(Fraction(1), Fraction(baseline, time)) / (1 << len(name))
        log_time = (time - 1).bit_length()
        if len(name) + max(0, log_time - log_baseline) <= budget:
            exact_cheap.add(word)
    assert cheap == exact_cheap

    max_bin = depth + 4
    streams = (1 << max_bin) * 64 * (log_baseline + 1)
    rng = Random(80621)
    hits = Counter()
    trials = 0
    for j in range(max_bin + 1):
        upper = baseline << j
        lower = upper // 2 if j else 0
        for _ in range(streams >> j):
            outcome = sampler[rng.getrandbits(width)]
            if outcome and lower < outcome[1] <= upper:
                hits[outcome[0]] += 1
            trials += 1
    result = {word for word, count in hits.items()
              if word not in cheap and (count << (depth + 2)) >= streams}
    threshold = Fraction(1, 1 << depth)
    required = {word for word, mass in exact_mass.items()
                if word not in cheap and mass >= threshold}
    permitted = {word for word, mass in exact_mass.items()
                 if word not in cheap and mass > threshold / 8}
    assert required == result == permitted == {21}
    return sorted(result), trials, exact_mass[21]


if __name__ == '__main__':
    profiles, harmonic = compare_envelopes()
    print(f'{profiles} positive profiles passed; uniform-clock mass/envelope = {harmonic:.6f} at 256 clocks')
    found, trials, score = threshold_search()
    print(f'{trials} independent streams; surviving lengths {found}; exact mass {score}')
