"""Optimal adaptive prediction of colored inverses with full past-index reveals."""

from collections import defaultdict
from fractions import Fraction
from functools import cache
from itertools import permutations
from math import comb


@cache
def tail(even, odd, keys, unknown, probes, need):
    """Maximum chance of at least need correct remaining predictions.

    Bits set in unknown designate active targets whose position is unseen.
    Exposed future targets are scored correctly at no additional cost.
    """
    if need <= 0:
        return Fraction(1)
    if need > keys:
        return Fraction(0)
    size = even + odd
    if unknown & 1:
        guesses = []
        for forecast in (0, 1):
            total = Fraction(0)
            for color, weight in enumerate((even, odd)):
                if weight:
                    total += weight * tail(even-(color == 0), odd-(color == 1),
                                           keys-1, unknown >> 1, probes,
                                           need-(color == forecast))
            guesses.append(total / size)
        best = max(guesses)
    else:
        best = tail(even, odd, keys-1, unknown >> 1, probes, need-1)
    if probes > 0 and size:
        unknown_keys = [i for i in range(keys) if unknown & (1 << i)]
        for color, weight in enumerate((even, odd)):
            if not weight:
                continue
            e, o = even-(color == 0), odd-(color == 1)
            total = sum((tail(e, o, keys, unknown ^ (1 << i), probes-1, need)
                         for i in unknown_keys), start=Fraction(0))
            if size > len(unknown_keys):
                total += (size-len(unknown_keys))*tail(e, o, keys, unknown, probes-1, need)
            best = max(best, total / size)
    return best


def literal_oracle(m, s):
    population = tuple(permutations(range(m)))

    @cache
    def optimum(possible, j, probes, need):
        if need <= 0:
            return Fraction(1)
        if need > s-j:
            return Fraction(0)
        score_groups = defaultdict(list)
        for table in possible:
            score_groups[table.index(j)].append(table)
        choices = []
        for bit in (0, 1):
            choices.append(sum(len(group)*optimum(tuple(group), j+1, probes,
                                                  need-(i % 2 == bit))
                               for i, group in score_groups.items()))
        if probes:
            for position in range(m):
                groups = defaultdict(list)
                for table in possible:
                    groups[table[position]].append(table)
                if len(groups) > 1:
                    choices.append(sum(len(group)*optimum(tuple(group), j, probes-1, need)
                                       for group in groups.values()))
        return max(choices) / len(possible)

    return lambda probes, need: optimum(population, 0, probes, need)


def binomial_tail(n, p, threshold):
    if threshold <= 0:
        return Fraction(1)
    return sum((comb(n, j)*p**j*(1-p)**(n-j) for j in range(threshold, n+1)),
               start=Fraction(0))


def check_two_implementations():
    checks = 0
    for m in (2, 4):
        for s in range(1, m+1):
            oracle = literal_oracle(m, s)
            for probes in range(m+1):
                for need in range(1, s+1):
                    result = tail(m//2, m//2, s, (1 << s)-1, probes, need)
                    assert result == oracle(probes, need)
                    checks += 1
    return checks


def check_martingale_bound():
    checks = nontrivial = 0
    for m in (12, 24, 64):
        for s in range(1, 8):
            for probes in range(5):
                unused = m-s-probes
                if unused <= m//2:
                    continue
                hit = min(Fraction(1), Fraction(s, unused))
                correct = Fraction(m, 2*unused)
                for need in range(1, s+1):
                    # A perfect prediction of a previously exposed target is
                    # charged to a hit. Every other success is a fresh guess.
                    upper = min(binomial_tail(probes, hit, a)
                                + binomial_tail(s, correct, need-a+1)
                                for a in range(1, min(need, probes+1)+1))
                    exact = tail(m//2, m//2, s, (1 << s)-1, probes, need)
                    assert exact <= upper
                    checks += 1
                    nontrivial += upper < 1
    return checks, nontrivial


if __name__ == "__main__":
    print("literal-vs-compressed optimal policies:", check_two_implementations())
    print("exact adaptive tail comparisons, bounds below one:", *check_martingale_bound())
