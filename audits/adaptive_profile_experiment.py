"""Finite checks for the adaptive threshold and online prefix code."""

from fractions import Fraction
from random import Random


def power(exponent):
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << -exponent)


def code_length(weight):
    length = 0
    while power(-length) > weight:
        length += 1
    return length


def grant_lengths(lengths):
    free = {0: ''}
    allocated = []
    for length in lengths:
        depth = max(depth for depth in free if depth <= length)
        prefix = free.pop(depth)
        while depth < length:
            depth += 1
            free[depth] = prefix + '1'
            prefix += '0'
        assert all(not (prefix.startswith(old) or old.startswith(prefix))
                   for old in allocated)
        allocated.append(prefix)
    return allocated


def transition(lengths, cutoff, header, reserve, extra_weight):
    quota = 1 << (cutoff - header)
    assert len(lengths) == quota and max(lengths) < cutoff
    arrival = sum((power(-length) for length in lengths), extra_weight)
    weight = power(-45) + arrival / 8
    next_header = reserve + code_length(weight)
    cap = cutoff - 1 - header + next_header
    population = sorted(lengths)
    next_cutoff = max(t for t in range(cap + 1)
                      if sum(length >= t for length in population)
                      >= power(t - next_header))
    drop = cap - next_cutoff
    if drop:
        assert arrival >= power(drop - next_header)
    assert drop <= reserve + 4 and next_cutoff < cutoff
    assert (cutoff - header) - (next_cutoff - next_header) == 1 + drop
    return drop


def main():
    rng = Random(20261124)
    observed = set()
    count = 0
    for rank_bits in range(1, 8):
        header = 20
        cutoff = header + rank_bits
        for reserve in (1, 3, 5):
            for unused in range(25):
                lengths = [rng.randrange(max(10, cutoff - 11), cutoff)
                           for _ in range(1 << rank_bits)]
                for extra in (Fraction(0), power(-12), power(-4)):
                    observed.add(transition(lengths, cutoff, header, reserve, extra))
                    count += 1
    assert len(observed) >= 4
    requests = [2, 2, 3, 4, 5, 6, 7, 8]
    for unused in range(200):
        rng.shuffle(requests)
        grant_lengths(requests)
    print(f'{count} adaptive transitions checked, including overshoots {sorted(observed)}')
    print('200 chronological orders of prefix requests checked')


if __name__ == '__main__':
    main()
