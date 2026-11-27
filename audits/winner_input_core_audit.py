"""Exhaust all small public pin sets and compare with the dual certificate."""
from itertools import combinations
from math import comb


def address_sum(data, bits, addresses):
    value = 0
    for i in range(addresses):
        if data >> i & 1:
            value ^= i & ((1 << bits) - 1)
    return value


def orthogonal_support(y, addresses):
    return sum(1 << i for i in range(addresses) if (i & y).bit_count() % 2)


def audit(bits, addresses):
    alphabet = 1 << bits
    assert addresses % alphabet == 0
    outputs = [address_sum(data, bits, addresses) for data in range(1 << addresses)]
    supports = [orthogonal_support(y, addresses) for y in range(alphabet)]
    assert all(s.bit_count() == addresses // 2 for s in supports[1:])
    blocked = [[0] * (addresses + 1) for _ in range(alphabet)]
    all_pins = (1 << addresses) - 1
    trials = 0
    for fixed in range(1 << addresses):
        free = all_pins ^ fixed
        counts = [0] * alphabet
        data = free
        while True:
            counts[outputs[data]] += 1
            if not data:
                break
            data = (data - 1) & free
        for delta, count in enumerate(counts):
            certificate = any((delta & y).bit_count() % 2 and not (free & s)
                              for y, s in enumerate(supports))
            assert certificate == (count == 0)
            if count:
                assert count * sum(c > 0 for c in counts) == 1 << free.bit_count()
            else:
                blocked[delta][fixed.bit_count()] += 1
            trials += 1

    for delta in range(1, alphabet):
        relevant = [s for y, s in enumerate(supports) if (delta & y).bit_count() % 2]
        for size in range(addresses + 1):
            # Exactly count samples containing at least one required support.
            exact = 0
            for k in range(1, len(relevant) + 1):
                for selected in combinations(relevant, k):
                    union = 0
                    for s in selected:
                        union |= s
                    occupied = union.bit_count()
                    if size >= occupied:
                        exact += (-1)**(k+1) * comb(addresses-occupied, size-occupied)
            assert exact == blocked[delta][size]
    return trials


if __name__ == '__main__':
    trials = sum(audit(b, m) for b, m in [(1, 4), (1, 8), (2, 4), (2, 8), (2, 12), (3, 8)])
    print(f'{trials} pin-mask and target comparisons; exact fixed-size sample counts agree')
