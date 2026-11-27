"""Exhaust all small projected witness sets and all public Toeplitz/offset coins."""
from fractions import Fraction


def packed(bits, length, width):
    return sum(((bits >> j) & 1) << (j * width) for j in range(length))


def toeplitz(v, diagonals, offset, x):
    direct = offset
    for i in range(v + 1):
        bit = sum(((diagonals >> (i - j + v - 1)) & 1) * ((x >> j) & 1) for j in range(v))
        direct ^= (bit & 1) << i
    width = v.bit_length()
    product = packed(diagonals, 2 * v, width) * packed(x, v, width)
    recovered = offset
    for i in range(v + 1):
        recovered ^= ((product >> ((v - 1 + i) * width)) & 1) << i
    assert direct == recovered
    return direct


def audit(v):
    universe = 1 << v
    seeds = 1 << (3*v + 1)
    wins = [0] * (1 << universe)
    fixed = [0] * (1 << universe)
    bit_sets = [sum(1 << x for x in range(universe) if x >> i & 1) for i in range(v)]
    for diagonal in range(1 << (2*v)):
        linear = [toeplitz(v, diagonal, 0, x) for x in range(universe)]
        for offset in range(1 << (v+1)):
            buckets = []
            for level in range(v+2):
                prefix = (1 << level)-1
                buckets.append(sum(1 << x for x in range(universe) if (linear[x]^offset)&prefix == 0))
            for witnesses in range(1, len(wins)):
                # Width zero is feasible and v+2 is an artificial infeasible right boundary.
                lo, hi = 0, v+2
                while hi-lo > 1:
                    mid = (lo+hi)//2
                    if buckets[mid] & witnesses:
                        lo = mid
                    else:
                        hi = mid
                last = buckets[lo] & witnesses
                assert last and all(not (bucket & witnesses) for bucket in buckets[lo+1:])
                level = (witnesses.bit_count()-1).bit_length()+1
                single_at_level = (buckets[level] & witnesses).bit_count() == 1
                fixed[witnesses] += single_at_level
                if last.bit_count() > 1:
                    assert not single_at_level
                    continue
                answer = sum(bool(last & selected) << i for i, selected in enumerate(bit_sets))
                assert last == 1 << answer and witnesses & (1 << answer)
                wins[witnesses] += 1
    assert 16 * min(fixed[1:]) >= 3 * seeds
    assert all(a >= b for a, b in zip(wins, fixed))
    return len(wins)-1, seeds, Fraction(min(wins[1:]), seeds)


if __name__ == '__main__':
    for v in (1, 2, 3):
        sets, coins, worst = audit(v)
        print(f'{v} variables, {sets} nonempty sets, {coins} hashes, minimum success {worst}')
