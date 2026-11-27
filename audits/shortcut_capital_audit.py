"""Check exact specialist updates and the advice-prefix covering construction."""

from itertools import product


def prefix_length(s):
    d = (s + 1).bit_length() - 1
    return d + 2 * ((d + 1).bit_length() - 1) + 1


def run(rows, initial):
    weights = list(initial)
    correct = [0] * len(initial)
    wrong = [0] * len(initial)
    table = []
    for votes in rows:
        mass = [sum(w for w, vote in zip(weights, votes) if vote == bit) for bit in (0, 1)]
        bit = int(mass[1] < mass[0])
        table.append(bit)
        previous_total = sum(weights)
        for i, vote in enumerate(votes):
            if vote == bit:
                weights[i] *= 2
                correct[i] += 1
            elif vote is not None:
                weights[i] = 0
                wrong[i] += 1
        assert sum(weights) <= previous_total
        for i, w in enumerate(weights):
            expected = 0 if wrong[i] else initial[i] * 2**correct[i]
            assert w == expected
            if not wrong[i]:
                assert expected <= sum(initial)
    return table


def proposals(begin, end, extra):
    # All prefixes are integer intervals at one common depth.
    maximum = max(s + extra(s) for s in range(begin, end + 1))
    limit = 1 << maximum
    left = 0
    ranges = []
    for s in range(begin, end + 1):
        width = s + extra(s)
        cell = 1 << (maximum - width)
        assert left % cell == 0
        for advice in range(1 << s):
            start = left + advice * cell
            if start >= limit:
                break
            ranges.append((start, start + cell, width, left // cell + advice))
        left += (1 << s) * cell
        if left >= limit:
            break
    assert left >= limit
    assert ranges[0][0] == 0 and ranges[-1][1] == limit
    assert all(x[1] == y[0] for x, y in zip(ranges, ranges[1:]))
    for start, stop, width, prefix in ranges:
        assert start >> (maximum - width) == prefix
        assert (stop - 1) >> (maximum - width) == prefix
    return limit, len(ranges)


def main():
    ballots = list(product((None, 0, 1), repeat=3))
    n = 0
    for rows in product(ballots, repeat=3):
        for initial in ((1, 1, 1), (1, 2, 8)):
            run(rows, initial)
            n += 1
    max_s = 48
    common_bits = max(s + prefix_length(s) for s in range(max_s + 1))
    total = sum(1 << (common_bits - prefix_length(s)) for s in range(max_s + 1))
    assert total <= 1 << common_bits
    covered = [proposals(0, 3, lambda _: 2),
               proposals(2, 6, lambda s: 2 if s < 4 else 1),
               proposals(3, 10, lambda s: (s + 2).bit_length() - 1)]
    print(f'{n:,} weighted histories checked. Three advice covers partitioned '
          f'{sum(tables for tables, _ in covered):,} tables into '
          f'{sum(cells for _, cells in covered):,} dyadic intervals.')


if __name__ == '__main__':
    main()
