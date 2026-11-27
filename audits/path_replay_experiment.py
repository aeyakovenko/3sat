"""Compare optimal adaptive replay with the row-space formula on three input bits."""

from functools import cache
from itertools import combinations, product


INPUTS = range(8)
ALL_INPUTS = (1 << len(INPUTS)) - 1
DICTIONARIES = [(), (1, 2, 4), (3, 5, 6), (1, 3, 5, 7)]


def parity(mask, x):
    return (mask & x).bit_count() % 2


def inclusion_maximal(subsets):
    """Drop a successful input set if another tree already covers all of it."""
    kept = []
    for subset in sorted(set(subsets), key=int.bit_count, reverse=True):
        if not any((subset | other) == other for other in kept):
            kept.append(subset)
    return tuple(kept)


def tree_optima(target, dictionary):
    """Enumerate trees by their successful input sets, using a bit per input."""
    output_classes = [0] * 4
    for x in INPUTS:
        output = 2 * parity(target[0], x) + parity(target[1], x)
        output_classes[output] |= 1 << x

    probe_ones = [
        sum(1 << x for x in INPUTS if parity(probe, x)) for probe in dictionary
    ]

    @cache
    def successful_sets(reachable, probes_left):
        # A leaf chooses one common output for all inputs reaching it.
        results = {reachable & output_class for output_class in output_classes}
        if probes_left:
            for ones in probe_ones:
                left, right = reachable & ~ones, reachable & ones
                if not left or not right:
                    continue  # This probe cannot separate the reachable inputs.
                # Each branch can independently choose any remaining subtree.
                for a in successful_sets(left, probes_left - 1):
                    for b in successful_sets(right, probes_left - 1):
                        results.add(a | b)
        return inclusion_maximal(results)

    optima = {}
    for p in range(3):
        trees = successful_sets(ALL_INPUTS, p)
        unions = (0,)
        for descriptions in range(1, 5):
            unions = inclusion_maximal(a | b for a in unions for b in trees)
            if descriptions in (1, 2, 4):
                r = descriptions.bit_length() - 1
                optima[p, r] = max(mask.bit_count() for mask in unions)
    return optima


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            leading = row.bit_length() - 1
            if leading not in pivots:
                pivots[leading] = row
                break
            row ^= pivots[leading]
    return len(pivots)


def rank_prediction(target, dictionary, p, r):
    # dim W - dim(W intersect V) = dim(W + V) - dim V.
    residual = min(
        binary_rank(target + sample) - binary_rank(sample)
        for k in range(min(p, len(dictionary)) + 1)
        for sample in combinations(dictionary, k)
    )
    return len(INPUTS) // (1 << max(0, residual - r))


def main():
    checked = 0
    for target in product(INPUTS, repeat=2):
        for dictionary in DICTIONARIES:
            for (p, r), actual in tree_optima(target, dictionary).items():
                predicted = rank_prediction(target, dictionary, p, r)
                if actual != predicted:
                    raise AssertionError(
                        f'target={target}, dictionary={dictionary}, p={p}, r={r}: '
                        f'adaptive trees cover {actual}/8, rank predicts {predicted}/8'
                    )
                checked += 1
    assert checked == 64 * 4 * 3 * 3
    print(f'All {checked:,} optimal input fractions match the rank formula.')


if __name__ == '__main__':
    main()
