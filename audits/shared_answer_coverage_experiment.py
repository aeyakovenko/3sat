"""All injective three-name tables on four affine hidden-answer settings."""

from itertools import permutations, product


# The public promise is c = a XOR b. One query may ask for any of a, b or c.
settings = [(a, b, a ^ b) for a, b in product(range(2), repeat=2)]


def minimal_depth(table):
    if len(set(table)) == 1:
        return 0
    for column in zip(*settings):
        if all(len({table[i] for i in range(4) if column[i] == t}) == 1 for t in range(2)):
            return 1
    return 2


def main():
    labels = range(4)
    injections = list(permutations(labels, 3))
    omitted = {row: next(x for x in labels if x not in row) for row in injections}
    depth = {v: minimal_depth(v) for v in product(labels, repeat=4)}
    counts = [0, 0, 0]
    maxima = [0, 0, 0]
    for model in product(injections, repeat=4):
        k = max(depth[v] for v in zip(*model))
        holes = tuple(omitted[instance] for instance in model)
        counts[k] += 1
        maxima[k] = max(maxima[k], len(set(holes)))
        assert len(set(holes)) <= 2 ** k
        assert all((holes.count(x) * 2 ** k) % len(settings) == 0 for x in labels)
    assert sum(counts) == 24 ** 4
    assert maxima == [1, 2, 4]
    print(f'{sum(counts):,} models; counts by depth {counts}; maximum hole supports {maxima}')


if __name__ == '__main__':
    main()
