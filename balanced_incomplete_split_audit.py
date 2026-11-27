"""Check deterministic conditional-expectation splitting, independent sets and SAT replay."""

from collections import Counter
from itertools import combinations, product
from random import Random

from complete_csp_macro_audit import macro_solve
from incomplete_triple_rectangle_audit import PaddedTriples


def independent_weights(n, supports, cutoff=None):
    """Packed big-integer rows stand for consecutive native word bitsets in the analysis."""
    full = (1 << n) - 1
    missing = [[full] * n for _ in range(n)]
    for x, y, z in supports:
        missing[x][y] &= ~(1 << z)
        missing[x][z] &= ~(1 << y)
        missing[y][z] &= ~(1 << x)
    weights = Counter()
    count = 0

    def visit(prefix, available):
        nonlocal count
        count += 1
        if cutoff is not None and (count > cutoff or 1 << len(prefix) > cutoff):
            raise OverflowError('too many independent sets')
        if len(prefix) >= 3:
            weights[tuple(prefix[:3])] += 1
        while available:
            bit = available & -available
            available ^= bit
            x = bit.bit_length() - 1
            keep = available
            for y in prefix:
                keep &= missing[y][x]
            prefix.append(x)
            visit(prefix, keep)
            prefix.pop()

    visit([], full)
    return weights, count


def level_data(groups, weights):
    location = [0] * sum(map(len, groups))
    for i, block in enumerate(groups):
        for v in block:
            location[v] = i
    pair_weight = triple_weight = actual = 0
    blocks = len(groups)
    for triple, w in weights.items():
        labels = [location[x] for x in triple]
        seen = len(set(labels))
        pair_weight += sum(x == y for x, y in combinations(labels, 2)) * w
        triple_weight += (seen == 1) * w
        actual += (2 * blocks - 1 if seen == 1 else 2 if seen == 2 else 0) * w
    return location, blocks * triple_weight + pair_weight, actual


def term_cost(term, assignment):
    # Eight times the conditional probability that all resulting colors agree.
    colors = set()
    free = 0
    for key, side in term:
        choice = assignment[key]
        if choice < 0:
            free += 1
        else:
            colors.add(side ^ choice)
    if len(colors) > 1:
        return 0
    return (8 if colors else 16) >> free


def split_level(groups, weights):
    previous, old_potential, _ = level_data(groups, weights)
    coords = [None] * len(previous)
    key = 0
    for block in groups:
        for j in range(0, len(block), 2):
            coords[block[j]] = (key, 0)
            coords[block[j + 1]] = (key, 1)
            key += 1
    terms = []
    incident = [[] for _ in range(key)]

    def add(vertices, w):
        if any(previous[x] != previous[vertices[0]] for x in vertices):
            return
        term = tuple(coords[x] for x in vertices)
        if len({j for j, _ in term}) != len(term):
            return
        idx = len(terms)
        terms.append((term, w))
        for j, _ in term:
            incident[j].append(idx)

    for triple, w in weights.items():
        add(triple, 2 * len(groups) * w)
        for pair in combinations(triple, 2):
            add(pair, w)
    bits = [-1] * key
    for j, indices in enumerate(incident):
        scores = []
        for side in (0, 1):
            bits[j] = side
            scores.append(sum(term_cost(terms[idx][0], bits) * terms[idx][1] for idx in indices))
        bits[j] = int(scores[1] < scores[0])
    out = []
    for block in groups:
        children = [[], []]
        for x in block:
            j, side = coords[x]
            children[side ^ bits[j]].append(x)
        assert 2 * len(children[0]) == len(block)
        out.extend(children)
    _, new_potential, _ = level_data(out, weights)
    assert 2 * new_potential <= old_potential
    return out


def layout(n, weights):
    p = 1 << (max(1, n) - 1).bit_length()
    groups = [list(range(p))]
    actual = 0
    while True:
        _, potential, score = level_data(groups, weights)
        assert score <= 2 * potential
        actual += score
        if len(groups) == p:
            break
        groups = split_level(groups, weights)
    assert actual <= 16 * sum(weights.values())
    positions = [0] * p
    for i, block in enumerate(groups):
        positions[block[0]] = i
    return positions, actual


def audit():
    rng = Random(711194)
    cases = weighted_sets = visited = max_score = 0
    for n in range(3, 10):
        supports = list(combinations(range(n), 3))
        for shape in range(10):
            masks = {t: 1 << rng.randrange(8) for t in supports if rng.randrange(9) >= shape}
            if shape == 0:
                masks = {t: 1 << 7 for t in supports if t[-1] >= n // 2}
            weights, ct = independent_weights(n, masks)
            slow = Counter()
            for s in range(3, n + 1):
                for subset in combinations(range(n), s):
                    if all(t not in masks for t in combinations(subset, 3)):
                        slow[subset[:3]] += 1
            assert weights == slow
            assert ct == 1 + n + n * (n - 1) // 2 + sum(weights.values())
            assert independent_weights(n, masks, ct)[1] == ct
            try:
                independent_weights(n, masks, ct - 1)
            except OverflowError:
                pass
            else:
                raise AssertionError('false promise accepted')
            places, score = layout(n, weights)
            # The wrapper has zero-constrained gaps, not extra free variables.
            padded = PaddedTriples(places, n, masks)
            rows, cells = macro_solve(padded)
            assert all(not row[places[x]] for row in rows for x in range(n, len(places)))
            found = sorted(tuple(row[places[x]] for x in range(n)) for row in rows)
            brute = [row for row in product((0, 1), repeat=n)
                     if all(not (mask >> (4 * row[a] + 2 * row[b] + row[c]) & 1)
                            for (a, b, c), mask in masks.items())]
            assert found == brute
            weighted_sets += sum(weights.values())
            visited += cells
            max_score = max(max_score, score)
            cases += 1
    n = 17
    special = Counter({t: rng.randrange(1, 1024) for t in combinations(range(n), 3)})
    layout(n, special)
    print(f'{cases} partial supports, {weighted_sets} charged sets, {visited} macro keys; '
          f'all potentials, cutoffs, gap bits and solutions passed (largest score {max_score})')


if __name__ == '__main__':
    audit()
