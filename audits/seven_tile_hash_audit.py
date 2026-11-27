"""Check affine hash counts against actual seven-tip sign strings and raw colors."""

from collections import Counter, defaultdict
from itertools import pairwise, permutations, product
from random import Random

from single_lane_sat import TIPS


def coordinates(signs):
    bases = [0]
    tips = []
    for sign in signs:
        tips.append((bases[-1] - sign) % 3)
        bases.append((bases[-1] + sign) % 3)
    return bases, tips


def local_choices():
    words = []
    for signs in product((1, -1), repeat=7):
        _, tips = coordinates(signs)
        if all(tips[u] != tips[v] for u, v in pairwise(TIPS)):
            words.append(signs)
    assert len(words) == 4
    return words


def pack_signs(signs):
    return sum(1 << i for i, s in enumerate(signs) if s < 0)


def pack_colors(colors):
    return sum(1 << (3 * i + c) for i, c in enumerate(colors))


def fibers(order, choices):
    # Each row stores both the physical sign bits and one-hot color flags.
    # Do not use the proposed linear parametrization to generate any colors.
    n = len(order)
    result = defaultdict(list)
    for chosen in product(choices, repeat=n):
        signs = tuple(s for tile in chosen for s in tile)
        bases, tips = coordinates(signs)
        blue = [7 * vertex + tip for vertex in order for tip in TIPS]
        if all(tips[u] != tips[v] for u, v in pairwise(blue)):
            key = tuple(bases[7 * i] for i in range(n))
            result[key].append((pack_signs(signs), pack_colors(bases + tips)))
    return result


def syndrome(rows, value):
    return sum(((mask & value).bit_count() % 2) << i for i, mask in enumerate(rows))


def binary_basis(vectors):
    pivots = {}
    for vector in vectors:
        while vector:
            highest = vector.bit_length() - 1
            if highest not in pivots:
                pivots[highest] = vector
                break
            vector ^= pivots[highest]
    return tuple(pivots.values())


def span(vectors):
    values = [0]
    for vector in binary_basis(vectors):
        values += [v ^ vector for v in values]
    return values


def source_colorings(order):
    n = len(order)
    return {
        r
        for tail in product(range(3), repeat=n - 1)
        for r in [(0,) + tail]
        if all(a != b for a, b in pairwise(r))
        and all(r[a] != r[b] for a, b in pairwise(order))
    }


def raw_directions(key):
    n = len(key)
    num_bases = 7 * n + 1
    masks = []
    for i, source_color in enumerate(key):
        colors = set(range(3)) - {source_color}
        sites = [7 * i + j for j in (1, 2, 3, 4)]
        sites += [num_bases + 7 * i + j for j in (0, 4)]
        masks.append(sum(1 << (3 * v + c) for v in sites for c in colors))
    colors = set(range(3)) - {key[-1]}
    sites = [7 * n - 1, 7 * n, num_bases + 7 * (n - 1) + 5]
    masks.append(sum(1 << (3 * v + c) for v in sites for c in colors))
    return masks


def check(order, choices, rng):
    n = len(order)
    by_source = fibers(order, choices)
    assert set(by_source) == source_colorings(order)
    all_signs = [s for rows in by_source.values() for s, _ in rows]
    signed_dims = [31 << (7 * i) for i in range(n)] + [96 << (7 * (n - 1))]
    reflected_dims = signed_dims + [(1 << (7 * n)) - 1]
    assert len(binary_basis(reflected_dims)) == n + 2
    h = len(by_source)
    for key, records in by_source.items():
        start = records[0][1]
        assert {start ^ raw for _, raw in records} == set(span(raw_directions(key)))
    pins = [1 << (7 * i) for i in range(n)] + [1 << (7 * (n - 1) + 5), 1 << 5]
    for k in (n + 1, n + 2):
        actual = Counter(syndrome(pins[:k], x) for x in all_signs)
        assert all(actual[w] == h // (1 << (k - n - 1)) for w in range(2**k))
    for count in (0, 1, n + 1, n + 2, n + 4):
        rows = [rng.getrandbits(7 * n) for _ in range(count)]
        projected = span([syndrome(rows, d) for d in reflected_dims])
        expected = Counter()
        for key, records in by_source.items():
            if key[1] == 1:  # One representative per global reflection orbit.
                shift = syndrome(rows, records[0][0])
                for w in projected:
                    expected[shift ^ w] += 2 ** (n + 2) // len(projected)
        assert expected == Counter(syndrome(rows, s) for s in all_signs)
        raw_tests = [rng.getrandbits(3 * (14 * n + 1)) for _ in range(count)]
        for key, records in by_source.items():
            raw_span = span([syndrome(raw_tests, v) for v in raw_directions(key)])
            raw_shift = syndrome(raw_tests, records[0][1])
            raw_hist = Counter(syndrome(raw_tests, r) for _, r in records)
            assert raw_hist == {
                raw_shift ^ w: 2 ** (n + 1) // len(raw_span) for w in raw_span
            }
    return len(all_signs)


def audit():
    choices = local_choices()
    rng = Random(93173)
    instances = witnesses = 0
    for n in range(2, 6):
        orders = (
            list(permutations(range(n)))
            if n <= 4
            else [tuple(rng.sample(range(n), n)) for _ in range(8)]
        )
        for order in orders:
            witnesses += check(order, choices, rng)
            instances += 1
    print(
        f"{instances} two-path orders, {witnesses} valid sign strings, and {5 * instances} dense hash pairs checked."
    )


if __name__ == "__main__":
    audit()
