"""Finite checks for the binary tensor tests, exact distance and native tile layout."""

from argparse import ArgumentParser
from itertools import combinations, product
from random import Random


def mul(a, b, field_size, modulus):
    value = 0
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        if a & field_size:
            a ^= modulus
        b >>= 1
    return value


def basis(radix, field_size, modulus):
    powers = [1] * radix
    rows, costs, pivots = [], [], {}
    for exponent in range(radix):
        for bit in range(field_size.bit_length() - 1):
            row = sum(((v >> bit) & 1) << i for i, v in enumerate(powers))
            reduced = row
            while reduced:
                p = reduced.bit_length() - 1
                if p not in pivots:
                    pivots[p] = reduced
                    rows.append(row)
                    costs.append(exponent + 1)
                    break
                reduced ^= pivots[p]
        powers = [mul(v, i, field_size, modulus) for i, v in enumerate(powers)]
    assert len(rows) == radix
    return rows, costs


def transform(x, rows):
    return sum(((x & row).bit_count() & 1) << i for i, row in enumerate(rows))


def tensor_mask(left, right, width):
    return sum(right << (width * i) for i in range(left.bit_length()) if left & (1 << i))


def tensor_axes(axes):
    rows, costs, size = [1], [1], 1
    for local, local_cost in axes:
        rows = [tensor_mask(u, v, len(local)) for u in rows for v in local]
        costs = [a * b for a in costs for b in local_cost]
        size *= len(local)
    assert len(rows) == size
    return rows, costs


def partial_distances(rows):
    minima = [len(rows) + 1] * len(rows)
    for x in range(1, 1 << len(rows)):
        y = transform(x, rows)
        i = (y & -y).bit_length() - 1
        minima[i] = min(minima[i], x.bit_count())
    return minima


def distance_audit(axes):
    rows, costs = tensor_axes(axes)
    products = [1]
    for local, _ in axes:
        distances = partial_distances(local)
        products = [v * p for v in products for p in distances]
    cheapest = [0] * (1 << len(rows))
    for y in range(1, len(cheapest)):
        bit = y & -y
        cheapest[y] = costs[bit.bit_length() - 1]
        if y ^ bit:
            cheapest[y] = min(cheapest[y], cheapest[y ^ bit])
    first_weights = [len(rows) + 1] * (len(rows) + 1)
    for x in range(1, 1 << len(rows)):
        cost = cheapest[transform(x, rows)]
        first_weights[cost] = min(first_weights[cost], x.bit_count())
        assert cost <= x.bit_count()
    for cutoff in range(len(rows) + 1):
        actual = min(first_weights[cutoff + 1:], default=len(rows) + 1)
        expected = min((p for p, c in zip(products, costs) if c > cutoff), default=len(rows) + 1)
        assert actual == expected
    return (1 << len(rows)) - 1


def transpose_tiles(words, lanes):
    """Exchange row and column index bits in every side-by-side square."""
    side = len(words)
    words = list(words)
    shift = 1
    while shift < side:
        mask = sum(1 << i for i in range(lanes) if i & shift == 0)
        for i in range(side):
            if i & shift:
                continue
            j = i | shift
            delta = ((words[i] >> shift) ^ words[j]) & mask
            words[i] ^= delta << shift
            words[j] ^= delta
        shift *= 2
    return words


def check_tile(words, rows, lanes):
    s = len(rows)
    transposed = transpose_tiles(words, lanes)
    transformed = []
    for word in transposed:
        packed = 0
        for start in range(0, lanes, s):
            packed |= transform((word >> start) & ((1 << s) - 1), rows) << start
        transformed.append(packed)
    actual = transpose_tiles(transformed, lanes)
    for j, mask in enumerate(rows):
        direct = 0
        for i, word in enumerate(words):
            if (mask >> i) & 1:
                direct ^= word
        assert actual[j] == direct


def check_projected_files():
    from compact_product_projection_audit import ProductLayout, check_models

    side = 2
    layout = ProductLayout(side, 1)
    rows, costs = basis(side, 2, 3)
    files = models = 0
    for values in product((0, 1), repeat=12):
        a, b, c = values[:4], values[4:8], values[8:]
        count = check_models(layout, list(values))
        smallest = 5
        for u, left_cost in zip(rows, costs):
            for v, right_cost in zip(rows, costs):
                left = [sum(a[2*i+k] for i in range(2) if (u >> i) & 1) % 2
                        for k in range(2)]
                right = [sum(b[2*k+j] for j in range(2) if (v >> j) & 1) % 2
                         for k in range(2)]
                proposed = sum(c[2*i+j] for i in range(2) for j in range(2)
                               if ((u >> i) & 1) and ((v >> j) & 1)) % 2
                if sum(x*y for x, y in zip(left, right)) % 2 != proposed:
                    smallest = min(smallest, left_cost * right_cost)
        for budget in range(1, 5):
            detected = smallest <= budget
            assert not detected or count > 0
            if count <= budget:
                assert detected == bool(count)
        files += 1
        models += count
    print(f'{files} projected DIMACS files, {models} complete models, all four budgets checked')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--dimacs', action='store_true', help='also run PicoSAT on all side-two files')
    options = parser.parse_args()
    local = {n: basis(n, 8, 0b1011) for n in (2, 4, 8)}
    total = sum(distance_audit([local[s] for s in axes])
                for axes in ((2, 2), (4, 2), (2, 2, 2), (4, 4)))
    rng = Random(10491)
    tiles = 0
    for s, lanes in product((2, 4, 8), (8, 16, 32)):
        for _ in range(60):
            check_tile([rng.getrandbits(lanes) for _ in range(s)], local[s][0], lanes)
            tiles += 1
    rows, costs = tensor_axes([local[s] for s in (4, 2, 4, 2)])
    for weight in (1, 2, 3):
        eligible = [row for row, cost in zip(rows, costs) if cost <= weight]
        for support in combinations(range(len(rows)), weight):
            x = sum(1 << i for i in support)
            assert any((row & x).bit_count() & 1 for row in eligible)
            total += 1
    print(f'{total} error patterns passed; four full distance profiles and {tiles} packed tiles checked')
    if options.dimacs:
        check_projected_files()
