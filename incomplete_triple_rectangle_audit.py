"""Check the deterministic order and adaptive rectangle solver on incomplete triples."""
from collections import Counter
from itertools import combinations, product
from random import Random

from complete_csp_dyadic_audit import solve


def independent_sets(n, present, cutoff=None):
    """Report every independent set once. Block z if adding z completes a triple."""
    blocked = [0] * n
    answer = []

    def visit(current, start):
        answer.append(tuple(current))
        if cutoff is not None and len(answer) > cutoff:
            raise OverflowError("independent-set budget exhausted")
        for x in range(start, n):
            if blocked[x]:
                continue
            changed = []
            for y in current:
                for z in range(x + 1, n):
                    if (y, x, z) in present:
                        blocked[z] += 1
                        changed.append(z)
            current.append(x)
            visit(current, x + 1)
            current.pop()
            for z in changed:
                blocked[z] -= 1

    visit([], 0)
    return answer


def degree_over_two(x):
    return x.bit_length() - 1


def residue(x, p):
    while x.bit_length() >= p.bit_length():
        x ^= p << (x.bit_length() - p.bit_length())
    return x


def field_modulus(h):
    for p in range(1 << h, 2 << h):
        if all(residue(p, q) for q in range(2, 2 << (h // 2))):
            return p
    raise AssertionError(h)


def multiply(a, b, p):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
    return residue(result, p)


def order_by_cost(n, independent):
    v = 1 << (n - 1).bit_length()
    h = degree_over_two(v)
    poly = field_modulus(h)
    weights = Counter(s[:3] for s in independent if len(s) >= 3)
    scores = []
    for a in range(1, v):
        places = [multiply(a, x, poly) for x in range(v)]
        assert len(set(places)) == v
        score = 0
        for tri, weight in weights.items():
            for shift in range(h + 1):
                blocks = len({places[x] >> shift for x in tri})
                score += weight * (2*(v >> shift)-1 if blocks == 1 else 2 if blocks == 2 else 0)
        scores.append((score, places))
    assert sum(score for score, _ in scores) <= (v-1)*4*(h+1)*sum(weights.values())
    score, places = min(scores)
    return score, sorted(range(n), key=places.__getitem__), places


class PaddedTriples:
    """Keep holes in the multiplication layout, and force their prefix bits to zero."""

    def __init__(self, places, actual_size, masks):
        self.n = len(places)
        self.k = 3
        self.complete = False
        self.actual_size = actual_size
        self.old = sorted(range(self.n), key=places.__getitem__)
        self.masks = masks

    def forbidden_extensions(self, coords, bits, stage):
        last = self.old[stage]
        if last >= self.actual_size:
            return 2
        i, j = coords
        if not i < j < stage:
            return 0
        a, b = self.old[i], self.old[j]
        if max(a, b) >= self.actual_size:
            return 0
        order = sorted(range(3), key=(a, b, last).__getitem__)
        mask = self.masks.get(tuple(sorted((a, b, last))), 0)
        flags = 0
        for new in range(2):
            values = (*bits, new)
            code = sum(values[index] << (2-pos) for pos, index in enumerate(order))
            flags |= ((mask >> code) & 1) << new
        return flags


def main():
    rng = Random(271127)
    cases = checked_sets = total_states = 0
    for n in range(3, 10):
        all_triples = list(combinations(range(n), 3))
        for shape in range(12):
            masks = {t: 1 << rng.randrange(8) for t in all_triples
                     if rng.randrange(7) >= shape % 5}
            if shape == 0:
                masks = {t: 1 << 7 for t in all_triples if t[-1] >= n//2}
            elif shape == 11:
                masks = {}
            independent = independent_sets(n, masks)
            brute = {tuple(i for i in range(n) if word >> i & 1) for word in range(1<<n)
                     if not any(all(word >> i & 1 for i in t) for t in masks)}
            assert set(independent) == brute
            score, order, places = order_by_cost(n, independent)
            assert order == [x for x in sorted(range(len(places)), key=places.__getitem__) if x < n]
            rows, states = solve(PaddedTriples(places, n, masks))
            assert all(not row[places[x]] for row in rows for x in range(n, len(places)))
            actual = {tuple(row[places[x]] for x in range(n)) for row in rows}
            expected = {a for a in product((0, 1), repeat=n) if all(
                not ((q >> (4*a[i]+2*a[j]+a[k])) & 1)
                for (i,j,k),q in masks.items())}
            assert actual == expected
            total_states += states
            checked_sets += len(independent)
            cases += 1
    print(f'{cases} partial support systems, {checked_sets:,} independent sets checked; {total_states:,} shared states in padded solver replays.')


if __name__ == '__main__':
    main()
