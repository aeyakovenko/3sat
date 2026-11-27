"""Independent finite checks for minimum positive complements of mixed affine flats."""

from collections import deque
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from math import prod
from random import Random


def greedy(q, v, dimensions):
    remaining = q ** v - 1
    for a in sorted(dimensions, reverse=True):
        power = q ** a
        while power > remaining:
            power //= q
        remaining -= power
    return remaining + 1


def uniform(q, v, a, r):
    parallel = q ** (v - a) - 1
    if r <= parallel:
        return (parallel + 1 - r) * q ** a
    levels, residue = divmod(r - parallel, q - 1)
    if levels >= a:
        return 1
    return (q - residue) * q ** (a - levels - 1)


class Geometry:
    def __init__(self, q, v):
        self.q, self.v = q, v
        self.points = list(product(range(q), repeat=v))
        self.index = {p: i for i, p in enumerate(self.points)}
        self.size = len(self.points)
        self.add = (lambda a, b: a ^ b) if q == 4 else (lambda a, b: (a + b) % q)
        def multiply(a, b):
            if q != 4:
                return a * b % q
            raw = (a if b & 1 else 0) ^ (a << 1 if b & 2 else 0)
            return raw ^ 7 if raw & 4 else raw  # x^2 = x + 1
        self.mul = multiply
        for a, b, c in product(range(q), repeat=3):
            assert multiply(a, self.add(b, c)) == self.add(multiply(a, b), multiply(a, c))
            assert multiply(a, multiply(b, c)) == multiply(multiply(a, b), c)
        assert all(any(multiply(a, b) == 1 for b in range(1, q)) for a in range(1, q))

    def index_sum(self, a, b):
        return self.index[tuple(self.add(x, y) for x, y in zip(self.points[a], self.points[b]))]

    def flats_avoiding_zero(self):
        # Enumerate linear subspaces by adjoining vectors, then translate every
        # subspace by every point outside it. Bit i-1 represents nonzero point i.
        q, v, n = self.q, self.v, self.size
        plus = [[self.index_sum(i, j) for j in range(n)] for i in range(n)]
        rays = [[self.index[tuple(self.mul(c, x) for x in p)] for c in range(q)]
                for p in self.points]
        linear = {frozenset({0})}
        result = []
        for a in range(v):
            masks = {
                sum(1 << (plus[b][i] - 1) for i in space)
                for space in linear for b in range(1, n) if b not in space
            }
            gaussian = prod(q ** v - q ** j for j in range(a)) // prod(
                q ** a - q ** j for j in range(a))
            assert len(masks) == gaussian * (q ** (v - a) - 1)
            assert all(mask.bit_count() == q ** a for mask in masks)
            result.append(masks)
            if a + 1 < v:
                linear = {frozenset(plus[i][j] for i in space for j in rays[b])
                          for space in linear for b in range(1, n) if b not in space}
        return result

    def elementary_maps(self, keep=None, fix_plane=False):
        indices = range(self.v)
        changeable = range(1 if fix_plane else 0, self.v)
        operations = [('swap', i, i+1, 0) for i in changeable if i+1 < self.v]
        operations += [('add', i, j, a) for i in changeable for j in indices if i != j
                       for a in range(1, self.q)]
        operations += [('scale', i, i, a) for i in changeable for a in range(2, self.q)]
        if keep is None:
            keep = tuple(range(1, self.size))
        local = {self.points[j]: i for i, j in enumerate(keep)}
        maps = []
        for kind, i, j, a in operations:
            perm = []
            for index in keep:
                p = self.points[index]
                new = list(p)
                if kind == 'swap':
                    new[i], new[j] = new[j], new[i]
                elif kind == 'add':
                    new[i] = self.add(new[i], self.mul(a, new[j]))
                else:
                    new[i] = self.mul(a, new[i])
                perm.append(local[tuple(new)])
            assert sorted(perm) == list(range(len(keep)))
            maps.append(perm)
        return maps


def orbit_quotient(geom, flats, keep=None, fix_plane=False):
    # GL fixes zero and preserves the *set* of flats in each dimension. Its
    # quotient only merges equivalent states of actual union enumeration.
    count = 1 << (geom.size - 1 if keep is None else len(keep))
    orbit = [-1] * count
    reps = []
    moves = []
    for perm in geom.elementary_maps(keep, fix_plane):
        table = [0] * count
        for mask in range(1, count):
            bit = mask & -mask
            table[mask] = table[mask ^ bit] | (1 << perm[bit.bit_length() - 1])
        assert all({table[f] for f in family} == family for family in flats)
        moves.append(table)
    for mask in range(count):
        if orbit[mask] >= 0:
            continue
        tag = len(reps)
        reps.append(mask)
        orbit[mask] = tag
        queue = deque([mask])
        while queue:
            old = queue.popleft()
            for move in moves:
                new = move[old]
                if orbit[new] < 0:
                    orbit[new] = tag
                    queue.append(new)
    transitions = [[sum(1 << idx for idx in {orbit[rep | f] for f in family})
                    for rep in reps] for family in flats]
    return orbit, reps, transitions


def bit_indices(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


def exhaust_geometry(q, v):
    geom = Geometry(q, v)
    flat_sets = geom.flats_avoiding_zero()
    orbit, reps, transitions = orbit_quotient(geom, flat_sets)

    @lru_cache(None)
    def advance(state, a):
        result = 0
        for idx in bit_indices(state):
            result |= transitions[a][idx]
        return result

    @lru_cache(None)
    def true_minimum(state):
        return geom.size - max(reps[j].bit_count() for j in bit_indices(state))

    # Profiles with any one dimension repeated >= n-1 times saturate:
    # every nonzero point belongs to a flat of that dimension missing zero.
    # Include the boundary count n-1 explicitly for each coordinate.
    for family in flat_sets:
        assert all(any(f >> j & 1 for f in family) for j in range(geom.size - 1))
    profiles = 0
    def visit(a, state, dimensions):
        nonlocal profiles
        if a == v:
            assert true_minimum(state) == greedy(q, v, dimensions), (q, v, dimensions)
            if len(set(dimensions)) <= 1:
                assert true_minimum(state) == uniform(q, v, dimensions[0] if dimensions else 0,
                                                     len(dimensions))
            profiles += 1
            return
        for repeat in range(geom.size):
            visit(a+1, state, dimensions + (a,) * repeat)
            state = advance(state, a)
    visit(0, 1 << orbit[0], ())

    # Independent raw unions without orbit reduction: check full *reachable
    # orbit sets*, not only their optimum, for all profiles of length <= 3.
    for r in range(4):
        for dimensions in combinations_with_replacement(range(v), r):
            unions = {0}
            state = 1 << orbit[0]
            for a in dimensions:
                unions = {old | f for old in unions for f in flat_sets[a]}
                state = advance(state, a)
            assert {orbit[mask] for mask in unions} == set(bit_indices(state))
    return profiles, len(reps)


def raw_three_steps(q, v):
    geom = Geometry(q, v)
    flats = geom.flats_avoiding_zero()
    checked = 0
    for r in range(4):
        for dimensions in combinations_with_replacement(range(v), r):
            frontier = {0}
            for a in dimensions:
                frontier = {s | f for s in frontier for f in flats[a]}
            actual = geom.size - max(s.bit_count() for s in frontier)
            assert actual == greedy(q, v, dimensions)
            checked += 1
    return checked


def exhaust_ternary_three_space():
    geom = Geometry(3, 3)
    flats = geom.flats_avoiding_zero()
    # For profiles having a plane, transitivity fixes the first plane x_0=1.
    # Its stabilizer acts on the remaining 17 nonzero points.
    keep = tuple(i for i in range(1, 27) if geom.points[i][0] != 1)
    reduced = [{sum(((f >> (i-1)) & 1) << j for j, i in enumerate(keep)) for f in family}
               for family in flats[1:]]
    orbit, reps, transitions = orbit_quotient(geom, reduced, keep, fix_plane=True)

    @lru_cache(None)
    def advance(state, a):
        result = 0
        for i in bit_indices(state):
            result |= transitions[a-1][i]
        return result

    # For line-only profiles the parallel class missing zero already attains
    # the volume bound through eight lines. Above that range optimize directly
    # using a depth-limited geometric cover search with an optional point budget.
    # Any first affine line missing zero is equivalent under GL(3,3).
    lines = flats[1]
    full = (1 << 26) - 1
    one_line = min(lines)
    parallel = {}
    for i, p in enumerate(geom.points[1:]):
        if p[:2] != (0, 0):
            parallel[p[:2]] = parallel.get(p[:2], 0) | (1 << i)
    assert len(parallel) == 8 and set(parallel.values()) <= lines
    assert sum(parallel.values()).bit_count() == 24
    through = {1 << i: [f for f in lines if f >> i & 1] for i in range(26)}

    @lru_cache(None)
    def can_leave(missing, budget, omitted):
        if missing.bit_count() <= omitted:
            return True
        if missing.bit_count() > 3 * budget + omitted:
            return False
        first = missing & -missing
        return (any(can_leave(missing & ~f, budget-1, omitted) for f in through[first])
                or (omitted > 0 and can_leave(missing ^ first, budget, omitted-1)))

    line_minimum = [27 - 3*r for r in range(9)]
    for r in range(9, 27):
        if line_minimum[-1] == 1:
            line_minimum.append(1)
        else:
            line_minimum.append(1 + next(k for k in range(27)
                                         if can_leave(full ^ one_line, r-1, k)))
    base = 1 << orbit[0]
    tested = 0
    for planes in range(27):
        state = base
        for line_count in range(27):
            if planes:
                ordinary = 18 - max(reps[i].bit_count() for i in bit_indices(state))
                state = advance(state, 1)
            else:
                ordinary = line_minimum[line_count]
            for points in range(27):
                # Independent singleton flats can fill arbitrary remaining
                # nonzero points. Zero itself was fixed as a survivor.
                actual = max(1, ordinary - points)
                dims = (0,) * points + (1,) * line_count + (2,) * planes
                assert actual == greedy(3, 3, dims), dims
                tested += 1
        if planes:
            base = advance(base, 2)
    return tested, len(reps)


def coin_optimum(q, v, dimensions):
    # Multiple-choice subset sum; allow every reduction to any smaller q-power
    # or to zero, in the original supplied order, with no greedy choices.
    capacity = q ** v - 1
    mask = (1 << (capacity + 1)) - 1
    found = 1
    for a in dimensions:
        next_found = found
        for j in range(a + 1):
            next_found |= found << (q ** j)
        found = next_found & mask
    return q ** v - (found.bit_length() - 1)


def coordinate_prefix_advancer(q, v):
    # Independently try actual axis-parallel flats in a lex-ordered geometry.
    # Continue only if their union with the already covered prefix stays a
    # prefix and leaves the final point uncovered. This computes constructions,
    # and makes no lower-bound claim about general flats.
    points = list(product(range(q), repeat=v))
    geometric = []
    for a in range(v):
        masks = set()
        for fixed in combinations(range(v), v - a):
            groups = {}
            for i, point in enumerate(points):
                key = tuple(point[j] for j in fixed)
                groups[key] = groups.get(key, 0) | (1 << i)
            masks.update(mask for mask in groups.values() if mask.bit_length() < len(points))
        geometric.append(masks)
    @lru_cache(None)
    def advance(covered, a):
        prefix = (1 << covered) - 1
        best = -1
        for f in geometric[a]:
            union = prefix | f
            if union & (union + 1) == 0:
                best = max(best, union.bit_length())
        assert best >= 0
        return best
    return advance


def arithmetic_and_construction_checks():
    rng = Random(18392)
    checked = 0
    for q, v in ((2, 6), (3, 4), (4, 3), (5, 3), (7, 3)):
        advance = coordinate_prefix_advancer(q, v)
        cases = set()
        for a in range(v):
            final = q ** (v-a) - 1 + a * (q-1)
            cases.update((a,) * r for r in range(final + 3))
        for r in range(9):
            cases.update(combinations_with_replacement(range(v), r))
        for _ in range(300):
            cases.add(tuple(sorted(rng.choices(range(v), k=rng.randrange(1, 2*v*(q-1)+1)))))
        for dimensions in sorted(cases):
            shuffled = list(dimensions)
            rng.shuffle(shuffled)
            actual_coins = coin_optimum(q, v, shuffled)
            covered = 0
            for a in reversed(dimensions):
                covered = advance(covered, a)
            assert q ** v - covered == actual_coins == greedy(q, v, dimensions)
            if len(set(dimensions)) <= 1:
                assert actual_coins == uniform(q, v, dimensions[0] if dimensions else 0,
                                               len(dimensions))
        checked += len(cases)
    return checked


def main():
    for q, v in ((2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (4, 2)):
        profiles, orbits = exhaust_geometry(q, v)
        print(f"AG({v},{q}): {profiles} exhaustive mixed profiles, {orbits} union orbits")
    print(f"AG(3,3): {raw_three_steps(3,3)} raw arbitrary-flat profiles through three flats")
    profiles, orbits = exhaust_ternary_three_space()
    print(f"AG(3,3): {profiles} exhaustive mixed profiles with {orbits} "
          "first-plane stabilizer orbits and independent line-cover search")
    print(f"{arithmetic_and_construction_checks()} larger profiles with exact coin DP "
          "and independently constructed geometric unions")


if __name__ == '__main__':
    main()
