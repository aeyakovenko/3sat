"""Find the minimum nonempty proper 3-CNF uniquely satisfied by zero,
allowing at most one clause per unordered variable triple. No SAT solver
is used. Running this file also checks all polarity shifts and a balanced
two-copy SAT/UNSAT pair with a single fresh cross-support clause.
"""

from functools import lru_cache
from itertools import combinations, permutations
from math import comb


WITNESS = ((-1, 2, 3), (1, -2, 4), (-1, -2, 5), (1, 3, -4), (1, 3, -5),
           (-1, 4, -5), (2, -3, 4), (2, -3, -5), (-2, -4, -5), (-3, -4, 5))


def search(t, budget):
    triples = list(combinations(range(t), 3))
    words = range(1 << t)
    local = [[sum(((x >> coord) & 1) << k for k, coord in enumerate(triple)) for x in words]
             for triple in triples]
    faces = [[sum(1 << x for x in words if row[x] == p) for p in range(8)] for row in local]
    unit = sum(1 << (1 << j) for j in range(t))
    one_zero = sum(1 << ((1 << t)-1-(1 << j)) for j in range(t))

    @lru_cache(None)
    def cover(holes, remaining, left):
        if not holes:
            return ()
        # Every missing unit word requires a separate weight-one pattern.
        # None can hit a one-zero word. A weight-two pattern hits one of
        # those words, and a weight-three pattern hits t-3 of them.
        slack = left - (holes & unit).bit_count()
        heavy = holes & one_zero
        if left == 0 or slack < 0 or heavy.bit_count() > slack*max(1, t-3):
            return None
        ids = [i for i in range(len(triples)) if remaining >> i & 1]
        gain = {i: max((mask & holes).bit_count() for mask in faces[i][1:]) for i in ids}
        if sum(sorted(gain.values(), reverse=True)[:left]) < holes.bit_count():
            return None
        # In every completion at least one unused support covers the chosen
        # hole. On that support its pattern must equal this word's projection.
        eligible = heavy or holes
        choices = min(([(i, local[i][x]) for i in ids if local[i][x]
                        and (slack or faces[i][local[i][x]] & holes & unit)]
                       for x in words if eligible >> x & 1), key=len)
        for i, p in sorted(choices, key=lambda ip: (holes & faces[ip[0]][ip[1]]).bit_count()-gain[ip[0]],
                           reverse=True):
            result = cover(holes & ~faces[i][p], remaining ^ (1 << i), left-1)
            if result is not None:
                return ((i, p),) + result
        return None

    # The all-ones global word requires a local 111 pattern. Permuting the
    # variables puts one such support on triple 0 while keeping zero planted.
    holes = ((1 << (1 << t))-2) & ~faces[0][7]
    choices = cover(holes, (1 << len(triples))-2, budget-1)
    result = None if choices is None else tuple(
        tuple(-(coord+1) if p >> k & 1 else coord+1 for k, coord in enumerate(triples[i]))
        for i, p in ((0, 7),) + choices)
    return result, cover.cache_info().misses


def support_checks(rows):
    supports = [tuple(sorted(abs(lit) for lit in row)) for row in rows]
    assert all(len(s) == len(set(s)) == 3 for s in supports) and len(set(supports)) == len(rows)
    positive = {x for row in rows for x in row if x > 0}
    negative = {-x for row in rows for x in row if x < 0}
    assert positive == negative  # no pure-variable simplification
    for row in rows:
        # Every single support allows seven out of eight local tuples, so
        # it forces neither a literal nor any nonconstant linear parity.
        denied = sum((lit < 0) << i for i, lit in enumerate(row))
        for mask in range(1, 8):
            assert {(mask & x).bit_count() % 2 for x in range(8) if x != denied} == {0, 1}


def truth_masks(rows):
    return [(sum(1 << (x-1) for x in row if x > 0), sum(1 << (-x-1) for x in row if x < 0))
            for row in rows]


def models(rows, t):
    masks = truth_masks(rows)
    return [x for x in range(1 << t) if all((x & pos) or (x & neg) != neg for pos, neg in masks)]


def signed_copy(rows, shift, offset=0):
    return tuple(tuple((abs(v)+offset) * ((-1 if v < 0 else 1) *
                       (-1 if shift >> (abs(v)-1) & 1 else 1)) for v in row) for row in rows)


def seven_and_above():
    # t>=9 needs t critical singleton patterns plus an all-ones pattern.
    # t=8 leaves just one other pattern after the eight critical clauses.
    assert 8-3 < 8
    # At t=7, one 111 clause and one weight-two clause jointly hit at
    # most 4+1 of the seven one-zero words. Thus BOTH must be 111.
    assert 7-3+1 < 7
    triples = list(combinations(range(7), 3))
    feasible = 0
    for a, b in combinations(triples, 2):
        if set(a) & set(b):
            continue  # zero at any shared coordinate avoids both 111 patterns
        feasible += 1
        holes = {tuple(sorted((i, j))) for i in a for j in b}
        assert len(holes) == 9  # all words zero at exactly this pair avoid both
        assert len(holes) > 7  # each remaining singleton pattern hits at most one pair
    assert feasible == 70


def main():
    assert all((comb(t, 3) << (t-3) if t >= 3 else 0) < (1 << t)-1 for t in range(1, 5))
    seven_and_above()
    for t in (5, 6):
        result, states = search(t, 9)
        assert result is None
        print(f't={t} slots<=9 exhaustive_states={states} no_cover')

    found, states = search(5, 10)
    for witness in (WITNESS, found):
        assert len(witness) == 10 and models(witness, 5) == [0]
        support_checks(witness)
    print(f't=5 slots=10 first_cover_states={states} direct_witness={WITNESS}')

    coordinate_tests = 0
    for reordering in permutations(range(1, 6)):
        renamed = tuple(tuple(reordering[abs(v)-1] * (-1 if v < 0 else 1) for v in row) for row in WITNESS)
        for shift in range(32):
            shifted = signed_copy(renamed, shift)
            assert models(shifted, 5) == [shift]
            coordinate_tests += 1

    pair_rows = 0
    for shift in range(32):
        opposite = 31 ^ shift
        positive = signed_copy(WITNESS, shift) + signed_copy(WITNESS, opposite, 5)
        target = shift | (opposite << 5)
        # Forbid just the target pattern on a genuinely unused mixed triple.
        mixed = tuple(-v if target >> (v-1) & 1 else v for v in (1, 2, 6))
        negative = positive + (mixed,)
        support_checks(positive)
        support_checks(negative)
        assert target.bit_count() == 5
        assert models(positive, 10) == [target] and models(negative, 10) == []
        pair_rows += 2*(1 << 10)
    print(f'polarity_and_coordinate_transforms={coordinate_tests} mixed_pair_truth_rows={pair_rows} '
          'minimum_variables=5 global_minimum_clauses=10')


if __name__ == '__main__':
    main()
