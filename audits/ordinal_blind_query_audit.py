"""Finite checks for sampling a raw array and finding a failed parity test."""

from collections import Counter
from functools import cache
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, prod
from random import Random


def tables(dimension, alphabet):
    return list(product(range(alphabet), repeat=dimension))


def check_reader(queries, outputs, arrays, hidden_sets, alphabet):
    dimension = len(arrays[0])
    seen = Counter()
    for array in arrays:
        paths = []
        accepts = []
        for r in range(alphabet):
            i, successors = queries[r]
            value = array[i]
            path = [i]
            if successors is not None:
                j = successors[value]
                path.append(j)
                value = array[j]
            paths.append(set(path))
            accepts.append(bool(outputs[r] & (1 << value)))
        # This false-claim event includes every array on which this reader has
        # permissible fresh-challenge soundness (one accepting symbol at most).
        can_be_false = sum(accepts) <= 1
        for hidden in hidden_sets:
            outside = tuple(array[i] for i in range(dimension) if i not in hidden)
            key = hidden, outside
            if can_be_false and all(accepts[array[i]] and
                                    paths[array[i]].isdisjoint(hidden) for i in hidden):
                seen[key, 0] += 1
            if all(paths[array[i]] & hidden == {i} for i in hidden):
                seen[key, 1] += 1

    for ((hidden, _), kind), count in seen.items():
        size = len(hidden)
        if kind == 0:
            assert count <= 1  # (alphabet * sigma)**size, sigma = 1/alphabet
        else:
            assert count * size**size <= alphabet**size


def graph_audit():
    cases = 0
    dimension = 4
    for edges in product(range(-1, dimension), repeat=dimension):
        adj = [{j for j in range(dimension)
                if j != i and (edges[i] == j or edges[j] == i)}
               for i in range(dimension)]
        for self_type in [False, True]:
            for cutoff in range(dimension):
                candidates = [i for i in range(dimension)
                              if (edges[i] == i) == self_type and len(adj[i]) <= cutoff]
                for size in range(1, dimension + 1):
                    lower = prod(max(0, len(candidates) - t * (cutoff + 1)) for t in range(size))
                    actual = sum(all(b not in adj[a] for a, b in combinations(seq, 2))
                                 for seq in permutations(candidates, size))
                    assert actual >= lower
                    cases += 1
    return cases


def parity_audit(dimension):
    assignments = range(1 << dimension)
    all_cases = (1 << (1 << dimension)) - 1

    def truthset(mask):
        return sum(1 << x for x in assignments if (x & mask).bit_count() % 2)

    # Edges form an odd-syndrome cycle. Finite search only uses the inconsistency.
    rows = [(1 << i) | (1 << ((i + 1) % dimension)) for i in range(dimension)]
    violations = [truthset(row) for row in rows]
    violations[0] ^= all_cases
    depths = []
    for width in range(1, dimension + 1):
        probes = [truthset(mask) for mask in range(1, 1 << dimension)
                  if mask.bit_count() <= width]

        @cache
        def depth(domain):
            if any(domain & ~violation == 0 for violation in violations):
                return 0
            splits = {(min(domain & mask, domain & ~mask),
                       max(domain & mask, domain & ~mask)) for mask in probes}
            return 1 + min(max(depth(left), depth(right))
                           for left, right in splits if left and right)

        depths.append(depth(all_cases))
    assert depths[-1] == (dimension - 1).bit_length()
    return depths



def ghost_audit():
    random = Random(99309)
    configurations = 0
    for exponents in ((1,), (1, 1), (1, 2), (3, 1), (2, 2), (1, 1, 1)):
        size = 9
        groups = len(exponents)
        odd = [i for i, n in enumerate(exponents) if n % 2]
        for steps in (0, 1, 2):
            for _ in range(3):
                background = [random.randrange(size) for _ in range(size)]
                pairs = [random.sample(range(size), 2) for _ in exponents]
                count = hits = cancellations = 0
                target_probes = min(size, 2 * groups * steps)
                for places in permutations(range(size), groups):
                    for swaps in product(range(2), repeat=groups):
                        public = list(background)
                        for j, loc in enumerate(places):
                            public[loc] = pairs[j][swaps[j]]
                        used = set()

                        def test(challenge):
                            state = challenge
                            for _ in range(steps):
                                loc = (state + 2 * challenge) % size
                                used.add(loc)
                                state = (state + public[loc] + 3) % size
                            return state % 2

                        value = 1
                        for j, n in enumerate(exponents):
                            diff = test(pairs[j][0]) - test(pairs[j][1])
                            value *= ((1 - 2 * swaps[j]) * diff)**n
                        for loc in range(size):
                            if len(used) == target_probes:
                                break
                            used.add(loc)
                        count += 1
                        if all(places[j] in used for j in odd):
                            hits += 1
                        else:
                            cancellations += value
                assert cancellations == 0
                assert hits * comb(size, len(odd)) == count * comb(target_probes, len(odd))
                configurations += count
    bounds = 0
    for d in range(2, 6):
        for k in (2, 4, 6):
            odd_law = Counter(sum(n % 2 for n in Counter(seq).values())
                              for seq in product(range(d), repeat=k))
            for a in (Fraction(0), Fraction(1, 3), Fraction(2, 3), Fraction(1)):
                lhs = sum(count * a**o for o, count in odd_law.items()) / d**k
                bound = sum(comb(k, 2*t) * prod(range(1, 2*t, 2)) * a**(k-2*t) / d**t
                            for t in range(k // 2 + 1))
                assert lhs <= bound
                bounds += 1
    return configurations, bounds

def main():
    dimension = alphabet = 3
    arrays = tables(dimension, alphabet)
    hidden_sets = [frozenset(s) for s in combinations(range(dimension), 2)]
    one_read = list(product(range(dimension), range(1 << alphabet)))
    count = 0
    for scheme in product(one_read, repeat=alphabet):
        queries = [(index, None) for index, _ in scheme]
        outputs = [out for _, out in scheme]
        check_reader(queries, outputs, arrays, hidden_sets, alphabet)
        count += 1
    random = Random(46223)
    for _ in range(2048):
        queries = [(random.randrange(dimension),
                    tuple(random.randrange(dimension) for _ in range(alphabet)))
                   for _ in range(alphabet)]
        outputs = [random.randrange(1 << alphabet) for _ in range(alphabet)]
        check_reader(queries, outputs, arrays, hidden_sets, alphabet)
    ghost_cases, matching_bounds = ghost_audit()
    print(f'{ghost_cases} hidden-address/swap configurations, {matching_bounds} moment matching bounds.')
    graph_cases = graph_audit()
    depths = [parity_audit(m) for m in (3, 4, 5)]
    print(f'{count} one-read and 2048 adaptive two-read verifiers checked on all arrays '
          'and hidden pairs.')
    print(f'{graph_cases} graph packing counts; optimal cycle-search depths by parity width {depths}.')


if __name__ == '__main__':
    main()
