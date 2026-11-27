"""Check the deterministic path and transcript steps of the word-opcode example."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb
from random import Random


def ordered_graphs(n):
    choices = [[p for r in range(min(v, 2)+1) for p in combinations(range(v), r)]
               for v in range(n)]
    yield from product(*choices)


def residual_depth(graph, seeds):
    ending = []
    for v, parents in enumerate(graph):
        ending.append(0 if v in seeds else 1+max((ending[p] for p in parents), default=0))
    return max(ending)


def deliver_from_seeds(graph, seeds, cap):
    available = set(seeds)
    seen = set()
    for _ in range(cap):
        ready = {v for v, parents in enumerate(graph) if all(p in available for p in parents)}
        seen.update(ready)
        available.update(ready)
    return seen


def graph_tests():
    cases = bounds = masks = 0
    for graph in ordered_graphs(6):
        cases += 1
        n = len(graph)
        for seedmask in (0, *[1 << i for i in range(n)]):
            seeds = {i for i in range(n) if seedmask >> i & 1}
            depth = residual_depth(graph, seeds)
            for rounds in (1, 2, 3):
                seen = deliver_from_seeds(graph, seeds, rounds)
                assert len(set(range(n))-seen) >= max(0, depth-rounds)
                bounds += 1
        # Removing heads of edges whose most significant difference belongs
        # to the chosen set makes the ordinal projected onto other bits grow.
        h = (n-1).bit_length()
        for mask in range(1 << h):
            removed = {v for v, parents in enumerate(graph) for p in parents
                       if (1 << ((p ^ v).bit_length()-1)) & mask}
            assert residual_depth(graph, removed) <= 1 << (h-mask.bit_count())
            masks += 1
    return cases, bounds, masks


def active_keys(graph, labels):
    return tuple((v, tuple(labels[p] for p in parents)) for v, parents in enumerate(graph))


def schedule(graph, table, seed, advice, rounds):
    # The target graph has sources and real two-parent cells. Query values
    # include both label and flag, so changing a flag can steer future probes.
    rng = Random(seed)
    responses = []
    hits = set()
    querylog = []
    for r in range(rounds):
        batch = []
        for v, parents in enumerate(graph):
            data = []
            for p in parents:
                if responses and (v+r+advice) % 3 != 0:
                    k = (p+advice) % len(responses)
                    label, flag = responses[k]
                    data.append((label+flag) % 4)
                else:
                    data.append((rng.randrange(4)+advice+p) % 4)
            batch.append((v, tuple(data)))
        querylog.append(tuple(batch))
        responses = [table[key] for key in batch]
        hits.update(batch)
    return tuple(querylog), tuple(responses), hits


def planted_tests():
    graph = ((), (0,), (0, 1), (1, 2))
    universe = [(v, x) for v, parents in enumerate(graph) for x in product(range(4), repeat=len(parents))]
    rng = Random(4701)
    decoys = {cell: (rng.randrange(4), rng.randrange(2)) for cell in universe}
    trials = flips = guessed = 0
    for labels in product(range(4), repeat=len(graph)):
        active = active_keys(graph, labels)
        table = decoys.copy()
        table.update((key, (labels[i], 0)) for i, key in enumerate(active))
        for seed, advice in product(range(3), range(3)):
            log, final, seen = schedule(graph, table, seed, advice, 2)
            reveals = set()
            lucky = set()
            for batch in log:
                # Test operands throughout this batch before any correct
                # response in this batch is revealed.
                for v, data in batch:
                    for p, z in zip(graph[v], data):
                        if p not in reveals and labels[p] == z:
                            lucky.add(p)
                reveals.update(lucky)
                reveals.update(v for v, pair in enumerate(active) if pair in batch)
            missing = [v for v, key in enumerate(active) if key not in seen]
            assert len(missing) >= residual_depth(graph, lucky)-len(log)
            alt = table.copy()
            for v in missing:
                alt[active[v]] = (labels[v], 1)
            assert schedule(graph, alt, seed, advice, 2) == (log, final, seen)
            trials += 1
            flips += len(missing)
            guessed += len(lucky)
    return trials, flips, guessed


def sample_transfer():
    # Exact finite analogue of the miss-or-low-probability union bound.
    tapes = (frozenset(), frozenset({0}), frozenset({1, 2}),
             frozenset({1}), frozenset({2}))
    n = 3
    choices = [set(S) for k in range(n+1) for S in combinations(range(n), k)]
    m = 4
    hist = Counter()
    for block in product(tapes, repeat=m):
        observed = set().union(*block)
        for index, subset in enumerate(choices):
            hist[index] += observed.isdisjoint(subset)
    for i, subset in enumerate(choices):
        p = Fraction(sum(not t.isdisjoint(subset) for t in tapes), len(tapes))
        assert Fraction(hist[i], len(tapes)**m) == (1-p)**m
    return len(tapes)**m, len(choices)


def candidate_sets():
    # Maximally eager adaptive equality trials on unrevealed independent
    # labels. Count actual matches and compare with the elementary bound.
    n, alphabet, attempts = 3, 23, 4
    values = Counter()
    for labels in product(range(alphabet), repeat=n):
        used = [set() for _ in labels]
        hit = set()
        for step in range(attempts):
            left = [i for i in range(n) if i not in hit]
            if not left:
                break
            v = left[(step+len(hit)) % len(left)]
            guess = (3*step+2*sum(hit)) % alphabet
            while guess in used[v]:
                guess = (guess+1) % alphabet
            used[v].add(guess)
            if labels[v] == guess:
                hit.add(v)
        values[len(hit)] += 1
    for k in range(1, n+1):
        observed = Fraction(sum(v for i,v in values.items() if i >= k), alphabet**n)
        upper = Fraction(comb(attempts,k), (alphabet-attempts)**k)
        assert observed <= upper
    return alphabet**n, tuple(sorted(values.items()))


if __name__ == "__main__":
    print("graphs, surviving-path and removed-level checks:", *graph_tests())
    print("planted transcripts, simultaneous flag edits, fresh guesses:", *planted_tests())
    print("coin samples, exact missed subsets:", *sample_transfer())
    print("planted equality strings, discovery histogram:", *candidate_sets())
