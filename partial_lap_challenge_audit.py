"""Exhaust small backward witnesses with competing intervening rows in partial laps."""

from itertools import combinations, pairwise, product
from math import log2, sqrt


def row(n, j, i, state, word, bits):
    key = (i + j + state + bits[j * n + i]) % 3
    payload = word ^ bits[j * n + i] ^ (i % 2)
    return key, payload, state ^ payload


def certify(n, laps, width, bits, header):
    boundaries = [j * n + i for j in range(laps) for i in range(0, n, width)] + [n * laps]
    starts = dict(zip(boundaries, header, strict=True))
    sketches = {}
    certified = {}
    reference = {}
    ideal_memory = [0, 1, 0]
    unseen_skips = 0
    proposals = 0
    for j in range(laps):
        mutable_next = ideal_memory.copy()
        for i in range(n):
            t = j * n + i
            if i % width == 0:
                incoming = {(starts[t], frozenset())}
                true_state = starts[t]
            else:
                incoming = {(next_state, claims) for (_, _, next_state), claims in sketches[t - 1]}
                true_state = reference[t - 1][2]
            built = set()
            for state, past in incoming:
                key = row(n, j, i, state, 0, bits)[0]
                claims = [(ideal_initial()[key], -1, frozenset())]
                for u in range(j * n):
                    for (other_key, value, _), prior_claims in sketches[u]:
                        if key == other_key:
                            claims.append((value, u, prior_claims))
                for value, source, prior_claims in claims:
                    built.add((row(n, j, i, state, value, bits), past | prior_claims | {(j, key, source)}))
            sketches[t] = built
            good = set()
            for result, claims in built:
                # A challenge can name a read in ANY node of the sketch.
                # Its proposed intervening row must survive the lower-rank challenge game.
                if all(not any(a == key for u in range(source + 1, tier * n)
                               for a, _, _ in certified[u]) for tier, key, source in claims):
                    good.add(result)
                    unseen_skips += sum(source >= 0 and source // n < tier - 1 for tier, _, source in claims)
            proposals += len(built)
            certified[t] = good
            key = row(n, j, i, true_state, 0, bits)[0]
            reference[t] = row(n, j, i, true_state, ideal_memory[key], bits)
            mutable_next[key] = reference[t][1]
            assert good == {reference[t]}
        ideal_memory = mutable_next
    consistent = not header[0]
    for right in boundaries[1:]:
        consistent &= reference[right - 1][2] == starts[right]
    for j in range(laps):
        keys = [reference[j * n + i][0] for i in range(n)]
        consistent &= len(set(keys)) == len(keys)
    return consistent, proposals, unseen_skips


def ideal_initial():
    return 0, 1, 0


def eager(n, laps, width, bits):
    memory = list(ideal_initial())
    state = 0
    controls = []
    legal = True
    for j in range(laps):
        keys = []
        for i in range(n):
            if i % width == 0:
                controls.append(state)
            key = row(n, j, i, state, 0, bits)[0]
            key, memory[key], state = row(n, j, i, state, memory[key], bits)
            keys.append(key)
        legal &= len(keys) == len(set(keys))
    controls.append(state)
    return tuple(controls), legal


def audit_game():
    proposals = headers = survivors = skipped = 0
    for n, laps, width in ((2, 2, 1), (2, 3, 2)):
        for bits in product(range(2), repeat=n * laps):
            true_header, legal = eager(n, laps, width, bits)
            for header in product(range(2), repeat=len(true_header)):
                accepted, found, gaps = certify(n, laps, width, bits, header)
                assert accepted == (legal and header == true_header)
                proposals += found
                skipped += gaps
                headers += 1
                survivors += accepted
    assert skipped
    print(f'{proposals} structural sketches, {headers} header lists, {survivors} truthful survivors; {skipped} genuine skipped-lap uses')


def audit_scales():
    # x=log_2 T is used directly; no huge allocations.
    for x in (2**18, 2**24, 2**30, 2**36, 2**42):
        y = log2(x)
        overhead = 12
        A = 4 * overhead
        cap = max(1, int(0.05 * sqrt(x / y)))
        log_b = A * (cap + 1) * y
        elim = cap * (overhead * y + 1)
        assert cap * (log_b + 1) + elim < x * 0.6
        assert x - log_b + y + elim <= x - 20 * y
    # Every odd pair of consecutive visits in one lane is a different
    # necessary boundary of any partition into cold read-once intervals.
    for b, rounds in product((2, 4, 8, 16), (3, 6, 12)):
        slots = [[] for _ in range(b)]
        for r in range(rounds):
            for j in range(b):
                slots[j].append(r * b + j)
        edges = [set(range(a, z)) for a, z in pairwise(slots[0])]
        assert all(not x & y for x, y in combinations(edges, 2))
    print('growing-depth uniform elimination and disjoint boundary counts passed')


if __name__ == '__main__':
    audit_game()
    audit_scales()
