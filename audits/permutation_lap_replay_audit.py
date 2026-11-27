"""Exact local defect certificates in two/three laps, and the butterfly path obstruction."""

from functools import lru_cache
from itertools import combinations, pairwise, product
from math import ceil, log2
from random import Random


def step(n, lap, i, state, old, bits, damaged):
    mode, carry = divmod(state, 2)
    address = (i + mode + lap) % n
    if damaged == 'outside' and lap == 1 and i == n - 1:
        address = n
    if damaged == 'repeat' and lap == 1 and i == n - 1:
        address = (mode + lap) % n
    value = old ^ bits[lap * n + i] ^ mode
    carry ^= value
    if i + 1 == n:
        mode = carry
    return address, value, 2 * mode + carry


def first_address(n, lap, i, state, damaged):
    # The choice depends on beginning-of-lap state, itself derived from previous contents.
    return step(n, lap, i, state, 0, [0] * (n * (lap + 1)), damaged)[0]


def boundaries(n, laps, width):
    return [j * n + i for j in range(laps) for i in range(0, n, width)] + [n * laps]


def actual(n, laps, bits, damaged):
    memory = [0] * (n + 1)
    state = 0
    states = [state]
    permuted = True
    for j in range(laps):
        addresses = []
        for i in range(n):
            address = first_address(n, j, i, state, damaged)
            _, value, state = step(n, j, i, state, memory[address], bits, damaged)
            addresses.append(address)
            memory[address] = value
            states.append(state)
        permuted &= sorted(addresses) == list(range(n))
    return states, permuted


def no_defect(n, laps, width, bits, headers, damaged):
    bounds = boundaries(n, laps, width)
    raw = dict(zip(bounds, headers, strict=True))
    if raw[0]:
        return False

    @lru_cache(None)
    def possible(j, i):
        if i % width == 0:
            incoming = {raw[j * n + i]}
        else:
            incoming = {next_state for _, _, next_state in possible(j, i - 1)}
        rows = set()
        for state in incoming:
            addr = first_address(n, j, i, state, damaged)
            if not 0 <= addr < n:
                # An address defect is visible before any missing-predecessor guess.
                rows.add((addr, 0, state))
                continue
            if j == 0:
                words = {0}
            else:
                words = {payload for prev in range(n) for a, payload, _ in possible(j - 1, prev)
                         if a == addr}
            rows.update(step(n, j, i, state, v, bits, damaged) for v in words)
        return rows

    for start, stop in pairwise(bounds):
        j, i = divmod(stop - 1, n)
        if any(next_state != raw[stop] for _, _, next_state in possible(j, i)):
            return False
        assert start < stop
    for j in range(laps):
        events = [{a for a, _, _ in possible(j, i)} for i in range(n)]
        if any(a not in range(n) for event in events for a in event):
            return False
        if any(first & second for first, second in combinations(events, 2)):
            return False
    return True


def audit_headers():
    candidates = 0
    passed = 0
    for n, laps, width in ((2, 2, 1), (3, 2, 2), (2, 3, 2)):
        bounds = boundaries(n, laps, width)
        for bits in product(range(2), repeat=n * laps):
            for damaged in ('valid', 'repeat', 'outside'):
                trace, legal = actual(n, laps, bits, damaged)
                true_header = tuple(trace[i] for i in bounds)
                for suffix in product(range(4), repeat=len(bounds) - 1):
                    header = (0,) + suffix
                    accepted = no_defect(n, laps, width, bits, header, damaged)
                    assert accepted == (legal and header == true_header)
                    passed += accepted
                    candidates += 1
    print(f'{candidates} proposed checkpoint lists, {passed} defect-free genuine runs')


def butterfly_path(n, source, target):
    """After stage j, the low j bits come from the target and the rest from the source."""
    return [((source & ~(2**j - 1)) | (target & (2**j - 1))) for j in range(n.bit_length())]


def hadamard(inputs):
    result = inputs.copy()
    levels = [result.copy()]
    for j in range(len(inputs).bit_length() - 1):
        span = 1 << j
        for base in range(0, len(inputs), 2 * span):
            for i in range(base, base + span):
                x, y = result[i], result[i + span]
                result[i], result[i + span] = (x + y) % 3, (x - y) % 3
        levels.append(result.copy())
    return levels


def audit_butterflies():
    rng = Random(941362)
    samples = 0
    for n in (4, 8, 16):
        d = n.bit_length() - 1
        vertices = list(product(range(d + 1), range(n)))
        paths = {(s, r): frozenset(enumerate(butterfly_path(n, s, r))) for s, r in product(range(n), repeat=2)}
        assert all(sum(v in path for path in paths.values()) == n for v in vertices)
        changes = []
        for source in range(n):
            bits = [0] * n
            bits[source] = 1
            changes.append(hadamard(bits))
        for _ in range(200):
            saved = set(rng.sample(vertices, rng.randrange(n)))
            counts = [sum(not saved & paths[s, r] for s in range(n)) for r in range(n)]
            r = max(range(n), key=counts.__getitem__)
            assert counts[r] >= n - len(saved)
            ancestors = set.union(*(set(paths[s, r]) for s in range(n)))
            for s in range(n):
                if not saved & paths[s, r]:
                    assert changes[s][d][r] != 0
                    assert all(not changes[s][j][u] for j, u in saved & ancestors)
            samples += 1
    print(f'{samples} arbitrary marker sets passed explicit cone sensitivity over F3')


def clock_examples():
    for stages in (1, 2, 3, 7, 15):
        # T = 2^k, B = T^(1/(L+1)), ignoring genuine logarithmic and constant factors.
        bits = 240
        bbits = ceil(bits / (stages + 1))
        outer, inner = bits - bbits, stages * bbits
        assert max(outer, inner) <= bits * stages / (stages + 1) + stages
    # Exact exponent-level test for the polylogarithmic choice in the manuscript.
    for e in (256, 1024, 4096, 65536):
        exponent = 3
        q = int(e // (4 * (exponent + 1) * log2(e)))
        assert q * (1 + exponent * log2(e)) <= e / 3
    print('fixed and growing lap clock inequalities checked')


if __name__ == '__main__':
    audit_headers()
    audit_butterflies()
    clock_examples()
