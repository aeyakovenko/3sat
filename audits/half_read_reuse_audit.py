"""Test positive-label sign representations and the coupled completion at a native cut."""
from collections import Counter
from itertools import product
from random import Random


def suffix_trace(x, memory, y):
    """The cross-input and incoming-word queries both depend on prior replies."""
    path = []
    acc = y
    for j in range(6):
        if (j + y) % 3:
            address = (acc + j) % len(memory)
            label = ('work', address)
            value = memory[address]
        else:
            address = (acc + 2*j) % 4
            label = ('pin', address)
            value = (x >> address) & 1
        path.append((label, value))
        acc = (3*acc + value + j) % 29
        if j >= 3 and acc % 6 == 0:
            break
    return tuple(path), 1 if acc & 1 else -1


def check_signs():
    rng = Random(1731)
    n = 0
    for _ in range(60):
        memories = [tuple(rng.randrange(3) for _ in range(4)) for _ in range(16)]
        rows = [x for x in range(16) if rng.randrange(4)]
        for y in range(8):
            actual = {x: suffix_trace(x, memories[x], y) for x in rows}
            leaves = sorted(set(actual.values()), key=lambda leaf: tuple(v for _, v in leaf[0]))
            features = Counter()
            for j, (path, verdict) in enumerate(leaves):
                term = frozenset((address, value) for address, value in path if value)
                features[term] += verdict * (1 << j)
            for x in rows:
                def holds(term):
                    return all((memories[x][i] if tag == 'work' else (x >> i) & 1) == v
                               for (tag, i), v in term)
                score = sum(weight for term, weight in features.items() if holds(term))
                assert score * actual[x][1] > 0
                n += 1
    return n


def prefix(data):
    remaining = list(range(6))
    bits = []
    control = 1
    for j in range(3):
        address = remaining.pop(control % len(remaining))
        value = data[address]
        bits.append((address, value))
        control = 3*control + value + j
    return tuple(bits), control % 7


def suffix(data, start, memory):
    _, state = start
    pins, inherited, local = set(), set(), {}
    for j in range(10):
        a = (state + 3*j) % 6
        z = (state + j) % 5
        pins.add(a)
        if z not in local:
            inherited.add(z)
        w = local.get(z, memory.get(z, 0))
        state = (2*state + data[a] + w + j) % 19
        if state % 4 == 0:
            local[z] = state % 3
    return pins, inherited


def cheap(data):
    start = prefix(data)
    seen = {i for i, _ in start[0]}
    mem = {((i + 1) % 5): (b + i) % 3 for i, b in start[0]}
    pins, work = suffix(data, start, mem)
    return len(pins & seen) <= 2 and len(work) <= 4


def check_completion():
    samples = list(product(range(2), repeat=6))
    successes = 0
    joint = 0
    checked = 0
    for data in samples:
        start = prefix(data)
        seen = {i for i, _ in start[0]}
        mem = {((i + 1) % 5): (b + i) % 3 for i, b in start[0]}
        successes += cheap(data)
        for fill in samples:
            other = tuple(data[i] if i in seen else fill[i] for i in range(6))
            assert prefix(other) == start
            pins, incoming = suffix(other, start, mem)
            fix = {i for i in pins & seen if data[i] != fill[i]}
            oracle = {z: mem[z] for z in incoming if mem.get(z, 0)}
            decoded = tuple(b ^ (i in fix) for i, b in enumerate(fill))
            assert suffix(decoded, ((), start[1]), oracle) == (pins, incoming)
            # Unknown positions allowed by the omission guarantee are in the correction set.
            unseen = set(range(6)) - seen
            correction = pins ^ unseen
            assert pins ^ correction == unseen
            assert len(correction) == len(pins & seen) + len(unseen - pins)
            joint += cheap(data) and cheap(other)
            checked += 1
    assert successes and successes < len(samples)
    assert joint >= successes**2
    return checked, successes, joint


if __name__ == '__main__':
    print(f'{check_signs()} adaptive rows have the sign of their positive-label polynomial')
    pairs, hits, joint = check_completion()
    print(f'{pairs} coupled continuations reconstructed; joint mass numerator {joint} >= {hits}^2')
