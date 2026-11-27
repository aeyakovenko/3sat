"""Finite tests for decoding whole snapshots on two independently completed inputs."""
from itertools import product
from collections import defaultdict


def epoch(data):
    # The start prefix has already observed positions 0 and 1.
    choices = list(range(2, 8))
    indices = []
    state = 1 + data[0] + 2*data[1]
    mem = [0]*4
    for _ in range(3):
        addr = choices.pop(state % len(choices))
        indices.append(addr)
        mem[(addr + state) % 4] = data[addr] + state % 3
        state = (2*state+data[addr]+addr) % 11
    return frozenset(indices), state % 3, tuple(mem)


def reconstruct_and_run(get, ctl, advice):
    # Full candidate may read data from either side and depends on the advice.
    mem = []
    for j in range(4):
        if advice & (1 << (2*j)):
            val = get((2*j+ctl) % 8)
        else:
            val = 0
        mem.append(val + ((advice >> (8+2*j)) & 3))
    sign = 0
    # This toy suffix probes all positions, in a data- and memory-dependent order;
    # its role here is to stress the routing, not exhibit a large cut rank.
    start = (ctl + sum(mem)) % 8
    for j in range(8):
        if j % 3 or get((start+j) % 8):
            sign ^= get((start+j+1) % 8)
    return tuple(mem), sign


def run_with_log(data, ctl, advice):
    probed = set()

    def get(i):
        probed.add(i)
        return data[i]

    return (*reconstruct_and_run(get, ctl, advice), probed)


def audit():
    samples = list(product(range(2), repeat=8))
    prefixes = {d: epoch(d) for d in samples}
    verified = 0
    changed_headers = 0
    by_prefix = defaultdict(list)
    for data in samples:
        by_prefix[(data[:2], prefixes[data], tuple((i,data[i]) for i in sorted(prefixes[data][0])))].append(data)
    for (past, (old, ctl, target), _), completions in by_prefix.items():
        for fill in samples[::11]:
            old_or_past = old | {0, 1}
            companion = tuple(completions[0][i] if i in old_or_past else fill[i] for i in range(8))
            assert companion in completions
            # Let the two headers use optional probes that depend on their own input.
            lowbit = 1 << (2*(sum(companion)%4))
            word = (sum(companion)%4*2+ctl)%8
            def header(low, value):
                base = tuple(x - (value if low & (1 << (2*j)) else 0) for j,x in enumerate(target))
                if any(x < 0 for x in base):
                    return sum(x << (8+2*j) for j,x in enumerate(target))
                return low | sum(x << (8+2*j) for j,x in enumerate(base))
            h2 = header(lowbit, companion[word])
            candidate, sign, queried = run_with_log(companion, ctl, h2)
            assert candidate == target
            flips = {i for i in old & queried if companion[i] != fill[i]}
            fake = tuple(past[i] if i < 2 else fill[i] ^ (i in flips) for i in range(8))
            assert run_with_log(fake, ctl, h2) == (candidate, sign, queried)
            outside = queried - {0, 1}
            unseen = set(range(2, 8)) - old
            exceptions = outside ^ unseen
            assert set(range(2, 8)) - (outside ^ exceptions) == old
            for original in completions:
                h1 = header(lowbit, original[word])
                assert run_with_log(original, ctl, h1)[0] == target
                changed_headers += h1 != h2
                verified += 1
    assert changed_headers > 0
    return verified, changed_headers


if __name__ == "__main__":
    pairs, different = audit()
    print(f"{pairs} original/companion snapshot pairs passed, {different} using different headers")
