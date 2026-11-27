"""Check the epoch replay, cut-rank accounting and square-tile matching on finite cases."""

from collections import defaultdict
from itertools import permutations
from math import isqrt
from random import Random

from expander_cut_sign_audit import graph, rank


def trace(z, controller=("left", 0, 0, 0, 0), memory=(1, 0, 1, 0)):
    """Yield action, coordinate and post-state on an adaptive four-pair inner product."""
    while True:
        op, i, swap, bit, parity = controller
        if op == "halt":
            return
        order = (0, 2, 1, 3) if swap else (0, 1, 2, 3)
        if op == "left":
            a = order[i]
            bit = z >> a & 1
            if i == 0:
                swap = bit
            tag, controller = "input", ("write", i, swap, bit, parity)
        elif op == "write":
            a = order[i]
            memory = memory[:a] + (bit,) + memory[a + 1:]
            tag = "store"
            controller = ("left", i + 1, swap, 0, parity) if i < 3 else ("right", 0, 0, 0, parity)
        elif op == "right":
            a = i + 4
            tag = "input"
            if z >> a & 1:
                controller = ("read", i, 0, 0, parity)
            else:
                controller = ("right", i + 1, 0, 0, parity) if i < 3 else ("halt", 0, 0, 0, parity)
        else:
            assert op == "read"
            a = i
            tag = "load"
            parity ^= memory[a]
            controller = ("right", i + 1, 0, 0, parity) if i < 3 else ("halt", 0, 0, 0, parity)
        yield tag, a, controller, memory


def mask(indices):
    return sum(1 << i for i in indices)


def epoch(z, index, width):
    events = list(trace(z))
    initial = (("left", 0, 0, 0, 0), (1, 0, 1, 0))
    cuts = [0] + [i + 1 for i, e in enumerate(events) if e[0] == "input"]
    lo, hi = cuts[width * index], cuts[width * (index + 1)]
    c0, m0 = events[lo - 1][2:] if lo else initial
    c1, m1 = events[hi - 1][2:]
    past = set(a for op, a, *_ in events[:lo] if op == "input")
    born = set(a for op, a, *_ in events[lo:hi] if op == "input") - past
    retrieved = []
    overwritten = set()
    for i in range(hi, len(events)):
        op, a, *_ = events[i]
        if op == "input" and a in born or op == "load" and a not in overwritten and m0[a] != m1[a]:
            retrieved.append(i)
        if op == "store":
            overwritten.add(a)
    return past, born, c0, c1, m0, m1, retrieved, events[hi:]


def audit_companions():
    count = 0
    for width in (1, 2):
        for idx in range(4 // width):
            for z in range(256):
                past, born, _, c, baseline, _, actual, suffix = epoch(z, idx, width)
                predictive = list(trace(z & ~mask(born), c, baseline))
                pin_trigger = any(e[0] == "input" and e[1] in born for e in predictive)
                incoming = set()
                local = set()
                for op, a, *_ in predictive:
                    if op == "store":
                        local.add(a)
                    elif op == "load" and a not in local:
                        incoming.add(a)
                end_mem = epoch(z, idx, width)[5]
                differences = {i for i in range(len(baseline)) if end_mem[i] != baseline[i]}
                hits = 1 if pin_trigger else len(differences & incoming)
                assert bool(hits) == bool(actual) and hits <= 1 + len(differences)
                if not actual:
                    assert [(e[0], e[1], e[2]) for e in predictive] == [e[:3] for e in suffix]
                for fill in (0, 23, 89, 170, 255):
                    fixed = mask(past | born)
                    companion = (z & fixed) | (fill & ~fixed)
                    other = epoch(companion, idx, width)
                    assert other[:6] == epoch(z, idx, width)[:6]
                    if other[6]:
                        continue
                    simulated = list(trace((z & mask(past)) | (fill & ~mask(past)), c, baseline))
                    assert [e[:3] for e in simulated] == [e[:3] for e in other[-1]]
                    read_set = {e[1] for e in simulated if e[0] == "input"}
                    assert set(range(8)) - past - read_set == born
                    count += 1
    for z in range(256):
        events = list(trace(z))
        assert events[-1][2][-1] == (((z >> 4) & z).bit_count() % 2)
        for width in (1, 2):
            owners = set()
            for idx in range(4 // width):
                reads = set(epoch(z, idx, width)[6])
                assert owners.isdisjoint(reads)
                owners |= reads
    return count


def audit_rank():
    n = 8
    adj = graph(n)
    allbits = (1 << n) - 1
    count = 0
    for order in permutations(range(n), n // 2):
        right = allbits ^ mask(order)
        total = rank([~adj[i] & right for i in order])
        for width in (1, 2, 3, 4):
            ranks = []
            seen = 0
            for end in range(width, len(order) + 1, width):
                new = order[end - width:end]
                seen |= mask(new)
                ranks.append(rank([~adj[i] & (allbits ^ seen) for i in new]))
            assert total <= (len(order) % width) + sum(ranks)
            count += 1
    return count


def audit_bias():
    size = 10
    adj = graph(size)
    full = (1 << size) - 1
    verdict = [sum(((~adj[v]) & z & ((1 << v) - 1)).bit_count()
                   for v in range(size) if z >> v & 1) % 2 for z in range(1 << size)]
    count = 0
    for pins in range(1 << size):
        if pins.bit_count() > size // 2:
            continue
        free = full ^ pins
        r = rank([(~(adj[i] | (1 << i))) & free for i in range(size) if free >> i & 1])
        sums = defaultdict(int)
        for z, out in enumerate(verdict):
            sums[z & pins] += 1 - 2 * out
        assert (r + 1) * 9 >= free.bit_count()
        for total in sums.values():
            assert total * total * (1 << r) <= 1 << (2 * free.bit_count())
            count += 1
    return count


def audit_tiles(size, block, trials, rng):
    side = 2 * (isqrt(size) // 2)
    adj = graph(size)
    cells = defaultdict(list)
    for i in range(side):
        for j in range(side):
            cells[i // block, j // block].append(side * i + j)

    def location(v):
        i, j = divmod(v, side)
        return (i // block, j // block), block * (i % block) + j % block

    edges = defaultdict(list)
    neighbors = {a: {a} for a in cells}
    for v in range(side * side):
        v_tile, vi = location(v)
        others = adj[v]
        while others:
            low = others & -others
            w = low.bit_length() - 1
            others ^= low
            w_tile, wi = location(w)
            neighbors[v_tile].add(w_tile)
            if v < w:
                edges[v_tile, w_tile].append((vi, wi))
    assert max(map(len, neighbors.values())) <= 81
    for a, targets in neighbors.items():
        assert all(a in neighbors[b] for b in targets)
    for trial in range(trials):
        z = trial if trials == 1 << size else rng.getrandbits(size)
        words = {}
        for a in cells:
            packet = 1 << (block * block)
            for v in cells[a]:
                packet |= ((z >> v) & 1) << location(v)[1]
            for b in neighbors[a]:
                assert (a, b) not in words
                words[a, b] = packet
        sparse = 0
        for b in cells:
            own = words.pop((b, b))
            for a in neighbors[b]:
                packet = own if a == b else words.pop((a, b))
                for vi, wi in edges[b, a]:
                    sparse ^= (own >> vi) & (packet >> wi) & 1
        assert not words
        ones = z.bit_count()
        verdict = (ones * (ones - 1) // 2 & 1) ^ sparse
        direct = sum(((~adj[v]) & z & ((1 << v) - 1)).bit_count()
                     for v in range(size) if (z >> v) & 1) % 2
        assert direct == verdict
    return trials, max(map(len, neighbors.values()))


def main():
    rng = Random(62803)
    companions = audit_companions()
    ranks = audit_rank()
    bias = audit_bias()
    tile_checks = [audit_tiles(size, block, trials, rng) for size, block, trials in
                   ((8, 1, 256), (10, 2, 1024), (36, 4, 180),
                    (154, 4, 100), (900, 8, 20), (1024, 2, 12))]
    print(f"{companions} retrieval-free companions replayed; {ranks} epoch-rank sums checked")
    print(f"{bias} sign biases on pinned subcubes checked")
    print(f"{sum(n for n, _ in tile_checks)} exact tile verdicts; "
          f"largest observed tile list {max(d for _, d in tile_checks)}")


if __name__ == "__main__":
    main()
