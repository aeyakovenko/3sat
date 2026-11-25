"""Check the two marking schedules and prefix/suffix splices on finite word sets."""

from itertools import product
from random import Random


def orbit_prefixes(seeds, fun, target):
    covered = set()
    for a in seeds:
        local = set()
        while a in target and a not in local:
            local.add(a)
            a = fun[a]
        covered.update(local)
    assert covered == set(target)


def step(state, f, raw_destination):
    p, memory, written, seen = state
    x = memory[p]
    addr = x if raw_destination else p
    new = list(memory)
    new[addr] = f[x] if raw_destination else p
    return f[x], tuple(new), written | {addr}, seen | {p}


def start(p, memory):
    return p, memory, frozenset(), frozenset()


def trace(memory, p0, f, raw_destination):
    h = set(memory)
    seeds = {p0} | {f[x] for x in h}
    g = tuple(f[f[x]] for x in range(len(f))) if raw_destination else f
    state = start(p0, memory)
    past = set()
    longest = {s: () for s in seeds}
    seed = p0
    prefix = ()
    snapshot = None
    while state not in past:
        past.add(state)
        p, current, written, seen = state
        orbit_prefixes(seeds, g, seen)
        tips = {seq[-1] for seq in longest.values() if seq}
        assert seen == frozenset(v for seq in longest.values() for v in seq)
        if raw_destination:
            orbit_prefixes(h, f, written)
            assert seen - written <= tips
        else:
            assert written == seen
        for a in written:
            assert current[a] == (f[a] if raw_destination else a)
        if snapshot is None and len(seen) >= max(1, len(f) // 2):
            cached = tuple((a, current[a]) for a in sorted(seen-written))
            label = (p, written, seen, cached)
            snapshot = (label, len(past)-1, state)
        if p not in prefix:
            prefix += (p,)
            if len(prefix) > len(longest[seed]):
                longest[seed] = prefix
        was_unmarked = p not in written
        state = step(state, f, raw_destination)
        if was_unmarked:
            seed = state[0]
            prefix = ()
    return len(past), snapshot


def check_group(memories, p0, f, raw_destination):
    snapshots = {}
    states = splices = 0
    for memory in memories:
        length, snapshot = trace(memory, p0, f, raw_destination)
        states += length
        if snapshot is None:
            continue
        label, turns, state = snapshot
        snapshots.setdefault(label, []).append((memory, turns, state))
    for (_, _, seen, _), runs in snapshots.items():
        for left, turns, _ in runs:
            for right, _, expected in runs:
                if left == right:
                    continue
                hybrid = tuple(left[i] if i in seen else right[i] for i in range(len(f)))
                state = start(p0, hybrid)
                for _ in range(turns):
                    state = step(state, f, raw_destination)
                assert state == expected
                splices += 1
    return states, splices


def main():
    count = states = splices = 0
    rng = Random(84103)
    for q in (2, 3, 4):
        maps = list(product(range(q), repeat=q))
        funcs = maps if q < 4 else rng.sample(maps, 24)
        memories = maps if q < 4 else [m for m in maps if len(set(m)) <= 2]
        for f in funcs:
            for p0 in range(q):
                for raw_destination in (False, True):
                    newstates, newsplices = check_group(memories, p0, f, raw_destination)
                    states += newstates
                    splices += newsplices
                    count += len(memories)
    print(f"{count} traces; {states} distinct trace states; {splices} prefix/suffix splices")


if __name__ == "__main__":
    main()
