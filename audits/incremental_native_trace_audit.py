"""Audit the ordered-access change-propagation simulator against full recomputation."""

from bisect import bisect_left, bisect_right
from collections import defaultdict
from random import Random


def step(t, regs, inp, get):
    a, b = regs
    phase = t % 11
    if phase in (0, 3, 8):
        space, i = "input", (t + a) % len(inp)
        value = inp[i]
        nxt = (value % 7, 0) if phase == 3 else (a, b ^ value)
        return regs, (space, i), "load", value, nxt
    if phase in (1, 7):
        i = (a + t) % 5
        value = get(i)
        return regs, ("work", i), "load", value, (a, b ^ value)
    if phase in (2, 5, 9):
        i, v = ((t % 5, 0) if phase == 5 else ((a + b) % 5, b & 7))
        return regs, ("work", i), "store", v, (a, b)
    return regs, None, "cpu", 0, ((0, 0) if phase in (4, 10) else (b % 7, a))


def full(inp, length):
    regs = (0, 0)
    mem = defaultdict(int)
    result = []
    for t in range(length):
        e = step(t, regs, inp, mem.__getitem__)
        if e[2] == "store":
            mem[e[1][1]] = e[3]
        regs = e[-1]
        result.append(e)
    return result


def update(old, inp, changed):
    accesses, stores = defaultdict(list), defaultdict(list)
    for t, e in enumerate(old):
        if e[1]:
            accesses[e[1]].append(t)
        if e[2] == "store":
            stores[e[1][1]].append(t)

    def reference(i, t):
        j = bisect_left(stores[i], t)
        return old[stores[i][j - 1]][3] if j else 0

    pending, delta = {}, {}

    def schedule(site, t):
        pending.pop(site, None)
        space, i = site
        if (space == "work" and i not in delta) or (space == "input" and i not in changed):
            return
        entries = accesses[site]
        j = bisect_right(entries, t)
        if j < len(entries):
            pending[site] = entries[j]

    for i in changed:
        schedule(("input", i), -1)
    t = simulated = discharges = 0
    regs = (0, 0)
    new = old.copy()
    while t < len(old):
        if regs == old[t][0]:
            target = min(pending.values(), default=len(old))
            assert target >= t
            if target == len(old):
                break
            t, regs = target, old[target][0]
        before = old[t]
        after = step(t, regs, inp, lambda i: delta.get(i, reference(i, t)))
        new[t] = after
        simulated += 1
        fix = {site[1] for _, site, op, _, _ in (before, after) if op == "store"}
        if before == after:
            assert before[2] == "store" and before[1][1] in delta
            discharges += 1
        for i in fix:
            pre = reference(i, t)
            new_val = (after[3] if after[2] == "store" and after[1][1] == i
                       else delta.get(i, pre))
            old_val = (before[3] if before[2] == "store" and before[1][1] == i else pre)
            if old_val == new_val:
                delta.pop(i, None)
            else:
                delta[i] = new_val
        for site in {("work", i) for i in fix} | ({before[1]} if before[1] else set()):
            schedule(site, t)
        t += 1
        regs = after[-1]
    distance = sum(a != b for a, b in zip(new, old))
    assert simulated == distance + discharges and discharges <= 2 * distance
    return new, distance, discharges


def main():
    rng = Random(6219380)
    checks = discharges = differences = 0
    for n in (7, 17, 33):
        inp = [rng.randrange(16) for _ in range(n)]
        old = full(inp, 91)
        for _ in range(700):
            edits = {rng.randrange(n): rng.randrange(16) for _ in range(rng.randrange(1, 5))}
            changed = {i for i, v in edits.items() if v != inp[i]}
            for i, v in edits.items():
                inp[i] = v
            new, d, clean = update(old, inp, changed)
            assert new == full(inp, len(old))
            old = new
            discharges += clean
            differences += d
            checks += 1
    print(f"{checks} trace repairs, {differences} differing slots, "
          f"{discharges} identical stores eliminating memory differences")


if __name__ == "__main__":
    main()
