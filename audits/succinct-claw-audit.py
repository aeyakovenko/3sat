"""Check dyadic conflict keys and a forward permutation of producer/load pairs."""

from itertools import product


def gap_cells(lo, hi, width):
    """At each size, only the first/last aligned block can be maximal."""
    result = set()
    for level in range(width + 1):
        size = 1 << level
        for index in {(lo + size - 1) // size, hi // size - 1}:
            start = index * size
            if start < lo or start + size > hi:
                continue
            parent = (index // 2) * (2 * size)
            if level < width and lo <= parent and parent + 2 * size <= hi:
                continue
            result.add((level, index))
    return result


def verify_logs():
    width = 2
    size = 1 << width
    alphabet = [None, *product(("s", "l"), range(2), range(2))]
    tested = candidates = good = 0
    for log in product(alphabet, repeat=size):
        memory = [0, 0]
        true = True
        loads = []
        store_keys = set()
        for t, op in enumerate(log):
            if op is None:
                continue
            kind, addr, bit = op
            if kind == "s":
                memory[addr] = bit
                for level in range(width + 1):
                    store_keys.add((addr, level, t >> level, bit))
            else:
                true &= memory[addr] == bit
                choices = [s + 1 for s in range(t) if log[s] == ("s", addr, bit)]
                if bit == 0:
                    choices.append(0)
                loads.append((t, addr, bit, choices))
        certifiable = False
        for cuts in product(*(rec[3] for rec in loads)):
            candidates += 1
            excluded = {(addr, level, node, 1 - bit)
                        for (t, addr, bit, _), cut in zip(loads, cuts)
                        for level, node in gap_cells(cut, t, width)}
            clean = store_keys.isdisjoint(excluded)
            assert clean == all(
                all(log[s] != ("s", addr, 1 - bit) for s in range(cut, t))
                for (t, addr, bit, _), cut in zip(loads, cuts))
            certifiable |= clean
        assert certifiable == true
        tested += 1
        good += int(true)
    return tested, candidates, good


def act(g, s):
    if s >= 5:
        return s
    if g == 0:
        return (s + 1) % 5
    return (1 - s) if s < 2 else s


def causal_image(rows):
    prev = 0
    encoded = []
    for g, s in rows:
        encoded.append((g, s ^ act(g, prev)))
        prev = s
    return tuple(encoded)


def check_inverse():
    domain = list(product(tuple(product(range(2), range(8))), repeat=3))
    image = [causal_image(x) for x in domain]
    assert len(set(image)) == len(domain)
    order = sorted(range(len(domain)), key=lambda t: image[t])
    addresses = sorted(domain)
    for rank, t in enumerate(order):
        assert causal_image(domain[t]) == addresses[rank]
    for generators in product(range(2), repeat=3):
        zero_image = tuple((g, 0) for g in generators)
        preimage = domain[order[addresses.index(zero_image)]]
        prev = 0
        for (g, state) in preimage:
            prev = act(g, prev)
            assert state == prev
    return len(domain)


def main():
    intervals = 0
    for width in range(8):
        for lo in range((1 << width) + 1):
            for hi in range(lo, (1 << width) + 1):
                cells = gap_cells(lo, hi, width)
                points = sorted(x for j, node in cells
                                for x in range(node << j, (node + 1) << j))
                assert points == list(range(lo, hi))
                assert all(sum(j == level for j, _ in cells) <= 2 for level in range(width + 1))
                intervals += 1
    tests, certificates, good = verify_logs()
    print(f"{intervals} exact dyadic interval covers; {tests} logs, "
          f"{certificates} anchor lists, {good} genuine logs")
    print(f"{check_inverse()} permutation inputs; all sorted producers and group prefixes agreed")


if __name__ == "__main__":
    main()
