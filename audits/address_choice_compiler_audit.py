"""Check a guarded address-set compiler and the disjoint hard-list restrictions.

The compiler evaluates all inputs in parallel using Boolean gate truth tables.
Its writable words have a new gated version for each allowed write event.
The reference interpreter uses one mutable dictionary per physical input.
"""
from itertools import permutations, product


WIDTH = 2
WORDS = range(1 << WIDTH)
INPUTS = tuple(product(WORDS, repeat=3))
ONES = (1 << len(INPUTS)) - 1
ZERO = (0,) * WIDTH


def bits(value):
    return tuple(ONES if value >> j & 1 else 0 for j in range(WIDTH))


def bit_xor(x, y):
    return tuple(a ^ b for a, b in zip(x, y))


def mux(select, yes, no):
    return tuple((select & a) | ((ONES ^ select) & b) for a, b in zip(yes, no))


def eq_constant(x, value):
    gate = ONES
    for pos, column in enumerate(x):
        gate &= column if value >> pos & 1 else ONES ^ column
    return gate


def reference(words):
    memory = {}
    history = []

    def read(bank, addr):
        history.append((bank, addr))
        return words[addr] if bank == "input" else memory.get(addr, 0)

    def write(addr, value):
        history.append(("work", addr))
        memory[addr] = value

    a = read("input", 0)
    b = read("input", 1 + (a & 1))
    write(a, b)
    if a & 2:
        write(b, a)
    else:
        history.append(None)
    c = read("work", a ^ b)
    if c & 1:
        write(b ^ a, b ^ 1)
        d = 0
    else:
        d = read("input", 1)
    out = read("work", b ^ d)
    return history, out


def guarded(supports):
    input_wires = [tuple(sum(((word[pos] >> j) & 1) << ix
                             for ix, word in enumerate(INPUTS)) for j in range(WIDTH))
                   for pos in range(3)]
    version = {}
    live = ONES
    first = []
    slot = 0

    def access(inp_read, work_read, work_write, address, payload=ZERO):
        nonlocal live, slot
        old_live = live
        computed = ZERO
        matched = 0
        for bank, addr in sorted(supports[slot]):
            same = eq_constant(address, addr)
            read_on = same & (inp_read if bank == "input" else work_read)
            write_on = same & work_write if bank == "work" else 0
            matched |= read_on | write_on
            old = (input_wires[addr] if bank == "input" else version.get(addr, ZERO))
            computed = tuple(a | (read_on & b) for a, b in zip(computed, old))
            if bank == "work":
                version[addr] = mux(write_on & old_live, payload, old)
        enabled = inp_read | work_read | work_write
        fail = old_live & enabled & (ONES ^ matched)
        first.append(fail)
        live ^= fail
        slot += 1
        return computed

    a = access(ONES, 0, 0, bits(0))
    source = mux(a[0], bits(2), bits(1))
    b = access(ONES, 0, 0, source)
    access(0, 0, ONES, a, b)
    access(0, 0, a[1], b, a)
    c = access(0, ONES, 0, bit_xor(a, b))
    sel = c[0]
    addr = mux(sel, bit_xor(a, b), bits(1))
    d = access(ONES ^ sel, 0, sel, addr, bit_xor(b, bits(1)))
    out = access(0, ONES, 0, bit_xor(b, d))
    return first, live, out


def main():
    actual = [reference(words) for words in INPUTS]
    full = [{hist[t] for hist, _ in actual if hist[t] is not None} for t in range(7)]
    tested = 0

    def test(supports):
        nonlocal tested
        first, survivors, output = guarded(supports)
        for ix, (hist, val) in enumerate(actual):
            miss = next((t for t, item in enumerate(hist)
                         if item is not None and item not in supports[t]), None)
            flags = [t for t, column in enumerate(first) if column >> ix & 1]
            assert flags == ([] if miss is None else [miss])
            assert bool(survivors >> ix & 1) == (miss is None)
            if miss is None:
                assert val == sum(((col >> ix) & 1) << j for j, col in enumerate(output))
        tested += 1

    test(full)
    events = [(t, item) for t, cells in enumerate(full) for item in cells]
    for event in events:
        for other in events:
            supports = [set(cells) for cells in full]
            for t, cell in (event, other):
                supports[t].discard(cell)
            test(supports)
    print(f"{tested} calendars × {len(INPUTS)} RAM inputs: exact first escapes and surviving outputs.")

    # Width 2 contains a width 1 list in its first two rows. Its outer
    # universe has 16 words, its inner universe 4, leaving 12 tail symbols.
    seen = set()
    for tail in permutations(range(4, 16), 2):
        for prefix in product(range(4), repeat=2):
            source = prefix + tail
            assert source not in seen
            seen.add(source)
            assert (len(set(source)) < 4) == (prefix[0] == prefix[1])
    assert len(seen) == 12 * 11 * 16
    print("132 disjoint tails, 2,112 distinct lists: every verdict equals its embedded list verdict.")


if __name__ == "__main__":
    main()
