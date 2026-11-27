"""Finite audit for random-order-equality-accesses.md, using one word per record."""

from fractions import Fraction
from itertools import combinations, permutations, product
from math import factorial


def checker(symbols, supply, record_trace=False):
    """A deterministic adaptive equality checker, supplied one physical slot at a time."""
    n = len(symbols)
    remaining = list(range(2 * n))
    layout = [None] * (2 * n)
    records = {}
    events = []
    memory = {}
    choose_right = False

    def log(operation, address):
        if record_trace:
            events.append((operation, address))

    def read_work(address):
        log('read', address)
        return memory.get(address, 0)

    def store(address, value):
        log('write', address)
        memory[address] = value

    while remaining:
        slot = remaining.pop(-1 if choose_right else 0)
        row = supply(slot)
        coordinate, side = divmod(row, 2)
        symbol = symbols[coordinate]
        log('input', slot)
        layout[slot] = row
        if records:
            old_slot = next(iter(records))
            log('input', old_slot)
            old_value = records[old_slot]
        else:
            old_value = 0
        records[slot] = symbol
        store(row, symbol)
        # Exercise explicit zero stores, overwritten values and unwritten default loads.
        store(2 * n, 0)
        assert read_work(2 * n) == read_work(2 * n + 1) == 0
        choose_right = bool((coordinate + side + old_value + symbol) % 2)

    assert all(read_work(2 * t) == read_work(2 * t + 1) for t in range(n))
    return tuple(layout), events


def split_count(rows, n):
    return sum((2 * t in rows) != (2 * t + 1 in rows) for t in range(n))


def audit_split_mean(n):
    for m in range(2 * n + 1):
        counts = [split_count(rows, n) for rows in combinations(range(2 * n), m)]
        assert Fraction(sum(counts), len(counts)) == Fraction(m * (2 * n - m), 2 * n - 1)


def audit_lifetimes(events):
    first_input = {}
    last_write = {}
    links = []
    for time, (op, addr) in enumerate(events):
        if op == 'input':
            if addr in first_input:
                links.append((first_input[addr], time, op, addr))
            else:
                first_input[addr] = time
        elif op == 'write':
            last_write[addr] = time
        elif addr in last_write:
            links.append((last_write[addr], time, op, addr))

    cuts = sorted(first_input.values())
    transfer_count = 0
    for cut in cuts:
        returned = set()
        previously_stored = {addr for op, addr in events[:cut + 1] if op == 'write'}
        stored_after = set()
        frozen_reads = set()
        for op, addr in events[cut + 1:]:
            if op == 'input' and first_input[addr] <= cut:
                returned.add(addr)
            elif op == 'write':
                stored_after.add(addr)
            elif op == 'read' and addr not in stored_after:
                frozen_reads.add(addr)
        transferred = frozen_reads & previously_stored
        crossing = {(op, addr) for origin, destination, op, addr in links
                    if origin <= cut < destination}
        assert crossing == ({('input', addr) for addr in returned}
                            | {('read', addr) for addr in transferred})
        transfer_count += len(crossing)
    lifetime_sum = sum(sum(origin <= cut < dest for cut in cuts)
                       for origin, dest, _, _ in links)
    assert transfer_count <= lifetime_sum


def audit_adaptive_layouts(n):
    size = 2 * n
    for symbols in product(range(2), repeat=n):
        layouts = set()
        for order in permutations(range(size)):
            stream = iter(order)
            to_trace = symbols == tuple(t % 2 for t in range(n))
            layout, events = checker(symbols, lambda _: next(stream), to_trace)
            assert layout not in layouts
            layouts.add(layout)
            inverse_order = []

            def static_read(slot):
                inverse_order.append(layout[slot])
                return layout[slot]

            static_layout, static_events = checker(symbols, static_read, to_trace)
            assert static_layout == layout and tuple(inverse_order) == order
            if to_trace:
                assert static_events == events
                audit_lifetimes(events)
        assert len(layouts) == factorial(size)
    return 2**n * factorial(size)


def audit_separator(universe_size):
    # Any incorrect candidate H that misses a shared address must fail the label checks.
    all_sets = range(1 << universe_size)
    for prefix, suffix, claimed in product(all_sets, repeat=3):
        if claimed & ~prefix:
            continue
        can_separate = any((mask & (prefix & ~claimed)) == 0
                           and ((~mask) & (suffix & ~claimed)) == 0 for mask in all_sets)
        assert can_separate == ((prefix & suffix & ~claimed) == 0)


def audit_biased_cover(universe_size):
    # Enumerate the iid measure on Boolean functions with exact rational weights.
    modes = range(1 << universe_size)
    for size in range(1, universe_size + 1):
        for local in range(1, size + 1):
            p = min(Fraction(1, 2), Fraction(local, size))
            weights = [p**mask.bit_count() * (1 - p)**(universe_size - mask.bit_count())
                       for mask in modes]
            assert sum(weights) == 1
            for common, rare in product(modes, repeat=2):
                if common & rare or (common | rare).bit_count() > size or rare.bit_count() > local:
                    continue
                probability = sum(weights[mask] for mask in modes
                                  if mask & common == 0 and mask & rare == rare)
                assert probability >= p**local * (1 - p)**size


if __name__ == '__main__':
    for pair_count in range(1, 7):
        audit_split_mean(pair_count)
    layouts = audit_adaptive_layouts(3)
    audit_separator(4)
    audit_biased_cover(4)
    print(f'{layouts} adaptive layout bijection cases; 720 traces audited cut by cut')
    print('Exact split means through 6 pairs; exhaustive 4-key separator and biased probability checks passed')
