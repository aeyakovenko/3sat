"""Exhaust the finite memory checks used by the two single-run notes."""

from itertools import combinations, permutations, product


# A row is absent, or is (address, is_store, word).

def genuine(rows):
    memory = {}
    for row in rows:
        if row is None:
            continue
        address, store, word = row
        if store:
            memory[address] = word
        elif word != memory.get(address, 0):
            return False
    return True


def key(rows, time):
    row = rows[time]
    return (1, 0, time) if row is None else (0, row[0], time)


def sorted_passes(rows, ranks):
    previous_key = None
    previous_row = None
    for time in ranks:
        current_key = key(rows, time)
        if previous_key is not None and current_key <= previous_key:
            return False
        row = rows[time]
        if row is not None and not row[1]:
            expected = previous_row[2] if previous_row and previous_row[0] == row[0] else 0
            if row[2] != expected:
                return False
        previous_key, previous_row = current_key, row
    return True


def gf4_multiply(x, y):
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x & 4:
            x ^= 0b111
    return result


def field_hash(point, address):
    value = 0
    for place in reversed(range(3)):
        value = gf4_multiply(point, value) ^ (address >> place & 1)
    return value


def bucket_summary(events):
    incoming = None
    last_write = None
    for _, store, word in events:
        if store:
            last_write = word
        elif last_write is not None and word != last_write:
            return None
        elif last_write is None:
            if incoming is not None and incoming != word:
                return None
            incoming = word
    return incoming, last_write


def hashed_passes(rows, block_size, points):
    memory = {}
    for start in range(0, len(rows), block_size):
        events = [r for r in rows[start:start + block_size] if r is not None]
        addresses = {r[0] for r in events}
        reports = {}
        for point in points:
            buckets = {}
            for event in events:
                index = field_hash(point, event[0])
                buckets.setdefault(index, []).append(event)
            for entries in buckets.values():
                z = entries[0][0]
                if any(row[0] != z for row in entries):
                    continue
                summary = bucket_summary(entries)
                if summary is None:
                    return False
                assert z not in reports or reports[z] == summary
                reports[z] = summary
        if set(reports) != addresses:
            return False
        for z, (incoming, last_write) in reports.items():
            if incoming is not None and incoming != memory.get(z, 0):
                return False
            if last_write is not None:
                memory[z] = last_write
    return True


def incoming_addresses(rows, block_size):
    incoming = set()
    for start in range(0, len(rows), block_size):
        written = set()
        for row in rows[start:start + block_size]:
            if row is None:
                continue
            address, store, _ = row
            if store:
                written.add(address)
            elif address not in written:
                incoming.add(address)
    return incoming


def filtered_passes(rows, block_size, retained):
    kept = [row if row is not None and row[0] in retained else None for row in rows]
    if not hashed_passes(kept, block_size, (1,)):
        return False
    for index, row in enumerate(rows):
        if row is None or row[1] or row[0] in retained:
            continue
        start = index - index % block_size
        preceding = (r for r in reversed(rows[start:index]) if r is not None and r[0] == row[0] and r[1])
        last_store = next(preceding, None)
        if last_store is None or last_store[2] != row[2]:
            return False
    return True


def exercise():
    # Addresses 0 and 2 collide under h_0; h_1 separates them.
    alphabet = (None, *product((0, 2), (False, True), (0, 1)))
    ranks = list(product(range(4), repeat=4))
    lists = [(0,), (1,), (0, 1), (1, 0, 1)]
    accepted = rank_checks = bucket_checks = 0
    filter_checks = filter_passes = 0
    for rows in product(alphabet, repeat=4):
        authentic = genuine(rows)
        canonical = tuple(sorted(range(4), key=lambda t: key(rows, t)))
        for proposed in ranks:
            assert sorted_passes(rows, proposed) == (authentic and proposed == canonical)
            rank_checks += 1
        for block_size in (1, 2, 4):
            incoming = incoming_addresses(rows, block_size)
            for retained in (set(), {0}, {2}, {0, 2}):
                passed = filtered_passes(rows, block_size, retained)
                assert passed == (authentic and incoming <= retained)
                filter_checks += 1
                filter_passes += passed
            for points in lists:
                passes = hashed_passes(rows, block_size, points)
                assert not passes or authentic
                if 1 in points:
                    assert passes == authentic
                bucket_checks += 1
        accepted += authentic
    assert accepted > 0
    # Find address-wise coverage with every single hash colliding somewhere.
    example = None
    for addresses in combinations(range(8), 3):
        for points in combinations(range(4), 3):
            groups = [[field_hash(p, z) for z in addresses] for p in points]
            if all(len(set(group)) < 3 for group in groups) and all(
                any(group.count(group[j]) == 1 for group in groups) for j in range(3)
            ):
                example = addresses, points
                break
        if example:
            break
    assert example
    addresses, points = example
    for order in permutations(addresses):
        for store_flags in product((False, True), repeat=6):
            for values in product((0, 1), repeat=6):
                rows = list(zip((*addresses, *order), store_flags, values))
                assert hashed_passes(rows, 3, points) == genuine(rows)
                bucket_checks += 1
    print(f'{len(alphabet)**4} four-row logs, {accepted} valid, {rank_checks} rank checks')
    print(f'{bucket_checks} block checks; per-address isolation example {example}')
    print(f'{filter_checks} filter checks, {filter_passes} passed')


if __name__ == '__main__':
    exercise()
