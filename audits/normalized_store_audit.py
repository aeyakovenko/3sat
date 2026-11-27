"""Check prefix-frozen digits, dense high slots, and monotonicity on complete small traces."""

from collections import Counter
from bisect import bisect_left
from itertools import product


class EventTable:
    def __init__(self, events):
        self.events = tuple(events)
        assert all(left[0] < right[0] for left, right in zip(events, events[1:]))
        self.keys = sorted((slot, time) for time, slot in events)
        self.counts = []
        for i, (slot, _) in enumerate(self.keys):
            same_slot = i > 0 and self.keys[i-1][0] == slot
            self.counts.append(self.counts[-1] + 1 if same_slot else 1)

    def certified_read(self, slot, time, cut):
        query = slot, time
        assert 0 <= cut <= len(self.keys)
        assert cut == 0 or self.keys[cut-1] < query
        assert cut == len(self.keys) or query <= self.keys[cut]
        if cut > 0 and self.keys[cut-1][0] == slot:
            return self.counts[cut-1]
        return 0

    def read(self, slot, time):
        return self.certified_read(slot, time, bisect_left(self.keys, (slot, time)))


class VersionedMemory:
    def __init__(self, low_radix, low_depth, high_radix, high_depth, table=None):
        self.low_radix = low_radix
        self.low_depth = low_depth
        self.block = low_radix ** low_depth
        self.high_radix = high_radix
        self.high_depth = high_depth
        self.low = {}
        self.slots = {}
        self.arena = []
        self.payload = {}
        self.high_updates = 0
        self.downward = 0
        self.writes_per_slot = Counter()
        self.table = table
        self.events = []

    def digit(self, bank, key):
        if bank == 'low':
            mask = self.low.get(key, 0)
            assert mask == (1 << mask.bit_count()) - 1
            return mask.bit_count()
        if key not in self.slots:
            return 0
        slot = self.slots[key]
        if self.table is not None:
            return self.table.read(slot, len(self.payload) + 1)
        return self.arena[slot]

    def read_number(self, bank, prefix, radix, depth):
        value = 0
        for level in reversed(range(depth)):
            digit = self.digit(bank, (prefix, level, value))
            assert 0 <= digit < radix
            value = radix * value + digit
        return value

    def increment(self, bank, prefix, old, radix, depth):
        for level in range(depth):
            higher, digit = divmod(old, radix)
            if digit < radix - 1:
                key = prefix, level, higher
                assert self.digit(bank, key) == digit
                if bank == 'low':
                    before = self.low.get(key, 0)
                    self.low[key] = 2 * before + 1
                    assert self.low[key] & before == before
                    assert (before ^ self.low[key]).bit_count() == 1
                else:
                    if key not in self.slots:
                        self.slots[key] = len(self.arena)
                        self.arena.append(0)
                    slot = self.slots[key]
                    self.writes_per_slot[slot] += 1
                    self.high_updates += 1
                    self.events.append((len(self.payload) + 1, slot))
                    self.downward += (digit & ~(digit + 1)).bit_count()
                    if self.table is None:
                        self.arena[slot] = digit + 1
                return
            old = higher
        raise AssertionError('overflow outside test clock')

    def parts(self, key):
        high = self.read_number('high', key, self.high_radix, self.high_depth)
        low = self.read_number('low', (key, high), self.low_radix, self.low_depth)
        return high, low

    def load(self, key):
        high, low = self.parts(key)
        version = high * self.block + low
        return self.payload[key, version] if version else 0

    def store(self, key, value):
        high, low = self.parts(key)
        next_version = high * self.block + low + 1
        if low + 1 == self.block:
            self.increment('high', key, high, self.high_radix, self.high_depth)
        else:
            self.increment('low', (key, high), low, self.low_radix, self.low_depth)
        assert (key, next_version) not in self.payload
        self.payload[key, next_version] = value
        assert self.parts(key) == divmod(next_version, self.block)


def replay(trace, parameters, table):
    memory = VersionedMemory(*parameters, table=table)
    cursor = 0
    for time, (key, value) in enumerate(trace, 1):
        memory.store(key, value)
        due = cursor < len(table.events) and table.events[cursor][0] <= time
        emitted = len(memory.events) > cursor
        assert emitted == due
        if due:
            assert memory.events[cursor] == table.events[cursor]
            cursor += 1
        assert memory.load(key) == value
    assert cursor == len(table.events)


def check_trace(trace, low_radix, low_depth, high_radix, high_depth):
    memory = VersionedMemory(low_radix, low_depth, high_radix, high_depth)
    reference = {}
    stores = Counter()
    for i, (key, value) in enumerate(trace, 1):
        memory.store(key, value)
        reference[key] = value
        stores[key] += 1
        assert all(memory.load(address) == reference.get(address, 0) for address in (*stores, 7))
        exact = sum(count // memory.block for count in stores.values())
        assert len(memory.arena) <= memory.high_updates == exact <= i // memory.block
        assert memory.downward == sum(count - count.bit_count() for count in memory.arena)
        assert memory.downward <= exact
        assert all(count < high_radix for count in memory.writes_per_slot.values())
    table = EventTable(memory.events)
    replay(trace, (low_radix, low_depth, high_radix, high_depth), table)


def reject(action):
    try:
        action()
    except AssertionError:
        return
    raise AssertionError('accepted a false claim')


def main():
    stores = tuple(product((0, 3), (0, 15)))
    small = 0
    for length in range(7):
        for trace in product(stores, repeat=length):
            check_trace(trace, 2, 1, 2, 4)
            small += 1
    long = 0
    for low_radix, low_depth, high_radix in product((2, 3, 4), (1, 2, 3), (2, 3, 4)):
        trace = [(0 if i % 5 else i % 7, (7*i) % 19) for i in range(400)]
        check_trace(trace, low_radix, low_depth, high_radix, 10)
        long += 1
    trace = [(0, 2), (0, 4), (3, 1), (3, 2)]
    parameters = (2, 1, 4, 2)
    replay(trace, parameters, EventTable([(2, 0), (4, 1)]))
    for bad in ([(2, 1), (4, 0)], [(2, 0)], [(2, 0), (3, 1)], [(1, 0), (2, 0), (4, 1)]):
        reject(lambda: replay(trace, parameters, EventTable(bad)))
    table = EventTable([(1, 2), (2, 1), (3, 2), (4, 0)])
    for slot, time in product(range(4), range(1, 7)):
        cut = bisect_left(table.keys, (slot, time))
        assert table.certified_read(slot, time, cut) == sum(
            s == slot and t < time for t, s in table.events
        )
        for wrong in set(range(len(table.keys) + 1)) - {cut}:
            reject(lambda: table.certified_read(slot, time, wrong))
    print(f'Verified {small} complete small write traces and {long} longer mixed-radix runs.')


if __name__ == '__main__':
    main()
