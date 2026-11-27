"""Stable packed trace checking with no timestamps and exact native branch counts."""

from functools import cache
from itertools import product


class Packed:
    """Least-significant-bit first, allowing fields to cross actual word boundaries."""

    def __init__(self, word_width):
        self.width = word_width
        self.words = []
        self.length = 0

    def push(self, value, bits):
        assert bits <= self.width and value >= 0 and value.bit_length() <= bits
        if not bits:
            return
        index, used = divmod(self.length, self.width)
        if not used:
            self.words.append(0)
        take = min(bits, self.width - used)
        self.words[index] |= (value & ((1 << take) - 1)) << used
        if take < bits:
            self.words.append(value >> take)
        self.length += bits

    def get(self, pos, bits):
        assert 0 <= pos <= pos + bits <= self.length and bits <= self.width
        if not bits:
            return 0
        index, used = divmod(pos, self.width)
        low = self.words[index] >> used
        if used + bits > self.width:
            low |= (self.words[index + 1] & ((1 << (used + bits - self.width)) - 1)) << (self.width - used)
        return low & ((1 << bits) - 1)

    def canonical(self):
        return not self.length or not (self.length % self.width) or (
            self.words[-1] < (1 << (self.length % self.width)))

    def chunks(self, bits, capacity):
        assert self.length % bits == 0 and capacity * bits <= self.width
        for start in range(0, self.length, bits * capacity):
            width = min(self.length - start, bits * capacity)
            yield self.get(start, width), width // bits


def pack(records, field, width):
    out = Packed(width)
    for record in records:
        out.push(record, field)
    return out


def little_fields(code, size, field):
    for _ in range(size):
        yield code & ((1 << field) - 1)
        code >>= field


def append(out, source):
    for pos in range(0, source.length, source.width):
        b = min(source.length - pos, source.width)
        out.push(source.get(pos, b), b)


def encode_event(bank, addr, write, val, w):
    return val | (write << w) | ((addr | (bank << w)) << (w + 1))


def decode_event(code, w):
    return code >> (w + 1), (code >> w) & 1, code & ((1 << w) - 1)


@cache
def partition(code, entries, field, shift):
    sides = [(0, 0), (0, 0)]
    for x in little_fields(code, entries, field):
        side = (x >> shift) & 1
        val, bits = sides[side]
        sides[side] = (val | (x << bits), bits + field)
    return tuple(sides)


def group_by_key(source, field, w, capacity):
    for bit in range(w+1):
        first, second = Packed(source.width), Packed(source.width)
        for chunk, count in source.chunks(field, capacity):
            low, high = partition(chunk, count, field, bit+w+1)
            first.push(*low)
            second.push(*high)
        append(first, second)
        source = first
    return source


@cache
def sorted_chunk(code, entries, w):
    """One summary of a sorted block, with its first read requiring the old cache."""
    field = 2*w+2
    first_key = last_key = None
    required = last = None
    for e in little_fields(code, entries, field):
        key, write, val = decode_event(e, w)
        if key != last_key:
            if first_key is None:
                first_key = key
                last = None
            else:
                assert key > last_key
                last = 0
            last_key = key
        if not write:
            if last is None:
                required = val
            elif val != last:
                return None
        last = val
    return first_key, required, last_key, last


def sorted_ok(source, w, capacity):
    field = 2*w+2
    rows = group_by_key(source, field, w, capacity)
    last_key, last = None, 0
    for packed, count in rows.chunks(field, capacity):
        summary = sorted_chunk(packed, count, w)
        if summary is None:
            return False
        first_key, required, new_key, new = summary
        if required is not None and required != (last if first_key == last_key else 0):
            return False
        last_key, last = new_key, new
    return True


@cache
def projected_chunk(code, entries, w, target):
    required = last = None
    for event in little_fields(code, entries, 2*w+2):
        key, write, value = decode_event(event, w)
        if key != target:
            continue
        if not write:
            if last is not None and value != last:
                return None
            if last is None:
                required = value
        last = value
    return required, last


def projected_ok(source, w, capacity):
    for key in range(2 << w):
        current = 0
        for code, entries in source.chunks(2*w+2, capacity):
            summary = projected_chunk(code, entries, w, key)
            if summary is None:
                return False
            req, last = summary
            if req is not None and req != current:
                return False
            if last is not None:
                current = last
    return True


def direct_events(events, w):
    memory = {}
    for e in events:
        key, write, val = decode_event(e, w)
        if not write and val != memory.get(key, 0):
            return False
        memory[key] = val
    return True


# The test program has two dynamic guesses and multiple dependent indirect
# accesses; XFER reads work[a] before writing work[b], even if a=b.
def encode_row(pc, a, b, z, reply, w):
    return pc | (a << 4) | (b << (4+w)) | (z << (4+2*w)) | (reply << (4+3*w))


def decode_row(row, w):
    return (row & 15, *little_fields(row >> 4, 4, w))


def step(row, w):
    pc, a, b, z, reply = decode_row(row, w)
    if pc not in (0, 3) and z or pc not in (1, 4, 5) and reply:
        return None
    if pc in (0, 3):  # GUESS into a
        return (pc+1, z, b), ()
    if pc == 1:  # read input[a] into b
        return (2, a, reply), (encode_event(1, a, 0, reply, w),)
    if pc == 2:  # write b to work[a]
        return (3, a, b), (encode_event(0, a, 1, b, w),)
    if pc == 4:
        return (5, a, b), (encode_event(0, a, 0, reply, w), encode_event(0, b, 1, reply ^ a, w))
    if pc == 5:
        return (6, a, reply), (encode_event(0, b, 0, reply, w),)
    if pc == 6:
        return (7 if b else 8, a, b), ()
    if pc in (7, 8):
        return (pc, a, b), ()
    return None


@cache
def cpu_chunk(code, entries, w):
    field = 4+4*w
    first = expected = None
    events = []
    for row in little_fields(code, entries, field):
        current = decode_row(row, w)[:3]
        if first is None:
            first = current
        if expected is not None and current != expected:
            return None
        result = step(row, w)
        if result is None:
            return None
        expected, new = result
        events.extend(new)
    event_width = 2*w+2
    packed = sum(value << (i*event_width) for i, value in enumerate(events))
    return first, expected, packed, len(events)*event_width


def traced(payload, guesses, t, w):
    state = (0, 0, 0)
    memory = {}
    choices = iter(guesses)
    rows = []
    for _ in range(t):
        pc, a, b = state
        z = next(choices) if pc in (0, 3) else 0
        reply = 0
        if pc == 1:
            reply = payload[a] if a < len(payload) else 0
        elif pc in (4, 5):
            reply = memory.get(a if pc == 4 else b, 0)
        row = encode_row(pc, a, b, z, reply, w)
        rows.append(row)
        state, events = step(row, w)
        for event in events:
            key, write, val = decode_event(event, w)
            if write:
                memory[key] = val
    return tuple(rows), state[0] == 7


def verify(payload, rows, t, w, host, cpu_cap, event_cap):
    field, efield = 4+4*w, 2*w+2
    if rows.length != t*field or not rows.canonical():
        return False
    events = Packed(host)
    for addr, val in enumerate(payload):
        events.push(encode_event(1, addr, 1, val, w), efield)
    expected = (0, 0, 0)
    for packed, n in rows.chunks(field, cpu_cap):
        out = cpu_chunk(packed, n, w)
        if out is None:
            return False
        first, expected2, new, bits = out
        if first != expected:
            return False
        expected = expected2
        events.push(new, bits)
    return expected[0] == 7 and sorted_ok(events, w, event_cap)


def main():
    histories = accepts = corrupt = memories = 0
    for n in range(5):
        for events in product(range(8), repeat=n):
            # Single bank, two addresses, two values, both reads and writes.
            expected = direct_events(events, 1)
            for width in (13, 18):
                source = pack(events, 4, width)
                for cap in (1, 2, 3):
                    ordered = group_by_key(source, 4, 1, cap)
                    assert [x for x, _ in ordered.chunks(4, 1)] == sorted(events, key=lambda x:x>>2)
                    assert sorted_ok(source, 1, cap) == projected_ok(source, 1, cap) == expected
                    memories += 1
    for w in (1, 2):
        choices = range(1 << w)
        field = 4 + 4*w
        mask = (1 << w) - 1
        for length in range(1, 4 if w == 2 else 3):
            for payload in product(choices, repeat=length):
                for guesses in product(choices, repeat=2):
                    for t in (6, 7, 9):
                        sequence, yes = traced(payload, guesses, t, w)
                        host = 3*field+1
                        raw = pack(sequence, field, host)
                        assert verify(payload, raw, t, w, host, 3, 4) == yes
                        histories += 1
                        accepts += yes
                        if not yes or guesses != (0, mask):
                            continue
                        for i in range(len(sequence)):
                            for bit in range(field):
                                perturbed = list(sequence)
                                perturbed[i] ^= 1 << bit
                                got = verify(payload, pack(perturbed, field, host), t, w, host, 2, 3)
                                if got:
                                    # A different genuine guess may produce a different valid history.
                                    alternative = tuple(decode_row(perturbed[j], w)[3] for j in (0, 3))
                                    rebuilt, ok = traced(payload, alternative, t, w)
                                    assert ok and rebuilt == tuple(perturbed)
                                corrupt += 1
                        if raw.length % host:
                            raw.words[-1] |= 1 << (raw.length % host)
                            assert not verify(payload, raw, t, w, host, 3, 3)
    print(f'{histories} packed CPU histories ({accepts} accepting), {corrupt} single-bit '
          f'alterations, {memories} stable-sort and universally projected memory checks')


if __name__ == '__main__':
    main()
