"""Check the mark schedule and its one-pass reading of the dense ASCII files.

The reused dense DIMACS audit modules import pycosat. Python object storage and
the materialized reference suffix below are used for independent finite checks.
"""

from collections import Counter
from itertools import product
from random import Random

from dense_ascii_chunk_circuit_audit import encode, sat_from_bytes
from dense_projection_scan_audit import public_names, template


class Invalid(Exception):
    pass


class WordStream:
    def __init__(self, data, width):
        self.data = data
        self.width = width
        self.reads = 0
        self.buffer = self.available = self.consumed = 0

    def take(self, bits):
        if self.consumed + bits > 8 * len(self.data):
            raise Invalid
        while self.available < bits:
            start = self.reads * self.width
            end = min(start + self.width, len(self.data) * 8)
            raw = int.from_bytes(self.data[start // 8:(end + 7) // 8], 'little')
            word = (raw >> (start % 8)) & ((1 << (end - start)) - 1)
            self.buffer |= word << self.available
            self.available += end - start
            self.reads += 1
        value = self.buffer & ((1 << bits) - 1)
        self.buffer >>= bits
        self.available -= bits
        self.consumed += bits
        return value

    def match(self, token):
        if self.take(8 * len(token)) != int.from_bytes(token, 'little'):
            raise Invalid


def packed_key(fields, digits, k):
    byte_mask = int.from_bytes(bytes([1]) * digits, 'little')
    result = 0
    for j, field in enumerate(fields):
        if field & ~byte_mask != 48 * byte_mask:
            raise Invalid
        plane = field & byte_mask
        for s in range(digits):
            if j * digits + digits - 1 - s >= 2 * k and plane & (1 << (8 * s)):
                raise Invalid
        result |= plane << j
    return result


def work_log(keys, sentinels=False):
    # Namespaces stand for the disjoint address intervals of the word machine.
    sequence = [('key', x) for x in keys]
    if sentinels:
        sequence.extend([('sentinel', 0)] * 2)
    written = set()
    visits = Counter()
    replies = []
    hit = False
    for i, real in enumerate(sequence):
        dummy = ('dummy', i)
        source = dummy if hit else real
        returned = source in written
        hit |= returned
        target = dummy if hit else real
        assert target not in written
        written.add(target)
        visits.update((source, target))
        replies.append(int(returned))
    assert sum(replies) <= 1
    assert all(n <= 3 for n in visits.values())
    assert sum(n == 3 for n in visits.values()) <= 1
    return replies


def canonical_keys(data, k):
    count, digits, _, bound = public_names(k)
    fixed, _, pad, selector = template(k)
    width = 12 * ((len(data) * 8 + 1).bit_length())
    stream = WordStream(data, width)
    stream.match(f'p cnf {bound} {16 * count + len(fixed)}\n'.encode())
    keys = []
    for row in range(count):
        fields = []
        for bank in range(1, 9):
            prefix = f'-{selector + row} {bank}'.encode()
            stream.match(prefix)
            field = stream.take(8 * digits)
            stream.match(f' {pad} 0\n'.encode())
            stream.match(prefix)
            if stream.take(8 * digits) != field:
                raise Invalid
            stream.match(f' -{pad} 0\n'.encode())
            fields.append(field)
        keys.append(packed_key(fields, digits, k))
    for i, (a, b, c) in enumerate(fixed):
        stream.match(f'{a} {b} {c} 0'.encode())
        if i + 1 == len(fixed):
            padding = len(data) - stream.consumed // 8 - 1
            if padding < 0:
                raise Invalid
            for _ in range(padding):
                stream.match(b' ')
        stream.match(b'\n')
    assert stream.reads == (8 * len(data) + width - 1) // width
    return keys


def main():
    traces = 0
    for length in range(1, 6):
        for keys in product(range(4), repeat=length):
            duplicate = len(set(keys)) < len(keys)
            assert sum(work_log(keys)) == duplicate
            forced = work_log(keys, sentinels=True)
            assert sum(forced) == 1 and bool(forced[-1]) != duplicate
            traces += 1

    field_count = 0
    for k in range(1, 8):
        digits = (k + 3) // 4
        addresses = set()
        for x in range(1 << (2 * k)):
            mask = (1 << digits) - 1
            values = [(x >> (digits * j)) & mask for j in range(8)]
            fields = [int.from_bytes(format(v, f'0{digits}b').encode(), 'little')
                      for v in values]
            address = packed_key(fields, digits, k)
            assert address < 1 << (8 * digits) and address not in addresses
            addresses.add(address)
        field_count += len(addresses)

    rng = Random(20261126)
    files = 0
    for k in range(1, 8):
        m = 1 << k
        for duplicate in (False, True):
            values = rng.sample(range(m * m), m)
            if duplicate:
                values[-1] = values[0]
            raw = encode(k, values)
            assert sat_from_bytes(raw) == duplicate
            for padding in (0, 3, 18):
                data = raw[:-1] + b' ' * padding + b'\n'
                keys = canonical_keys(data, k)
                assert bool(sum(work_log(keys))) == duplicate
                files += 1
            # A mismatch in a fixed part must invalidate an otherwise good file.
            altered = raw[:-3] + b' 1\n'
            try:
                canonical_keys(altered, k)
            except Invalid:
                pass
            else:
                raise AssertionError('bad final clause passed')
    print(f'{traces} full/sentinel trace pairs, {field_count} packed key addresses, '
          f'{files} complete ordered files')


if __name__ == '__main__':
    main()
