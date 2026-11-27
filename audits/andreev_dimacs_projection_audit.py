"""Exercise the packed Andreev projection with the repository's PicoSAT DIMACS checker."""

from itertools import product
from random import Random

from dense_ascii_chunk_circuit_audit import bank_name, sat_from_bytes


def encode(r, m, h, source):
    """First 2**r bits form the table; the rest are r successive parity rows."""
    n = 1 << r
    assert 1 <= h <= n and h & (h - 1) == 0 and m > 0 and len(source) == n + r * m
    limit = 3 * 10**h - 1
    maximum = limit
    core = []

    def fresh():
        nonlocal maximum
        maximum += 1
        return maximum

    def xor(a, b):
        c = fresh()
        core.extend([(a, b, -c), (a, -b, c), (-a, b, c), (-a, -b, -c)])
        return c

    def scalar(bank, bits):
        mask = sum(bit << i for i, bit in enumerate(bits))
        lib = bank_name(bank, mask, h)
        c = fresh()
        core.extend([(-c, lib), (c, -lib)])
        return c

    anchors = [fresh() for _ in range(3)]
    mask_names = {bank_name(b, mask, h) for b in (1, 2) for mask in range(1 << h)}
    for mask in range(1 << h):
        name = bank_name(1, mask, h)
        core.append((name if mask.bit_count() % 2 else -name,))
    for name in range(1, limit + 1):
        if name not in mask_names:
            core.append((-anchors[0], name, anchors[1]))

    address = []
    for j in range(r):
        row = source[n + j * m:n + (j + 1) * m]
        chunks = [scalar(1, row[i:i + h]) for i in range(0, m, h)]
        parity = chunks[0]
        for chunk in chunks[1:]:
            parity = xor(parity, chunk)
        address.append(parity)

    # The two children of a low-address prefix represent parent AND the relevant literal.
    levels = [fresh()]
    core.append((levels[0],))
    low_bits = h.bit_length() - 1
    for selector in reversed(address[:low_bits]):
        children = []
        for parent in levels:
            for literal in (-selector, selector):
                c = fresh()
                core.extend([(-c, parent), (-c, literal), (c, -parent, -literal)])
                children.append(c)
        levels = children
    for mask in range(1 << h):
        lookup = bank_name(2, mask, h)
        for offset, chosen in enumerate(levels):
            core.append((-chosen, lookup if mask & (1 << offset) else -lookup))

    table = [scalar(2, source[i:i + h]) for i in range(0, n, h)]
    for selector in address[low_bits:]:
        reduced = []
        for lo, hi in zip(table[::2], table[1::2]):
            c = fresh()
            core.extend([(selector, -lo, c), (selector, lo, -c),
                         (-selector, -hi, c), (-selector, hi, -c)])
            reduced.append(c)
        table = reduced
    core.append((table[0],))

    proper = [tuple(-a if bit else a for a, bit in zip(anchors, bits))
              for bits in product(range(2), repeat=3) if any(bits)]
    proper.extend((*clause, *anchors[:3 - len(clause)]) for clause in core)
    lines = [f'p cnf {maximum} {len(proper)}\n']
    lines.extend(f'{a} {b} {c} 0\n' for a, b, c in proper)
    return ''.join(lines).encode('ascii')


def audit(r, m, h, samples):
    n = 1 << r
    k = n + r * m
    zero = [0] * k
    baseline = encode(r, m, h, zero)
    copies = []
    occupied = set()
    for pos in range(k):
        single = zero.copy()
        single[pos] = 1
        variant = encode(r, m, h, single)
        assert len(variant) == len(baseline)
        changed = {i for i, (a, b) in enumerate(zip(baseline, variant)) if a != b}
        assert len(changed) == 2 and changed.isdisjoint(occupied)
        assert all((baseline[i], variant[i]) == (48, 49) for i in changed)
        occupied.update(changed)
        copies.append(changed)
    checked = 0
    for source in samples:
        file = encode(r, m, h, source)
        assembled = bytearray(baseline)
        for bit, offsets in zip(source, copies):
            if bit:
                for i in offsets:
                    assembled[i] = 49
        assert file == assembled
        address = sum((sum(source[n + j * m:n + (j + 1) * m]) % 2) << j for j in range(r))
        assert sat_from_bytes(file) == bool(source[address])
        checked += 1
    return checked, k


if __name__ == '__main__':
    rng = Random(261126)
    counts = [audit(2, 2, 2, product(range(2), repeat=8))]
    for r, m, h in [(3, 5, 2), (4, 3, 4)]:
        samples = ([rng.randrange(2) for _ in range((1 << r) + r * m)] for _ in range(12))
        counts.append(audit(r, m, h, samples))
    print(f'{sum(c for c, _ in counts)} serialized SAT verdicts, '
          f'{sum(k for _, k in counts)} source-bit columns checked')
