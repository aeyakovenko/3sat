"""Check the base and single-word SAT edits for the static-size induction."""
from itertools import product
from small_sat_ram_clocks import BASE, HEADER


def record(names, forbidden):
    return sum(i << shift for i, shift in zip(names, (11, 7, 3))) | forbidden


def models(rec):
    names = [(rec >> p) & 15 for p in (11, 7, 3)]
    return sum(1 << value for value in range(32)
               if sum(((value >> (i - 1)) & 1) << j for j, i in enumerate(names)) != (rec & 7))


def check(s):
    prelude = [record((name, 4, 5), (a << 1) | (b << 2))
               for name in (1, 2, 3) for a, b in product(range(2), repeat=2)]
    requested = 4 * s + 40
    tail = requested
    while True:
        length = 16 * (len(prelude) + 1 + tail)
        width = 16 * (((length + 1).bit_length() + 15) // 16)
        lanes = width // 16
        first = (len(prelude) + 1 + lanes - 1) // lanes
        k = length // width - first
        if k >= requested:
            break
        tail += max(1, (requested - k) * lanes)
    data = [HEADER] + prelude + [BASE] * tail
    common = (1 << 32) - 1
    for rec in prelude:
        common &= models(rec)
    assert common & models(BASE)
    assert not common & models(BASE | 7)
    words = [sum(rec << (16 * j) for j, rec in enumerate(data[i:i + lanes]))
             for i in range(0, len(data), lanes)]
    assert len(set(words) | {0, width, length}) <= 20
    for address in range(first, first + k):
        index = address * lanes
        assert data[index] == BASE
        # Each edited record flips three sign bits and touches just its designated word.
        assert words[address] ^ ((words[address] & ~65535) | (BASE | 7)) == 7
    assert 2 * (k + max(0, k - 2*s - 20)) >= 3*k
    return width, k


if __name__ == '__main__':
    cases = [check(s) for s in (0, 1, 4, 5, 16, 256, 1024, 4096)]
    assert {w for w, _ in cases} == {16, 32}
    print('eight static-size suites verified; widths and full tail-word counts', cases)
