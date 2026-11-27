"""Verify three-shift growth and construct actual alternative word records."""
from itertools import product

from fresh_native_address_audit import raw, sat


def alternative(a):
    w = 8 * len(a)
    q = w // (w & -w)
    b = bytearray(a)
    b[-1] = ord('5')
    delta = (int.from_bytes(a, 'little') - int.from_bytes(b, 'little')) % q
    previous = {0: None}
    for i in range(a.index(b'\n') + 1, len(a) - 1):
        if delta in previous:
            break
        if 1 << (8*i) < w:
            continue
        assert b[i] == 32
        weights = [(c, ((c-32) * pow(256, i, q)) % q) for c in (9, 10)]
        for residue in tuple(previous):
            for c, weight in weights:
                new = (residue + weight) % q
                if new not in previous:
                    previous[new] = residue, i, c
    assert delta in previous
    while delta:
        delta, i, byte = previous[delta]
        b[i] = byte
    assert int.from_bytes(a, 'little') % w == int.from_bytes(b, 'little') % w
    return bytes(b)


def exhaustive_growth():
    checks = 0
    # The rescaling in the proof allows every nontrivial third shift u, at any modulus.
    for q in range(3, 16):
        full = (1 << q) - 1
        for t in range(1, full + 1):
            def rotate(offset):
                return ((t << offset) | (t >> (q-offset))) & full
            with_one = t | rotate(1)
            for u in range(2, q):
                assert (with_one | rotate(u)).bit_count() >= min(q, t.bit_count()+2)
                checks += 1
    return checks


def main():
    growth = exhaustive_growth()
    widths = list(range(32, 300)) + [341, 343, 375, 509, 1021, 2047, 4093, 4096]
    records = files = changed_padding = 0
    for W, digit in product(widths, (6, 7, 8, 9)):
        k = max(1, (W.bit_length() - 1) // 8)
        a = raw(8*W, k, digit, 4)
        b = alternative(a)
        assert a[-1:] == b'4' and b[-1:] == b'5' and a.split()[:-1] == b.split()[:-1]
        changed_padding += a[:-1] != b[:-1]
        records += 1
        if W in (32, 45, 63, 81, 97, 121, 233, 255, 341, 4093) and digit == 6:
            head = b'p cnf 9 20\n'
            for literal in (-1, -digit, 4, -5):
                for x, y in product((2,-2), (3,-3)):
                    head += f'{literal} {x} {y} 0\n'.encode()
            head += b' ' * ((-len(head) - 1) % W) + b'4'
            for switches in product((0,1), repeat=3):
                file = head + b''.join((a,b)[v] for v in switches) + f' {digit} 1 0\n'.encode()
                assert sat(file) == (not any(switches))
                files += 1
    print(f'{growth} finite additive-growth cases, {records} congruent records, '
          f'{changed_padding} with whitespace corrections, {files} parsed SAT files')


if __name__ == '__main__':
    main()
