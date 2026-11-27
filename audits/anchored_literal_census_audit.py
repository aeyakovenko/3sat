"""Check finite prefix behavior, proper anchors and lazy, wide-address RAM rows."""

from itertools import product
from random import Random


def decode(word, width):
    bits = []
    for _ in range(width // 2):
        tag = word & 3
        if tag == 3:
            return tuple(bits)
        if tag == 0:
            return None
        bits.append(tag == 2)
        word >>= 2
    return None


def encode(bits):
    word = 3
    for bit in reversed(bits):
        word = (word << 2) + 1 + int(bit)
    return word


def prefixes():
    checked = 0
    for width in (2, 4, 6, 8):
        completions = set()
        for z in range(1 << width):
            bits = decode(z, width)
            if bits is None:
                continue
            completions.add(bits)
            minimal = encode(bits)
            for high in range(-2, 16):
                other = (high << width) + z
                for at in range(2, width + 7, 2):
                    assert decode(other, at) == decode(minimal, at)
                    checked += 1
        assert len(completions) == (1 << (width // 2)) - 1
    return checked


def anchor(v):
    assert v % 3 == 0 and v >= 3
    clauses = [tuple(s*x for s, x in zip(signs, (1, 2, 3)))
               for signs in product((1, -1), repeat=3)]
    clauses.extend((j, j+1, j+2) for j in range(4, v, 3))
    lines = [f'p cnf {v} {len(clauses)}']
    for row in sorted(clauses, key=lambda c: tuple((abs(x), x < 0) for x in c)):
        lines.append(' '.join(map(str, (*row, 0))))
    return '\n'.join(lines).encode('ascii')


def anchors():
    count = 0
    for mult in (1, 2, 3, 100, 10000, 2**16, 2**100, 2**900):
        for exponent in (1, 2, 3):
            v = 3
            while True:
                raw = anchor(v)
                length = 8 * len(raw)
                if 2**v > mult * (1+length)**exponent:
                    break
                v += 3
            head, *body = raw.decode('ascii').splitlines()
            assert head == f'p cnf {v} {len(body)}'
            clauses = [tuple(map(int, row.split()[:-1])) for row in body]
            assert all(row.endswith(' 0') for row in body)
            assert all(len(c) == len({abs(z) for z in c}) == 3 for c in clauses)
            assert {abs(x) for c in clauses for x in c} == set(range(1, v+1))
            for bits in product((False, True), repeat=3):
                assert any(all(bits[abs(x)-1] != (x>0) for x in c)
                           for c in clauses if max(map(abs, c)) <= 3)
            count += 1
    return count


def memory_rows():
    rng = Random(1467001)
    total = 0
    for n in (64, 152, 1024, 2056):
        raw = rng.getrandbits(n)
        host_width = 16 * ((((n+2)**4 - 1).bit_length()+15) // 16)
        host_mask = 2**host_width - 1
        host_input = [(raw >> pos) & host_mask for pos in range(0, n, host_width)]
        digit = max(1, ((n+2).bit_length()-1)//4)
        radix = 2**digit
        for coefficient in (1, 4, 11, 24):
            width = 16 * ((((n+2)**coefficient - 1).bit_length()+15) // 16)
            mask = 2**width-1
            depth = (width+digit-1)//digit
            rows = [[] , [0]*radix]
            payload = {}
            reference = {}
            last = 0
            for index in range(850):
                dest = (rng.randrange(1+n//width) if index%4==0
                        else last if index%4==1 else rng.getrandbits(width))
                last = dest
                writing = index%3==0
                node = 1
                for level in reversed(range(depth)):
                    slot = (dest >> (level*digit)) & (radix-1)
                    if not rows[node][slot]:
                        if not writing:
                            node = 0
                            break
                        rows[node][slot] = len(rows)
                        rows.append([0]*radix)
                    node = rows[node][slot]
                if writing:
                    value = 0 if index%2==0 else rng.getrandbits(width)
                    reference[dest] = payload[node] = value
                else:
                    if dest * width >= n:
                        original = 0
                    else:
                        pos, skip = divmod(dest*width, host_width)
                        blocks = (skip+width+host_width-1)//host_width
                        acc = sum(host_input[pos+i] << (i*host_width)
                                  for i in range(blocks) if pos+i < len(host_input))
                        original = (acc >> skip) & mask
                    actual = payload[node] if node in payload else original
                    ref_original = (raw >> (dest*width)) & mask if dest*width<n else 0
                    assert actual == reference.get(dest, ref_original)
                total += 1
            assert len(rows) <= 2 + ((index//3)+1)*depth
    return total


if __name__ == '__main__':
    print(f'{prefixes():,} truncated and extended parameter comparisons')
    print(f'{anchors()} exact-clock anchor files')
    print(f'{memory_rows():,} sparse guest RAM reads/writes at four coefficients')
