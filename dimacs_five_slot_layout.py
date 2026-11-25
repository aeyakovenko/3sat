"""Virtual access to explicit sign-edit pairs even at astronomical encoded lengths."""
from itertools import product
from math import gcd


def record(names, negative):
    out = bytearray()
    for name, neg in zip(names, negative):
        if len(out) % 2 == 0:
            out.extend(b' ')
        out.extend(b'-' if neg else b' ')
        out.extend(str(name).encode('ascii'))
        out.extend(b' ')
    out.extend(b'0')
    if len(out) % 2 == 0:
        out.extend(b' ')
    out.extend(b'\n')
    assert len(out) % 2 == 0
    assert all(byte % 2 == 0 for byte in out[::2])
    return bytes(out)


def verified_family(j):
    total = 10**j
    header = f'p cnf 20 {total}'.encode('ascii')
    header += (b' ' if len(header) % 2 == 0 else b'') + b'\n'
    pins = [record((var, 8, 20), (False, a, b))
            for var in (2, 4, 6) for a, b in product((False, True), repeat=2)]
    base = record((2, 4, 6), (False, False, False))
    alt = record((2, 4, 6), (True, True, True))
    prefix = header + b''.join(pins)
    number_bytes = len(prefix) + (total-len(pins))*len(base)
    n = 8*number_bytes
    w = 16 * (((n+1).bit_length()+15)//16)
    width = w//8
    assert len(prefix) % 2 == 0 and width >= 2*len(base)

    def byte(i):
        if i < len(prefix):
            return prefix[i]
        if i < number_bytes:
            return base[(i-len(prefix)) % len(base)]
        return 0

    def word(i):
        return bytes(byte(i*width+t) for t in range(width))

    first = (len(prefix)+width-1)//width
    stop = number_bytes//width
    phases = len(base)//gcd(width,len(base))
    assert stop-first >= phases and stop-first > n//(2*w)
    addresses = [*range(first), *range(first, first+phases), stop-1, stop]
    assert all(word(a)[0] % 2 == 0 for a in addresses)
    for a in range(first,first+phases):
        ordinary = word(a)
        assert 10 <= ordinary[-1] <= 56
        start = (len(prefix) - a*width) % len(base)
        assert ordinary[start:start+len(base)] == base
        changed = ordinary[:start]+alt+ordinary[start+len(base):]
        assert len(changed) == width and changed != ordinary
        assert changed[0] % 2 == 0

    def clause(line):
        return [int(x) for x in line.split()][:-1]

    def sat(lines, values):
        return all(any(values[abs(v)] == (v>0) for v in c) for c in lines)

    vars_used = (2,4,6,8,20)
    assignments = [dict(zip(vars_used,t)) for t in product((False,True),repeat=5)]
    fixed = list(map(clause,pins))
    assert any(sat(fixed+[clause(base)], a) for a in assignments)
    assert not any(sat(fixed+[clause(alt)], a) for a in assignments)
    return w, first, phases


if __name__ == '__main__':
    cases = [verified_family(j) for j in (128,129,200,384,769,1200)]
    print('Verified width, prefix words, tail phases:', cases)
