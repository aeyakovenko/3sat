"""Compile aligned equality clauses, inspect their address ANF, and replay all routes."""
from itertools import product
from random import Random


def name(side, value, k):
    return str(side) + ''.join('2' if (value >> h) & 1 else '1' for h in range(k))


def records(k, shift):
    v = 1 << k
    rows = []
    for i in range(v):
        x, y = name(7, i, k), name(8, i ^ shift, k)
        lines = []
        for sign_x, sign_y in (('-', ' '), (' ', '-')):
            for sign_z in (' ', '-'):
                lines.append(f'{sign_x}{x} {sign_y}{y} {sign_z}1 0\n')
        text = ''.join(lines).encode()
        block = 1 << (len(text)-1).bit_length()
        rows.append(text.ljust(block, b' '))
    header = f'p cnf {name(8, v-1, k)} {4*v}\n'.encode()
    return header.ljust(v*block, b' '), b''.join(rows), block


def address_degree(data):
    n = len(data)*8
    assert n & (n-1) == 0
    coefficients = int.from_bytes(data, 'little')
    full = (1 << n) - 1
    stride = 1
    while stride < n:
        ones = ((1 << stride) - 1) << stride
        positions = (full // ((1 << (2*stride)) - 1)) * ones
        coefficients ^= (coefficients << stride) & positions
        stride *= 2
    maximum = 0
    while coefficients:
        term = coefficients & -coefficients
        maximum = max(maximum, (term.bit_length()-1).bit_count())
        coefficients -= term
    return maximum


def formula(k, prefix, data):
    header, rest = (prefix + data).split(b'\n', 1)
    mark, cnf, nv, nc = header.split()
    assert (mark,cnf) == (b'p',b'cnf') and int(nv) == int(name(8, (1<<k)-1, k))
    nums = list(map(int, rest.split()))
    assert len(nums) == 4 * int(nc)
    rows = []
    for i in range(0, len(nums), 4):
        x, y, z, zero = nums[i:i+4]
        assert zero == 0 and len({abs(x),abs(y),abs(z)}) == 3
        rows.append((x,y,z))
    assert len(set(rows)) == 4 << k
    return rows


def swap_stages(v, shift):
    data = list(range(v))
    counts = [0]*v
    for h in range(v.bit_length()-1):
        for j in range(v):
            if j & 1 << h:
                continue
            a, b = j, j | (1 << h)
            counts[data[a]] += 1
            counts[data[b]] += 1
            if shift & 1 << h:
                data[a], data[b] = data[b], data[a]
    assert all(data[j] == (j ^ shift) for j in range(v))
    assert all(n == v.bit_length()-1 for n in counts)


def main():
    rng = Random(3074)
    masks = files = routings = 0
    max_degrees = []
    for k in range(1, 8):
        v = 1 << k
        observed = 0
        for s in range(v):
            swap_stages(v,s)
            routings += 1
            if k >= 6 and s not in (0,1,v//2,v-1):
                continue
            header, body, block = records(k,s)
            physical = formula(k, header, body)
            # Row zero contains the true parameter bits in a fixed-position name.
            assert int(name(8, s, k)) == abs(physical[0][1])
            degree = address_degree(body)
            assert degree <= 1 + (8*block).bit_length() - 1
            observed = max(observed,degree)
            samples = product(range(1 << v), repeat=2) if k <= 2 else (
                (u, sum(((u >> (i ^ s)) & 1) << i for i in range(v)) ^ e)
                for u in (rng.getrandbits(v) for _ in range(4)) for e in (0,1,3))
            for a,b in samples:
                assignment = {1:bool(rng.getrandbits(1))}
                for j in range(v):
                    assignment[int(name(7,j,k))] = bool((a >> j) & 1)
                    assignment[int(name(8,j,k))] = bool((b >> j) & 1)
                actual = all(any(assignment[abs(z)] == (z>0) for z in row) for row in physical)
                expected = all(((a >> i) ^ (b >> (i ^ s))) & 1 == 0 for i in range(v))
                assert actual == expected
                masks += 1
            files += 1
        max_degrees.append(observed)
    print(f'{files} parsed files, {masks} assignment checks, {routings} routed shifts; '
          f'row-bit degrees {max_degrees}')


if __name__ == '__main__':
    main()
