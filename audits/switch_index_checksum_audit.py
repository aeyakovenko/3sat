"""Generate opposite-verdict proper DIMACS files on which all small checksums agree."""

import argparse
from collections import Counter
from functools import partial
from hashlib import sha256
from itertools import combinations, product
from math import comb, gcd, lcm
from pathlib import Path

import pycosat

from one_byte_dense_successor_audit import clause, encode, parse
from selector_parity_cube_audit import Names, physical_template


def mux_formula(r, _first, _second, arity):
    q = r.bit_length()-1
    assert r >= 2 and 1<<q == r and arity == r+q
    ids = Names()
    data = [ids.new() for _ in range(r)]
    index = [ids.new() for _ in range(q)]
    rows, level = [], data
    for bit in index:  # The least significant bit selects within each adjacent pair.
        parents = []
        for left,right in zip(level[::2],level[1::2]):
            out = ids.new()
            rows.extend(((bit,-left,out),(bit,left,-out),
                         (-bit,-right,out),(-bit,right,-out)))
            parents.append(out)
        level = parents
    root, u, v = level[0], ids.new(), ids.new()
    rows.extend((root,a,b) for a,b in product((u,-u),(v,-v)))
    return rows,data+index


def template(r):
    total = r+r.bit_length()-1
    fixed, selectors, v = physical_template([], [], total, h=2, semantic_builder=partial(mux_formula,r))
    zero = fixed | {clause(p,q,a) for p,q,a,b in selectors}
    base = encode(zero)
    coords = []
    for p,q,a,b in selectors:
        record = f'\n{p} {q} {a} 0'.encode()
        assert base.count(record) == 1 and str(a)[:-1] == str(b)[:-1]
        pos = base.index(record) + len(record)-3
        assert base[pos] == ord('2')
        coords.append(pos)
    return base, coords, v, len(zero)


def same_weight_collision(contributions, modulus, budget=750_000):
    checked = 0
    for weight in range(1,len(contributions)//2+1):
        seen = {}
        for subset in combinations(range(len(contributions)),weight):
            mask = sum(1<<i for i in subset)
            key = sum(contributions[i] for i in subset) % modulus
            checked += 1
            prev = seen.get(key)
            if prev is not None:
                return prev,mask,checked
            seen[key] = mask
            if checked >= budget:
                raise AssertionError("increase the search budget for this fixture")
    raise AssertionError("no equal-weight collision at these parameters")


def instantiate(base, coordinates, mask):
    raw = bytearray(base)
    for i,pos in enumerate(coordinates):
        raw[pos] ^= (mask>>i)&1
    return bytes(raw)


def streamed(raw, modulus):
    ans = 1 % modulus
    for byte in raw:
        ans = (ans*256+byte) % modulus
    return ans


def check_verdict(clauses, expected_sat):
    answer = pycosat.solve(list(clauses))
    if expected_sat:
        assert isinstance(answer, list), answer
        true_literals = set(answer)
        assert all(-literal not in true_literals for literal in true_literals)
        assert all(any(literal in true_literals for literal in row) for row in clauses)
    else:
        assert answer == 'UNSAT', answer


def audit(r=32, bound=32):
    base, coords, v, c = template(r)
    modulus = lcm(*range(1,bound+1))
    delta = [pow(256,len(base)-1-pos,modulus) for pos in coords[:r]]
    a,b,checked = same_weight_collision(delta,modulus)
    assert a != b and a.bit_count() == b.bit_count()
    # Set the common query index only after the two data strings are known.
    diff = a ^ b
    target = diff.bit_length()-1
    if (a>>target)&1 == 0:
        a,b = b,a
    outputs = [instantiate(base,coords,mask | (target<<r)) for mask in (a,b)]
    yes,no = outputs
    assert len(yes) == len(no) == len(base) and Counter(yes) == Counter(no)
    changed = [i for i,pos in enumerate(coords[:r]) if (diff>>i)&1]
    assert [i for i,(u,w) in enumerate(zip(yes,no)) if u != w] == [coords[i] for i in changed]
    # Independent direct hashing of the full file, including the leading 1.
    residues = [streamed(raw,modulus) for raw in outputs]
    numbers = [(1<<(8*len(raw))) | int.from_bytes(raw,'big') for raw in outputs]
    assert residues[0] == residues[1]
    assert numbers[0] != numbers[1] and numbers[0] % modulus == residues[0]
    assert numbers[1] % modulus == residues[1]
    assert all(numbers[0]%m == numbers[1]%m for m in range(1,bound+1))
    first_split = next(m for m in range(2,modulus+2) if numbers[0]%m != numbers[1]%m)
    assert first_split > bound
    for expected,raw in zip((True,False),outputs):
        rows = parse(raw)
        degrees = Counter(abs(x) for row in rows for x in row)
        assert len(rows) == c and len(degrees) == v and max(degrees.values()) == 4
        assert set(degrees) == set(range(1,v+1))
        check_verdict(rows, expected)

    print(f'{len(base)} bytes, {8*len(base)} bits, {v} dense names, {c} distinct proper clauses')
    print(f'{r} data bits, common selected index {target}; mask weight {a.bit_count()}')
    print(f'YES data mask {a:#x}, SHA256 {sha256(yes).hexdigest()}')
    print(f'NO  data mask {b:#x}, SHA256 {sha256(no).hexdigest()}')
    print(f'{checked} masks tried; {len(changed)} differing byte positions: {[coords[i] for i in changed]}')
    print(f'index byte positions: {coords[r:]}')
    print(f'LCM(1..{bound})={modulus}, tagged residue {residues[0]}, first splitting modulus {first_split}')
    print('byte histogram:', dict(sorted(Counter(yes).items())))
    # A size guaranteeing a collision in a single weight layer may be much
    # larger than the number searched in this concrete layout.
    print(f'largest equal-weight layer: {comb(r,r//2)} masks')


def cycle_period(bound, all_bases):
    def order(a, m):
        if m == 1:
            return 1
        u = a%m
        for d in range(1,m+1):
            if u == 1:
                return d
            u = u*a % m
        raise AssertionError("argument is not a unit")
    orders = []
    for m in range(2,bound+1):
        if all_bases:
            orders.extend(order(a,m) for a in range(1,m) if gcd(a,m) == 1)
        else:
            odd = m//(m & -m)
            orders.append(order(256,odd))
    return lcm(*orders)


def six_fields():
    # Return the printed selector rows and all nonselector rows. The third
    # coordinate is the index switch and the first two are the data bits.
    fixed, selectors, v = physical_template([],[],3,h=2,semantic_builder=partial(mux_formula,2))
    return fixed,selectors


def positioned_core(fixed,selectors,t):
    cut = selectors[1][0]
    n = 30*t
    def shift(x):
        y = abs(x)+(n if abs(x)>=cut else 0)
        return y if x>0 else -y
    old = {clause(*(shift(x) for x in row)) for row in fixed}
    sel = [tuple(shift(x) for x in row) for row in selectors]
    return old,sel


def last_digit(raw,sel,bit):
    p,q,a,b = sel
    text = f'\n{p} {q} {b if bit else a} 0'.encode()
    assert raw.count(text) == 1
    return raw.index(text) + len(text)-3


def gap(fixed,select,t):
    old,rows = positioned_core(fixed,select,t)
    raw = encode(old | {clause(p,q,a) for p,q,a,b in rows})
    cut = select[1][0]
    # All 10t new triples precede selector 1 and follow selector 0.
    digits = sum(len(str(j)) for j in range(cut,cut+30*t))
    return last_digit(raw,rows[1],0)-last_digit(raw,rows[0],0)+50*t+digits


def stride_pair(bound, all_bases, output_dir=None):
    fixed,selectors = six_fields()
    period = cycle_period(bound,all_bases)
    candidate = period
    while True:
        if gap(fixed,selectors,0) <= candidate:
            lo,hi = 0,1
            while gap(fixed,selectors,hi) <= candidate:
                lo,hi = hi,2*hi
            while lo+1 < hi:
                mid = (lo+hi)//2
                if gap(fixed,selectors,mid) <= candidate:
                    lo = mid
                else:
                    hi = mid
            t = lo
            slack = candidate-gap(fixed,selectors,t)
            if slack <= 30*t:
                break
        candidate += period

    old,rows = positioned_core(fixed,selectors,t)
    cut = selectors[1][0]
    added = {clause(*(-j if j<cut+slack else j for j in range(i,i+3)))
             for i in range(cut,cut+30*t,3)}
    # Force the common query index to 1. Only the data masks differ.
    def corner(mask):
        return encode(old | added | {clause(p,q,b if z else a) for (p,q,a,b),z in zip(rows,mask)})
    yes,no = corner((0,1,1)),corner((1,0,1))
    head = yes.split(b'\n',1)[0].decode()
    x,y = last_digit(yes,rows[0],0),last_digit(yes,rows[1],1)
    assert len(yes) == len(no) and Counter(yes) == Counter(no)
    assert y-x == candidate and [(i,a,b) for i,(a,b) in enumerate(zip(yes,no)) if a!=b] == [
        (x,ord('2'),ord('3')),(y,ord('3'),ord('2'))]
    suffix = len(yes)-1-y
    assert min(x,suffix) >= (bound-1).bit_length()
    for label,raw in ((True,yes),(False,no)):
        clauses = parse(raw)
        occurrences = Counter(abs(x) for row in clauses for x in row)
        assert max(occurrences.values()) == 4
        check_verdict(clauses, label)
    L = lcm(*range(1,bound+1))
    tag = 1<<(8*len(yes))
    numbers = [tag | int.from_bytes(raw,'big') for raw in (yes,no)]
    assert all(numbers[0]%m == numbers[1]%m for m in range(1,bound+1))
    for direction in ('little','big'):
        assert int.from_bytes(yes,direction)%L == int.from_bytes(no,direction)%L
    if all_bases:
        for m in range(1,bound+1):
            for base in range(m):
                assert pow(base,suffix,m)*(pow(base,candidate,m)-1) % m == 0
                assert pow(base,x,m)*(pow(base,candidate,m)-1) % m == 0
        # Directly stream two nonstandard byte maps and radices on whole files.
        for base in (2,3,257):
            def roll(raw):
                acc = 37
                for z in raw:
                    acc = (base*acc + z*z + z%7)%L
                return acc
            assert roll(yes) == roll(no)
    if output_dir is not None:
        output_dir.mkdir(parents=True, exist_ok=True)
        for name,raw in (("b48-yes.cnf",yes),("b48-no.cnf",no)):
            path = output_dir / name
            if path.exists():
                if path.read_bytes() != raw:
                    raise FileExistsError(f'different file already exists: {path}')
            else:
                path.write_bytes(raw)
            print(f'wrote verified {path}')
    print(f'B={bound}, all rolling bases={all_bases}; {head}; {len(yes)} bytes')
    print(f'data byte offsets {x} and {y}, distance {candidate}, period {period}, '
          f'{10*t} inserted triples, {slack} adjustable signs, index=1')
    print(f'YES SHA256 {sha256(yes).hexdigest()}')
    print(f'NO  SHA256 {sha256(no).hexdigest()}')
    print(f'tagged residue {numbers[0]%L} modulo {L}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-pair", type=Path, metavar="DIR",
                        help="write the two canonical 89,692-byte B=48 files to DIR")
    args = parser.parse_args()
    audit()
    stride_pair(48,False,args.write_pair)
    stride_pair(32,True)
