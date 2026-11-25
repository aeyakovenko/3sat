"""Build actual degree-four DIMACS selector cubes and solve their serialized corners."""

from collections import Counter, defaultdict
from itertools import product

import pycosat

from bounded_occurrence_edits_audit import pin
from one_byte_dense_successor_audit import clause, encode, parse


class Names:
    def __init__(self):
        self.count = 0

    def new(self):
        self.count += 1
        return self.count


def semantic_formula(first, second, arity):
    ids = Names()
    switches = [ids.new() for _ in range(arity)]
    rows = []
    parity = switches[0]
    for bit in switches[1:]:
        out = ids.new()
        for a, b in product((0, 1), repeat=2):
            rows.append((-parity if a else parity, -bit if b else bit, out if a ^ b else -out))
        parity = out
    for side, source in enumerate((first, second)):
        renamed = {v: ids.new() for v in sorted({abs(z) for row in source for z in row})}
        guard = -parity if side else parity
        for row in source:
            a, b, c = (renamed[abs(z)] if z > 0 else -renamed[abs(z)] for z in row)
            y = ids.new()
            rows.extend(((guard, a, y), (-y, b, c)))
    return rows, switches


def physical_template(first, second, arity, h, *, semantic_builder=semantic_formula):
    logical, switches = semantic_builder(first, second, arity)
    assert len(set(switches)) == arity == len(switches)
    pool = Names()
    rows = []
    def force_false(x):
        first_aux = pool.new()
        for _ in range(8):
            pool.new()
        rows.extend(pin(-x, first_aux))

    occurrences = defaultdict(list)
    for row in logical:
        physical = []
        for literal in row:
            v = pool.new()
            occurrences[abs(literal)].append(v)
            physical.append(v if literal > 0 else -v)
        rows.append(tuple(physical))

    size = sum(32 + sum(sum(len(str(x)) for x in row)+5 for row in src)
               for src in (first, second))
    scale = size + arity * (size + arity + 2).bit_length()
    start = 10 * (1 + (scale // max(1, scale.bit_length())) // 10)
    stride = 10 * ((h+29)//10)
    first_high = start + stride*arity + 2
    reserved = {}
    selector = []
    for i, bit in enumerate(switches):
        offset = start + stride*i
        p, q, a, b = [pool.new() for _ in range(4)]
        for sym, value in ((p, 1), (q, 2), (a, 12), (b, 13)):
            reserved[sym] = offset + value
        force_false(p)
        force_false(q)
        occurrences[bit].extend((-a, b))
        selector.append((p, q, a, b))
        for j in range(h):
            u, v, w = [pool.new() for _ in range(3)]
            reserved[u] = offset+20+j
            reserved[v] = first_high+2*(h*i+j)
            reserved[w] = reserved[v]+1
            rows.append((u, v, w))
    for copies in occurrences.values():
        if len(copies) < 2:
            continue
        for a, b in zip(copies, copies[1:]+copies[:1]):
            f = pool.new()
            force_false(f)
            rows.append((-a, b, f))
    while pool.count < max(reserved.values()):
        rows.append(tuple(pool.new() for _ in range(3)))
    remaining = iter(sorted(set(range(1, pool.count+1))-set(reserved.values())))
    ren = {j: reserved[j] if j in reserved else next(remaining) for j in range(1, pool.count+1)}
    def signed(x):
        return ren[abs(x)] if x > 0 else -ren[abs(x)]
    fixed = {clause(*(signed(x) for x in row)) for row in rows}
    assert len(fixed) == len(rows) and len(set(ren.values())) == pool.count
    return fixed, [tuple(map(signed, row)) for row in selector], pool.count


def minimum(v, c, t):
    return (len(str(v+3*t))-len(str(v)) + len(str(c+t))-len(str(c)) +
            5*t + sum(len(str(x)) for x in range(v+1, v+3*t+1)))


def padding(v, c, want):
    t = 0
    while minimum(v, c, t+1) <= want:
        t += 1
    slack = want-minimum(v, c, t)
    assert 0 <= slack <= 3*t
    triples = set()
    for i in range(t):
        row = tuple(v+3*i+j+1 for j in range(3))
        triples.add(clause(*(-z if 3*i+j<slack else z for j, z in enumerate(row))))
    return triples


def truth(rows):
    return pycosat.solve(list(rows)) != 'UNSAT'


def audit(first, second, arity, h=4):
    fixed, select, v = physical_template(first, second, arity, h)
    c = len(fixed)+arity
    zero = fixed | {clause(p,q,a) for p,q,a,b in select}
    length = len(encode(zero))
    outcomes = (truth(first), truth(second))
    t0 = 4*len(str(v+c+10))+20
    thresholds = [0, minimum(v,c,t0)+2, minimum(v,c,t0)+3, minimum(v,c,t0)+4]
    # Exercise the decimal carries in both counts.
    for value, step in ((c,1),(v,3)):
        next_decade = 10**len(str(value))
        gap = (next_decade-value + step-1)//step
        if t0 <= gap <= 600:
            thresholds.extend([minimum(v,c,gap)-1, minimum(v,c,gap)])
    cases = 0
    relative = None
    for target in sorted(set(thresholds)):
        add = padding(v,c,target)
        base = encode(zero|add)
        assert len(base) == length+target
        coordinates = []
        for p,q,a,b in select:
            start = base.index(f'\n{p} {q} {a} 0'.encode())+1
            coordinates.append(start+len(f'{p} {q} {a}')-1)
        deltas = tuple(x-coordinates[0] for x in coordinates)
        assert relative is None or relative == deltas
        relative = deltas
        for coeff in (1, 2, 4):
            width = 16*((coeff*(8*len(base)+1).bit_length()+15)//16)
            assert len({x//(width//8) for x in coordinates}) == arity
        for bits in product((0,1),repeat=arity):
            rows = fixed|add|{clause(p,q,b if z else a) for z,(p,q,a,b) in zip(bits,select)}
            raw = encode(rows)
            expected = bytearray(base)
            for z, pos in zip(bits,coordinates):
                expected[pos] ^= z
            assert raw == expected
            seen = parse(raw)
            assert max(Counter(abs(x) for row in seen for x in row).values()) <= 4
            assert truth(seen) == outcomes[sum(bits)%2]
            cases += 1
    return cases


def sharp_thresholds():
    checked = exceptional = 0
    for v in range(3, 250):
        d = len(str(v))
        t = d+3
        target = 1+t*(3*d+8)
        for c in range((v+2)//3, 4*v//3+1):
            cost = minimum(v,c,t)
            assert cost <= target+1
            if cost == target+1:
                assert v == 10**d-1 and c <= v
                assert 4*v-3*c > 3*(10**(d-1)-1)
                exceptional += 1
            assert minimum(v,c,t+1)-cost <= 3*t+1
            checked += 1
    # Construct real attaining and saturated inputs across decimal widths.
    for d in (1,2,3):
        v = 10**d-1
        k = d+3
        target = 1+k*(3*d+8)
        saturated = {clause(a, b*(a+1), c*(a+2)) for a in range(1,v+1,3)
                     for b,c in product((1,-1),repeat=2)}
        assert set(Counter(abs(j) for row in saturated for j in row).values()) == {4}
        assert truth(saturated) and len(saturated) == 4*v//3
        assert 1+(k-1)*(3*d+11) == target-2
        assert minimum(v,len(saturated),k) == target
        # Exhaust all count choices on the critical interval and check the
        # necessary loss of old rows for each possible count increase.
        last_counts = set()
        transitions = 0
        for gain in range(target,target+3*k+2):
            possible = {s for s in range(k+3) if 1+(3*d+8)*s <= gain <= 1+(3*d+11)*s}
            assert possible and possible <= {k,k+1}
            if gain == target:
                assert possible == {k}
            if gain == target+3*k+1:
                assert possible == {k+1}
            if k in last_counts and k+1 in possible:
                old_signs = gain-1-(1+k*(3*d+8))
                new_signs = gain-(1+(k+1)*(3*d+8))
                assert (old_signs-new_signs+2)//3 == k
                transitions += 1
            last_counts = possible
        assert transitions
        raw = encode(saturated | padding(v,len(saturated),target))
        assert len(raw)-len(encode(saturated)) == target and truth(parse(raw))

        cycle = {clause(1+i, 1+(i+1)%v, 1+(i+2)%v) for i in range(v)}
        assert set(Counter(abs(j) for row in cycle for j in row).values()) == {3}
        assert minimum(v,len(cycle),k) == target+1
        triples = {clause(v+3*i+1, v+3*i+2, v+3*i+3) for i in range(k)}
        triples.remove(clause(v+3*k-2,v+3*k-1,v+3*k))
        triples.add(clause(v,v+3*k-2,v+3*k-1))
        raw = encode(cycle|triples)
        assert len(raw)-len(encode(cycle)) == target and truth(parse(raw))
        assert max(Counter(abs(j) for row in parse(raw) for j in row).values()) == 4
    return checked, exceptional


if __name__ == '__main__':
    catalog = list(product((1,-1),(2,-2),(3,-3)))
    total = 0
    for first,second in ((catalog,catalog[:-1]),(catalog[:-1],catalog),(catalog,catalog),
                         ([],catalog[:-1]), ([],[])):
        for arity in (1,2,3):
            total += audit(first,second,arity)
    print(f'{total} parsed and solved degree-four selector corners; widths D=1,2,4')
    counts, exceptions = sharp_thresholds()
    print(f'{counts} feasible variable/clause counts, {exceptions} sharp-header exceptions, 6 actual boundary extensions')
