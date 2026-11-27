"""Exact tiny XOR search, packed tensor blocks, cutoff expansion and candidate selection."""
from itertools import combinations
from random import Random


def yates(values):
    out = list(values)
    for bit in range((len(values)-1).bit_length()):
        for s in range(len(values)):
            if s & (1 << bit):
                out[s] ^= out[s ^ (1 << bit)]
    return out


def butterfly(r):
    n = 1 << r
    indices = list(range(n))
    gates = []
    for h in range(r):
        for s in range(n):
            if s & 1 << h:
                gates.append((indices[s], indices[s ^ (1 << h)]))
                indices[s] = n+len(gates)-1
    return gates,indices


def shortest(r):
    n = 1 << r
    basis = tuple(1 << j for j in range(n))
    targets = yates(basis)
    frontier = {frozenset(basis): (basis,())}
    for count in range(1 + r*(n//2)):
        nxt = {}
        for present,(wires,gates) in frontier.items():
            if all(v in present for v in targets):
                return list(gates),[wires.index(v) for v in targets]
            for i,j in combinations(range(len(wires)),2):
                val = wires[i]^wires[j]
                if val in present:
                    continue
                key = present | {val}
                if key not in nxt:
                    nxt[key] = wires+(val,),gates+((i,j),)
        frontier = nxt
    raise AssertionError('butterfly upper bound')


def tensor(values, r, circuits):
    output = list(values)
    m = (len(values)-1).bit_length()
    for pos in range(0,m,r):
        width = min(r,m-pos)
        mask = (1 << width)-1
        gates, ends = circuits[width]
        for base in range(len(values)):
            if base & mask << pos:
                continue
            locations = [base | s << pos for s in range(mask+1)]
            wires = [output[t] for t in locations]
            for x,y in gates:
                wires.append(wires[x]^wires[y])
            for t,idx in zip(locations,ends,strict=True):
                output[t] = wires[idx]
    return output


def interpolate(clipped, d):
    coeff = list(clipped)
    for s in range(len(coeff)):
        if s.bit_count()>d:
            coeff[s]=0
    for h in range((len(coeff)-1).bit_length()):
        for s in range(len(coeff)):
            if s.bit_count()<=d and s & 1<<h:
                coeff[s] ^= coeff[s ^ (1<<h)]
    return coeff


def sparse_tail(coeff, b):
    output = yates([word if s.bit_count()<=b else 0 for s,word in enumerate(coeff)])
    full = len(output)-1
    direct = 0
    for s,word in enumerate(coeff):
        if not word or s.bit_count()<=b:
            continue
        other = full ^ s
        sub = other
        while True:
            output[s|sub] ^= word
            direct += 1
            if not sub:
                break
            sub = (sub-1) & other
    expected = sum(1 << (full.bit_count()-s.bit_count()) for s,x in enumerate(coeff)
                   if x and s.bit_count()>b)
    assert direct == expected
    return output


def choose(tables, original):
    keep = tables[0]
    for candidate in tables[1:]:
        offset = next((j for j,(a,b) in enumerate(zip(keep,candidate)) if a!=b),None)
        if offset is None:
            continue
        bit = (keep[offset]^candidate[offset]) & -(keep[offset]^candidate[offset])
        if (keep[offset] ^ original[offset]) & bit:
            keep = candidate
    return keep


def main():
    rng = Random(271191)
    circuits = {r:shortest(r) for r in (1,2)}
    assert [len(circuits[r][0]) for r in (1,2)] == [1,4]
    circuits.update({r:butterfly(r) for r in (3,4)})
    transforms = recoveries = tournaments = 0
    for m in range(1,11):
        for _ in range(12):
            length = 1 << m
            values = [rng.getrandbits(9) for i in range(length)]
            reference = yates(values)
            for r in range(1,min(4,m)+1):
                assert tensor(values,r,circuits) == reference
                transforms += 1
            d,b = rng.randrange(m+1),rng.randrange(m+1)
            coeff = [v if s.bit_count()<=d else 0 for s,v in enumerate(values)]
            table = yates(coeff)
            last = rng.randrange(length)
            last_mask = (1 << rng.randrange(1,10)) - 1
            clipped = table[:last] + [table[last]&last_mask] + [0]*(length-last-1)
            sampled = interpolate(clipped,d)
            sampled[last] &= last_mask
            sampled[last+1:] = [0]*(length-last-1)
            for method in (tensor(sampled,min(m,3),circuits), sparse_tail(sampled,b)):
                assert method[:last] == clipped[:last] and method[last]&last_mask == clipped[last]
                recoveries += 1
            candidates = []
            for _ in range(5):
                fake = list(clipped)
                fake[rng.randrange(length)] ^= rng.randrange(1,512)
                candidates.append(fake)
            candidates.insert(rng.randrange(6),clipped)
            assert choose(candidates,clipped) == clipped
            tournaments += 1
    print(f'minimum XOR counts for r=1,2 are 1,4; {transforms} dense transforms, '
          f'{recoveries} truncated/weighted reconstructions, {tournaments} candidate tournaments')


if __name__ == '__main__':
    main()
