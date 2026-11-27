"""Small exact tests of chirps, singular gathers and integer digit lifts."""

from itertools import product
from random import Random


def parity(x):
    return x.bit_count() & 1


def linear(a, x):
    return sum(parity(row & x) << i for i, row in enumerate(a))


def times(a, b):
    k = len(a)
    return tuple(sum(((linear(a, linear(b, 1 << j)) >> i) & 1) << j for j in range(k))
                 for i in range(k))


def symmetric(a):
    return all(((r >> j) & 1) == ((s >> i) & 1)
               for i, r in enumerate(a) for j, s in enumerate(a))


def walsh(x):
    h = list(x)
    z = 1
    while z < len(h):
        for root in range(0, len(h), 2*z):
            for i in range(root, root+z):
                a,b = h[i],h[i+z]
                h[i],h[i+z] = (a+b)%5,(a-b)%5
        z *= 2
    return h


def phases(a):
    n = 1 << len(a)
    q = [0] * n
    for x in range(1,n):
        j = x.bit_length()-1
        u = x ^ (1 << j)
        q[x] = (q[u]+((a[j]>>j)&1)+2*parity(a[j]&u))%4
    return [pow(2,i,5) for i in q]


def chirp_gather(a, x):
    phase = phases(a)
    n = len(x)
    scale = pow(n, -1, 5)
    left = [(h*pow(c,-1,5))%5 for h,c in zip(walsh(x),phase)]
    conv = walsh([(u*v)%5 for u,v in zip(walsh(left),walsh(phase))])
    return [(pow(c,-1,5)*z*scale*scale)%5 for c,z in zip(phase,conv)]


def affine_tests():
    matrices = basis = phases_checked = 0
    for k in (1,2,3):
        n = 1 << k
        all_mats = list(product(range(n), repeat=k))
        sym = [a for a in all_mats if symmetric(a)]
        factor = {times(b,c):(b,c) for b in sym for c in sym}
        assert len(factor) == len(all_mats)
        for b in sym:
            h = phases(b)
            for i,j in product(range(n),repeat=2):
                assert h[i^j] == h[i]*h[j]*(-1 if parity(linear(b,i)&j) else 1)%5
                phases_checked += 1
        for a,(b,c) in factor.items():
            for pos in range(n):
                table = [int(i == pos) for i in range(n)]
                mid = chirp_gather(b,table)
                got = chirp_gather(c,mid)
                assert got == [table[linear(a,i)] for i in range(n)]
                basis += 1
            matrices += 1
    return matrices,basis,phases_checked


def unit_gather(table, odd):
    n = len(table)
    assert odd & 1
    out = [table[0]] + [None]*(n-1)
    for r in range(1,n.bit_length()):
        mod = 1 << r
        step = n // mod
        if r <= 2:
            for j in range(1,mod,2):
                out[step*j] = table[step*((odd*j)%mod)]
            continue
        count = mod//4
        powers = [pow(5,j,mod) for j in range(count)]
        neg = int((odd & 3) == 3)
        e = powers.index((-odd if neg else odd)%mod)
        for sign,j in product(range(2),range(count)):
            p = (-1 if sign else 1)*powers[j] % mod
            q = (-1 if sign^neg else 1)*powers[(j+e)%count] % mod
            out[step*p] = table[step*q]
    assert None not in out
    return out


def mul_gather(table, s):
    if not s:
        return [table[0]] * len(table)
    h = (s&-s).bit_length()-1
    upper = unit_gather(table,s>>h)
    return [upper[(i<<h)%len(table)] for i in range(len(table))]


def forward_tables(table, s):
    n = len(table)
    h = (s&-s).bit_length()-1
    odd = s>>h
    mod = n>>h
    inverse = pow(odd,-1,mod)
    small = mul_gather(table[:mod],inverse)
    # Basis-symbol audit: None means no contribution; legal convolutions
    # in these one-sided bands have exactly one surviving data symbol.
    impulse = [None]*n
    for i in range(n):
        if i% (1<<h) == 0 and (i//(1<<h)*inverse)%mod <= (n-1)//s:
            impulse[i] = small[i>>h]
    quot, rem = [],[]
    for i in range(n):
        qterms = [impulse[j] for j in range(max(0,i-s+1),i+1) if impulse[j] is not None]
        rterms = [table[i-j] for j in range(i+1) if impulse[j] is not None and i-j < s]
        assert len(qterms) == len(rterms) == 1
        quot.append(qterms[0])
        rem.append(rterms[0])
    return quot, rem


def poly(coeff, x):
    result = 0
    for c in reversed(coeff):
        result = result*x+c
    return result


def derivative(coeff):
    return [j*c for j,c in enumerate(coeff) if j]


def hensel_gather(table, coeff):
    n=len(table)
    if n<=2:
        return [table[poly(coeff,i)%n] for i in range(n)]
    k=n.bit_length()-1
    low=1<<((k+1)//2)
    high=n//low
    # Apply the same lower-bit address operation down each high row first.
    lower=[hensel_gather(table[h*low:(h+1)*low],coeff) for h in range(high)]
    out=[None]*n
    for a in range(low):
        val=poly(coeff,a)
        der=poly(derivative(coeff),a)%high
        col=[lower[h][a] for h in range(high)]
        shifted=[col[(h+val//low)%high] for h in range(high)]
        routed=mul_gather(shifted,der)
        for h,z in enumerate(routed):
            out[h*low+a]=z
    return out


def digit_gather(table,coeff,b):
    n=len(table)
    k=n.bit_length()-1
    out=list(table)
    for start in range(0,k,b):
        width=min(b,k-start)
        low=1<<start
        radix=1<<width
        nxt=[None]*n
        for a in range(low):
            shift=(poly(coeff,a)//low)%radix
            slope=poly(derivative(coeff),a)%radix
            for hi in range(n//(low*radix)):
                col=[out[(hi*radix+d)*low+a] for d in range(radix)]
                if start==0:
                    routed=[col[poly(coeff,d)%radix] for d in range(radix)]
                else:
                    shifted=[col[(d+shift)%radix] for d in range(radix)]
                    routed=mul_gather(shifted,slope)
                for d,x in enumerate(routed):
                    nxt[(hi*radix+d)*low+a]=x
        out=nxt
    return out


def arithmetic_tests():
    rng=Random(111177)
    multiplier=division=polys=digits=0
    for k in range(1,9):
        n=1<<k
        table=list(range(n))
        rng.shuffle(table)
        for s in range(n):
            assert mul_gather(table,s)==[table[(i*s)%n] for i in range(n)]
            multiplier+=1
            if s:
                q,r=forward_tables(table,s)
                assert q==[table[i//s] for i in range(n)]
                assert r==[table[i%s] for i in range(n)]
                division+=1
        coeffs=list(product(range(n),repeat=3)) if n<=8 else [
            [rng.randrange(-n,n) for _ in range(rng.randrange(1,9))] for _ in range(60)]
        for coeff in coeffs:
            expected=[table[poly(coeff,i)%n] for i in range(n)]
            assert hensel_gather(table,coeff)==expected
            polys+=1
            for b in range(1,min(k,5)+1):
                assert digit_gather(table,coeff,b)==expected
                digits+=1
    return multiplier,division,polys,digits


if __name__=='__main__':
    print('all matrices, tested basis columns, polarizations',affine_tests(),flush=True)
    print('multipliers, divisor pairs, half lifts, digit lifts',arithmetic_tests())
