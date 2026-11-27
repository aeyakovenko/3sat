"""Elementwise tests for binary address frames and characteristic-two cubic maps."""

from itertools import combinations, product
from math import comb
from random import Random


def verify_incidence():
    triples=[sum(1<<i for i in t) for t in combinations(range(22),3)]
    checked=edges=0
    for x in triples:
        for y in triples:
            dot=(x&y).bit_count()
            center=(dot-1)*2%3
            side=(int(x==y)-center)%3
            assert side==0 or (dot%2==0 and x!=y)
            assert (center+side)%3==(x==y)
            checked+=1
            edges+=bool(side)
    v,d,c=len(triples),22,23
    w=2*v**3+3*v*v*(c+edges)
    s=w*d**3-2*v**3+6*v*v*c*d
    assert w*d**3-s==104350400
    return checked,edges,w,s


def linear(rows,v):
    return sum(((v&row).bit_count()&1)<<j for j,row in enumerate(rows))


def vector_frames():
    rng=Random(283)
    checks=0
    for k in range(1,7):
        n=1<<k
        for _ in range(20):
            a=[rng.randrange(n) for _ in range(k)]
            b=[rng.randrange(n) for _ in range(k)]
            mat=[x^y for x,y in zip(a,b)]
            s=rng.randrange(n)
            x=[rng.randrange(3) for i in range(n)]
            on_a=[x[i^linear(a,s)] for i in range(n)]
            on_b=[on_a[i^linear(mat,s)] for i in range(n)]
            assert on_b==[x[i^linear(b,s)] for i in range(n)]
            checks+=n
    return checks


def multiply(x,y,mod):
    k=mod.bit_length()-1
    out=0
    while y:
        if y&1:
            out^=x
        x<<=1
        if x&(1<<k):
            x^=mod
        y>>=1
    return out


def power(x,p,mod):
    out=1
    while p:
        if p&1:
            out=multiply(out,x,mod)
        x=multiply(x,x,mod)
        p//=2
    return out


def cubic(a,b,c,d,x,mod):
    return multiply(multiply(multiply(a,x,mod)^b,x,mod)^c,x,mod)^d


def normalize(a,b,c,d,mod):
    v=1<<(mod.bit_length()-1)
    if not a:
        return lambda x: multiply(b,multiply(x,x,mod),mod)^multiply(c,x,mod)^d
    h=multiply(b,power(a,v-2,mod),mod)
    eta=multiply(c,power(a,v-2,mod),mod)^multiply(h,h,mod)
    g=power(eta,v//2,mod) if eta else 1
    inv=power(g,v-2,mod)
    outscale=multiply(a,power(g,3,mod),mod)
    const=cubic(a,b,c,d,h,mod)

    def evaluate(x):
        u=multiply(inv,x^h,mod)
        y=power(u,3,mod)^(u if eta else 0)
        return multiply(outscale,y,mod)^const
    return evaluate


def cubic_tests():
    rng=Random(123)
    cases=points=0
    for mod in (3,7,11,19,37,67,131):
        k=mod.bit_length()-1
        n=1<<k
        assert all(power(i,n-1,mod)==1 for i in range(1,n))
        coeffs=product(range(n),repeat=4) if k<=3 else (
            tuple(rng.randrange(n) for _ in range(4)) for j in range(80))
        for a,b,c,d in coeffs:
            f=normalize(a,b,c,d,mod)
            assert all(f(x)==cubic(a,b,c,d,x,mod) for x in range(n))
            cases+=1
            points+=n
    return cases,points


if __name__=='__main__':
    print('scalar identities, directed side pairs, wires, total ranks',verify_incidence())
    print('binary frame data coordinates',vector_frames())
    print('cubic control configurations, checked named cells',cubic_tests())
