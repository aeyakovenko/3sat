"""Thin exceptional cross-name values, retrieve the residue, and verify unnamed interfaces."""

from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from random import Random

from succinct_dimacs_model_audit import gf_product, random_modulus


def ceil_power(n):
    return 1 << max(0,(n-1).bit_length())


def polynomial(key, coefficients, modulus):
    ans = 0
    for c in reversed(coefficients):
        ans = gf_product(ans,key,modulus)^c
    return ans


@dataclass(frozen=True)
class Table:
    modulus: int
    filters: tuple
    left_hash: tuple
    right_hash: tuple
    side_size: int
    left: int
    right: int

    def lookup(self,key):
        if self.side_size == 0: return 0
        for coefficients, buckets, mask in self.filters:
            i = polynomial(key,coefficients,self.modulus) & (buckets-1)
            if not (mask>>i)&1: return 0
        left = polynomial(key,self.left_hash,self.modulus) & (self.side_size-1)
        right = polynomial(key,self.right_hash,self.modulus) & (self.side_size-1)
        return ((self.left>>left)^(self.right>>right))&1


def build(keys, positives, rng):
    keys = set(keys)
    positives = set(positives)
    assert positives <= keys
    if not positives:
        return Table(3,(),(),(),0,0,0)
    e = len(positives)
    degree = max(2,max(keys).bit_length(),(32*len(keys)).bit_length())
    universe = 1<<degree
    modulus = random_modulus(degree,rng)
    negatives = keys-positives
    filters = []
    buckets = ceil_power(4*e)
    while len(negatives)>e:
        coefficients = tuple(rng.randrange(universe) for _ in range(2))
        def index(k): return polynomial(k,coefficients,modulus) & (buckets-1)
        mask = 0
        for k in positives: mask |= 1<<index(k)
        survivors = {k for k in negatives if (mask>>index(k))&1}
        if 2*len(survivors)<=len(negatives):
            negatives=survivors
            filters.append((coefficients,buckets,mask))
    residue = positives|negatives
    side = ceil_power(8*len(residue))
    order = min(len(residue), len(residue).bit_length()+2)
    while True:
        left_hash = tuple(rng.randrange(universe) for _ in range(order))
        right_hash = tuple(rng.randrange(universe) for _ in range(order))
        adjacency=defaultdict(list)
        for key in residue:
            u=polynomial(key,left_hash,modulus)&(side-1)
            v=side+(polynomial(key,right_hash,modulus)&(side-1))
            adjacency[u].append((v,key)); adjacency[v].append((u,key))
        bits={}
        visits=set()
        cycle=False
        for root in adjacency:
            if root in bits: continue
            bits[root]=0
            stack=[root]
            while stack:
                u=stack.pop()
                for v,key in adjacency[u]:
                    if key in visits: continue
                    visits.add(key)
                    if v in bits:
                        cycle=True
                        continue
                    bits[v]=bits[u] ^ int(key in positives)
                    stack.append(v)
        if not cycle: break
    assert visits==residue
    left=sum(bit<<i for i,bit in bits.items() if i<side)
    right=sum(bit<<(i-side) for i,bit in bits.items() if i>=side)
    result=Table(modulus,tuple(filters),left_hash,right_hash,side,left,right)
    assert all(result.lookup(k)==(k in positives) for k in keys)
    return result


def models(names, clauses):
    for values in product((0,1),repeat=len(names)):
        a=dict(zip(names,values,strict=True))
        if all(any(a[abs(v)]==(v>0) for v in clause) for clause in clauses):
            yield a


def protocol(chunks, global_value):
    """Universal comparison rejects a disagreement only upon an actual outside occurrence."""
    for b,chunk in enumerate(chunks):
        names=sorted({abs(v) for row in chunk for v in row})
        def accepts(local):
            for i in names:
                if local[i]!=global_value(i):
                    for c,other in enumerate(chunks):
                        if c!=b and any(abs(v)==i for row in other for v in row):
                            return False
            return True
        if not any(accepts(local) for local in models(names,chunk)):
            return False
    return True


def audit():
    rng=Random(118815)
    patterns=lookups=filter_count=0
    for q in range(1,8):
        keys=rng.sample(range(1024),q)
        for bits in product((0,1),repeat=q):
            positives={i for i,v in zip(keys,bits,strict=True) if v}
            table=build(keys,positives,rng)
            assert all(table.lookup(i)==v for i,v in zip(keys,bits,strict=True))
            patterns+=1;lookups+=q;filter_count+=len(table.filters)
    for q,e in ((48,1),(128,5),(256,11),(1024,16)):
        keys=rng.sample(range(1<<18),q)
        positives=rng.sample(keys,e)
        table=build(keys,positives,rng)
        assert len(table.filters)>0
        patterns+=1;lookups+=q;filter_count+=len(table.filters)
    glue=omissions=0
    for case in range(20):
        n=5
        chunks=[]
        for b in range(2+case%3):
            permitted=[1,2,3] if case%4==0 and b==0 else list(range(1,n+1))
            piece=[]
            for _ in range(1+rng.randrange(4)):
                piece.append(tuple(i if rng.randrange(2) else -i for i in rng.sample(permitted,3)))
            chunks.append(piece)
        name_sets=[{abs(v) for row in piece for v in row} for piece in chunks]
        names=sorted(set.union(*name_sets))
        crossed={i for i in names if sum(i in ns for ns in name_sets)>1}
        allmodels=list(models(names,[row for piece in chunks for row in piece]))
        for raw in product((0,1),repeat=len(names)):
            baseline=dict(zip(names,raw,strict=True))
            # Incorrect global guesses and off-interface outputs are both legal.
            want=any(all(a[i]==baseline[i] for i in crossed) for a in allmodels)
            assert protocol(chunks,lambda i:baseline[i])==want
            omissions+=sum(1 for i in names if i not in crossed)
            glue+=1
    forbidden=[tuple(-i if v>>(i-1)&1 else i for i in (1,2,3)) for v in range(8)]
    for chunks in ((forbidden[:4],forbidden[4:]),(forbidden[::2],forbidden[1::2])):
        assert all(any(models([1,2,3],part)) for part in chunks)
        assert not any(models([1,2,3],forbidden))
        for raw in product((0,1),repeat=3):
            assert not protocol(chunks,lambda i:raw[i-1])
            glue+=1
    print(f'{patterns} prescribed label patterns, {lookups:,} constrained lookups, '
          f'{filter_count} negative-thinning stages; {glue} complete chunk/gluing games, '
          f'{omissions} off-interface name settings included.')


if __name__=='__main__':
    audit()
