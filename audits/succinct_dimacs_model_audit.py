"""Exact small-bias rank, interpolation from supplied labels, and DIMACS lookup."""

from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import combinations, product
from random import Random
from subprocess import run

from three_file_interpolation_audit import gf_power, gf_product, linear_mask, poly_remainder


def gcd(a,b):
    while b:
        a,b=b,poly_remainder(a,b)
    return a


def irreducible(f):
    d=f.bit_length()-1
    if d<1:
        return False
    u=poly_remainder(2,f)
    z=u
    for i in range(1,d+1):
        z=gf_product(z,z,f)
        if i<=d//2 and gcd(f,z^u)!=1:
            return False
    return z==u


def random_modulus(d,rng):
    while True:
        f=(1<<d)|rng.getrandbits(d)
        if irreducible(f):
            return f


def trace(a,f):
    result=0
    for _ in range(f.bit_length()-1):
        result ^= a
        a=gf_product(a,a,f)
    assert result in (0,1)
    return result


def canonical_name(spelling):
    raw=spelling.encode('ascii') if isinstance(spelling,str) else spelling
    if not raw or any(c<48 or c>57 for c in raw):
        raise ValueError('expected an unsigned decimal identifier')
    raw=raw.lstrip(b'0')
    if not raw:
        raise ValueError('variable zero is not an identifier')
    return raw


def name_key(spelling,alpha,f):
    raw=canonical_name(spelling)
    h=1
    for digit in raw:
        for j in (3,2,1,0):
            h=gf_product(h,alpha,f)^((digit-48)>>j&1)
    return h


def trace_rows(indexes,x,f):
    d=f.bit_length()-1
    trmask=sum(trace(1<<j,f)<<j for j in range(d))
    rows=[]
    for idx in indexes:
        a=gf_power(x,idx,f)
        row=0
        for j in range(d):
            row |= ((a&trmask).bit_count()%2)<<j
            a=gf_product(a,2,f)
        rows.append(row)
    return rows


def gamma(n):
    assert n>0
    digits=format(n,'b')
    return '0'*(len(digits)-1)+digits


@dataclass(frozen=True)
class Seed:
    f: int
    g: int
    alpha: int
    x: int
    y: int

    def lookup(self,spelling):
        i=name_key(spelling,self.alpha,self.f)
        return trace(gf_product(self.y,gf_power(self.x,i,self.g),self.g),self.g)

    def encode(self):
        k,e=self.f.bit_length()-1,self.g.bit_length()-1
        blocks=((self.f^(1<<k),k),(self.g^(1<<e),e),(self.alpha,k),(self.x,e),(self.y,e))
        return gamma(k)+gamma(e)+''.join(format(a,f'0{d}b') for a,d in blocks)

    @classmethod
    def decode(cls,raw):
        pos=0
        def take(d):
            nonlocal pos
            if pos+d>len(raw):
                raise ValueError('truncated seed')
            out=int(raw[pos:pos+d],2)
            pos+=d
            return out
        def head():
            nonlocal pos
            end=raw.index('1',pos)
            d=end-pos+1
            pos=end
            return take(d)
        k,e=head(),head()
        ans=cls((1<<k)|take(k),(1<<e)|take(e),take(k),take(e),take(e))
        if pos!=len(raw):
            raise ValueError('trailing seed bits')
        return ans


def synthesize(model,N,rng):
    if N<0:
        raise ValueError('negative identifier-length bound')
    normalized={}
    for raw,value in model.items():
        name=canonical_name(raw)
        if value not in (0,1) or (name in normalized and normalized[name]!=value):
            raise ValueError('inconsistent prescribed assignment')
        normalized[name]=value
    names=list(normalized)
    v=len(names)
    if any(4*len(t)>N for t in names):
        raise ValueError('declared identifier-length bound too small')
    k=max(1,((N+1)*max(v*v,1)).bit_length())
    e=v+k+1
    f,g=random_modulus(k,rng),random_modulus(e,rng)
    while True:
        alpha=rng.randrange(1<<k)
        indices=[name_key(t,alpha,f) for t in names]
        if len(set(indices))==v:
            break
    while True:
        x=rng.randrange(1<<e)
        rows=trace_rows(indices,x,g)
        y=linear_mask(rows,[normalized[t] for t in names])
        if y is not None:
            seed=Seed(f,g,alpha,x,y)
            assert Seed.decode(seed.encode())==seed
            assert all(seed.lookup(t)==b for t,b in model.items())
            return seed


def bias_and_rank():
    rng=Random(2087)
    field=random_modulus(6,rng)
    tr=[trace(i,field) for i in range(64)]
    assert tr[1]==0 and sum(tr)==32  # even-degree trace still nondegenerate
    bits=[[gf_power(a,i,field) for i in range(4)] for a in range(64)]
    bias_cases=ranks=0
    for k in range(1,5):
        for ids in combinations(range(4),k):
            roots=signed=0
            for powers in bits:
                val=0
                for j in ids: val ^= powers[j]
                roots+=val==0
                signed+=sum(1-2*tr[gf_product(y,val,field)] for y in range(64))
            assert signed==64*roots and roots<=max(ids)
            bias_cases+=1
            if k<=3:
                bad=0
                for x in range(64):
                    rows=trace_rows(ids,x,field)
                    if linear_mask(rows,[0]*k) is None:
                        bad+=1
                    else:
                        for b in product(range(2),repeat=k):
                            y=linear_mask(rows,b)
                            assert tuple(tr[gf_product(y,bits[x][j],field)] for j in ids)==b
                            ranks+=1
                assert bad<32 and bad <= ((1<<k)-1)*3
    return bias_cases,ranks


def file_for(names, data, query):
    rows=[tuple(-j if v>>(j-1)&1 else j for j in (1,2,3)) for v in range(1,8)]
    for side in (data,query):
        rows.extend(((int(a) if side>>j&1 else -int(a)),1,2) for j,a in enumerate(names))
    return (f'p cnf {max(map(int,names))} {len(rows)}\n'+
            ''.join(f'{a} {b} {c} 0\n' for a,b,c in rows)).encode()


def audit(solver):
    rng=Random(7058)
    assert synthesize({'07':1,b'7':1}, 40, rng).lookup(b'0007')==1
    try:
        synthesize({'07':0,b'7':1}, 40, rng)
    except ValueError:
        pass
    else:
        raise AssertionError('conflicting aliases accepted')
    assert synthesize({},8,rng).lookup('9') in (0,1)
    biases,solutions=bias_and_rank()
    names=['10','101','347','2007']
    checked=solves=0
    for data in range(1<<len(names)):
        model={'1':0,'2':0,'3':0,**{a:data>>j&1 for j,a in enumerate(names)}}
        diagonal=file_for(names,data,data)
        seed=synthesize(model,8*len(diagonal),rng)
        for query in range(1<<len(names)):
            # Evaluate only these query clauses using the one diagonal model.
            assert seed.lookup('1')==seed.lookup('2')==0
            accept=all(seed.lookup(a)==(query>>j&1) for j,a in enumerate(names))
            assert accept==(query==data)
            if solver:
                raw=file_for(names,data,query)
                result=run([solver,'-q'],input=raw,check=False,capture_output=True)
                assert result.returncode==(10 if accept else 20)
                solves+=1
            checked+=1
    large='9'*5000
    model={large:1,large[:-1]+'8':0,'1'+large:1,'37':0,'703':1}
    seed=synthesize(model,8*sum(len(a) for a in model),rng)
    assert all(seed.lookup('000'+t)==wanted for t,wanted in model.items())
    print(f'{biases} exact parity-bias sums; {solutions:,} full-rank interpolation systems, '
          f'{checked} separated DIMACS queries, {solves} CaDiCaL checks; '
          '5,001-digit identifiers tested without conversion to machine integers.')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--solver',help='Optional CaDiCaL executable for the actual files.')
    audit(p.parse_args().solver)
