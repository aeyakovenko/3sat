"""Constant raw query words for grouped equality after arbitrary coordinate erasures."""

from argparse import ArgumentParser
from itertools import product
from random import Random
from subprocess import run

from packed_residue_dimacs import parse_proper_dimacs


def line(row):
    assert len(row)==3 and len(set(map(abs,row)))==3
    return (' '.join(map(str,row))+' 0\n').encode()


class XorProgram:
    """Wire numbers < m are input bits; -1 denotes the zero constant."""
    def __init__(self, m, gates, outputs):
        self.m,self.gates,self.outputs = m,tuple(gates),tuple(outputs)
        for i,(a,b) in enumerate(self.gates,m):
            if min(a,b)<-1 or max(a,b)>=i:
                raise ValueError('XOR operand is not available')
        if any(w < -1 or w >= m+len(self.gates) for w in self.outputs):
            raise ValueError('invalid final wire')

    @classmethod
    def from_columns(cls, cols, q):
        # Dense finite fixture; the compiler also accepts any supplied sparse XOR circuit.
        gates,outputs = [],[]
        for j in range(q):
            src = [i for i,c in enumerate(cols) if c >> j & 1]
            out = -1
            for i in src:
                if out==-1:
                    out=i
                else:
                    gates.append((out,i))
                    out=len(cols)+len(gates)-1
            outputs.append(out)
        return cls(len(cols),gates,outputs)

    def run(self, bits):
        wires = [bits >> i & 1 for i in range(self.m)]
        for a,b in self.gates:
            wires.append((wires[a] if a>=0 else 0) ^ (wires[b] if b>=0 else 0))
        return sum((wires[a] if a>=0 else 0) << j for j,a in enumerate(self.outputs))


class Layout:
    def __init__(self, k, groups, program):
        if k<1 or groups<1 or (groups & (groups-1)):
            raise ValueError('nonempty groups of a power-of-two count required')
        self.k,self.Q,self.code = k,groups,program
        self.gbits=groups.bit_length()-1
        self.q=k+self.gbits
        self.m=program.m
        if len(program.outputs)!=self.q or self.m<k*groups+self.q+1:
            raise ValueError('wrong output width or insufficient slots')
        self.rows = [tuple(-j if mask>>(j-1)&1 else j for j in (1,2,3)) for mask in range(1,8)]
        self.digits=max(1,len(str(self.m-1)))
        base=10**self.digits
        self.z=[5*base+i for i in range(self.m)]
        self.zero_names=[4*base+i for i in range(self.m)]
        self.maximum=5*base+self.m-1
        for a,b in zip(self.zero_names,self.z,strict=True):
            self.clause(a,b)
            self.clause(-a,-b)
        self.db = [self.wire() for _ in range(k*groups)]
        wires = self.z[:]
        for a,b in program.gates:
            wires.append(self.xor(wires[a] if a>=0 else 1,wires[b] if b>=0 else 1))
        x = [wires[i] if i>=0 else 1 for i in program.outputs]
        groups_equal = []
        for g in range(groups):
            matches = [-self.xor(self.db[g*k+j],x[self.gbits+j]) for j in range(k)]
            while len(matches)>1:
                rest = [matches[-1]] if len(matches)%2 else []
                matches = [self.conj(a,b) for a,b in zip(matches[::2],matches[1::2])]+rest
            groups_equal.append(matches[0])
        for control in x[:self.gbits]:
            groups_equal = [self.mux(control,lo,hi) for lo,hi in zip(groups_equal[::2],groups_equal[1::2],strict=True)]
        out, = groups_equal
        for name,want in ((4,-out),(5,out)):
            self.clause(-name,want)
            self.clause(name,-want)
        cap=24
        spec = [f'c pair-equality {k} {groups} {self.m} {len(program.gates)} {self.q}\n'.encode()]
        spec.extend(f'c xor {a} {b}\n'.encode() for a,b in program.gates)
        spec.extend(f'c output {w}\n'.encode() for w in program.outputs)
        self.head_words=(1+len(spec)+len(self.rows)+cap-1)//cap
        slots = self.head_words+2*self.m
        ell=1
        while (1<<ell)<1024*ell*slots+2:
            ell += 1
        self.W=128*ell
        self.width=8*self.W
        assert ell==(self.width*slots+1).bit_length()
        hdr=f'p cnf {self.maximum} {len(self.rows)+2*self.m}\n'.encode()
        parts=[]
        public=[hdr,*spec,*(line(row) for row in self.rows)]
        for j in range(self.head_words):
            content=b''.join(public[cap*j:cap*(j+1)])
            assert len(content)<=self.W
            parts.append(content.ljust(self.W,b' '))
        self.head=b''.join(parts)
        self.next_words=[f'{i:0{self.digits}d} 1 2 0\n'.encode().ljust(self.W,b' ') for i in range(self.m)]

    def wire(self):
        self.maximum += 1
        return self.maximum

    def clause(self,*args):
        vals=list(dict.fromkeys(args))
        if any(-v in vals for v in vals):
            return
        for j in (1,2,3):
            if len(vals)<3 and j not in set(map(abs,vals)):
                vals.append(j)
        assert len(vals)==3
        self.rows.append(tuple(vals))

    def xor(self,a,b):
        if a==1 or b==-1:
            return b if a==1 else -a
        if b==1 or a==-1:
            return a if b==1 else -b
        if abs(a)==abs(b):
            return 1 if a==b else -1
        z=self.wire()
        for x,y in product((0,1),repeat=2):
            self.clause(-a if x else a,-b if y else b,z if x^y else -z)
        return z

    def conj(self,a,b):
        if a==1 or b==1 or a==-b: return 1
        if a==-1 or a==b: return b
        if b==-1: return a
        z=self.wire()
        self.clause(-z,a)
        self.clause(-z,b)
        self.clause(z,-a,-b)
        return z

    def mux(self,c,x,y):
        if c==1: return x
        if c==-1: return y
        if x==y: return x
        z=self.wire()
        for ctrl,src in ((c,x),(-c,y)):
            self.clause(ctrl,-src,z)
            self.clause(ctrl,src,-z)
        return z

    def private(self,kind,value=0,ordinal=None):
        if value not in (0,1):
            raise ValueError('expected a bit')
        if kind=='seed':
            row=(-1,2,3)
            sign=b'5' if value else b'4'
        elif kind=='data':
            name=self.db[ordinal]
            row=(name if value else -name,1,2)
            sign=b'4'
        elif kind=='tag':
            row=(4+value,1,2)
            sign=b'4'
        else:
            raise ValueError(kind)
        return line(row).ljust(self.W-1,b' ')+sign

    def file(self,words):
        assert len(words)==self.m and all(len(a)==self.W for a in words)
        return self.head+b''.join(w+p for w,p in zip(words,self.next_words,strict=True))


def recognize(raw):
    """Return an exact verdict on a verified self-describing template, else None."""
    try:
        W=128*(8*len(raw)+1).bit_length()
        if len(raw)%W:
            return None
        physical=len(raw)//W
        lines=raw.splitlines()
        name=lines[1].split()
        if len(name)!=7 or name[:2]!=[b'c',b'pair-equality']:
            return None
        k,Q,m,g,q=map(int,name[2:])
        if not (1 <= k <= m <= physical//2 and 1 <= Q <= m and Q&(Q-1)==0 and
                q==k+Q.bit_length()-1 and k*Q+q+1<=m and 0<=g<=24*physical and
                2+g+q<=len(lines)):
            return None
        gate=[]
        for row in lines[2:2+g]:
            parts=row.split()
            if len(parts)!=4 or parts[:2]!=[b'c',b'xor']:
                return None
            gate.append(tuple(map(int,parts[2:])))
        outputs=[]
        for row in lines[2+g:2+g+q]:
            parts=row.split()
            if len(parts)!=3 or parts[:2]!=[b'c',b'output']:
                return None
            outputs.append(int(parts[2]))
        program=XorProgram(m,gate,outputs)
        z=Layout(k,Q,program)
        if z.W!=W or physical!=z.head_words+2*m or not raw.startswith(z.head):
            return None
        seed=z.private('seed',0)
        tags={z.private('tag',0):False,z.private('tag',1):True}
        tag=None
        values=[None]*len(z.db)
        wires=[]
        for i in range(m):
            a=(z.head_words+2*i)*W
            word=raw[a:a+W]
            if raw[a+W:a+2*W]!=z.next_words[i] or word[-1] not in (52,53):
                return None
            wires.append(word[-1]-52)
            normalized=word[:-1]+b'4'
            if normalized==seed:
                continue
            if normalized in tags:
                if tag is not None:
                    return None
                tag=tags[normalized]
                continue
            fields=normalized[:-1].split()
            if len(fields)!=4:
                return None
            lit,pad,pad2,zero=map(int,fields)
            pos=abs(lit)-z.db[0]
            if not 0<=pos<len(values) or values[pos] is not None or (pad,pad2,zero)!=(1,2,0):
                return None
            if normalized!=z.private('data',int(lit>0),pos):
                return None
            values[pos]=int(lit>0)
        if tag is None or None in values:
            return None
        for a,b in gate:
            wires.append((wires[a] if a>=0 else 0) ^ (wires[b] if b>=0 else 0))
        x=[wires[w] if w>=0 else 0 for w in outputs]
        group=sum(b<<j for j,b in enumerate(x[:z.gbits]))
        eq=values[group*k:(group+1)*k]==x[z.gbits:]
        return eq==tag
    except (ValueError,IndexError,AssertionError):
        return None


def independent(cols, erased=()):
    """Return a basis of survivor column positions and their triangular reductions."""
    excluded=set(erased)
    piv, indices={},[]
    for i,c in enumerate(cols):
        if i in excluded:
            continue
        t=c
        combination=1 << len(indices)
        while t:
            k=t.bit_length()-1
            if k not in piv:
                piv[k]=(t,combination)
                indices.append(i)
                break
            v,h=piv[k]
            t ^= v
            combination ^= h
    return indices,piv


def coefficients(piv, desired):
    out=0
    while desired:
        key=desired.bit_length()-1
        if key not in piv:
            raise ValueError('target outside survivor span')
        val,w=piv[key]
        desired ^= val
        out ^= w
    return out


def erasure_check(cols,q):
    d=min(sum((a&c).bit_count()%2 for c in cols) for a in range(1,1<<q))
    failures=[]
    rob=0
    for mask in range(1<<len(cols)):
        erased={j for j in range(len(cols)) if (mask>>j)&1}
        indices,piv=independent(cols,erased)
        if len(indices)<q:
            failures.append(len(erased))
        elif len(erased)<d:
            rob+=1
        if len(indices)==q and mask%127==0:
            for x in range(1<<q):
                w=coefficients(piv,x)
                y=0
                for j,i in enumerate(indices):
                    if w>>j&1: y ^= cols[i]
                assert y==x
    assert min(failures)==d
    return d,rob


def physical(solver):
    rng=Random(7257)
    checked=solved=headercomparisons=pivotal=0
    for k,Q,cols in ((3,1,list(range(1,8))+[1,2,3,4]),(2,2,[1,2,3,4,5,6,7,1]),(2,4,list(range(1,16)))):
        q=k+Q.bit_length()-1
        code=XorProgram.from_columns(cols,q)
        z=Layout(k,Q,code)
        alphabet={z.private('seed',0),z.private('seed',1)}
        tag_words={z.private('tag',0),z.private('tag',1)}
        assert sum((a^b).bit_count() for a,b in zip(*alphabet,strict=True))==1
        assert len(alphabet)==len(tag_words)==2
        assert len(alphabet|tag_words)==4
        d,rob=erasure_check(cols,q)
        print(f'q={q}, m={len(cols)}, minimum failed erasure={d}, {rob:,} smaller survivor spans verified.')
        examples = []
        for tag in range(z.m):
            order=list(range(z.m))
            rng.shuffle(order)
            used=[i for i in order if i!=tag][:(tag%min(d-1,len(z.db)+1))]
            examples.append((tag,used))
        for n,(tag,used) in enumerate(examples):
            basis,piv=independent(cols,set(used)|{tag})
            assert len(basis)==q and len(used)<d-1
            data=used+[i for i in range(z.m) if i not in used and i not in basis and i!=tag]
            data=data[:len(z.db)]
            assert len(data)==len(z.db)
            for db in (0,(1<<len(z.db))-1,rng.getrandbits(len(z.db))):
                for x in range(1<<q):
                    packed=coefficients(piv,x)
                    inputs=sum(((packed>>j)&1)<<pos for j,pos in enumerate(basis))
                    assert code.run(inputs)==x
                    g=x%z.Q
                    seek=x//z.Q
                    equal=(db>>(g*k))% (1<<k)==seek
                    vals=[z.private('seed',0) for _ in range(z.m)]
                    for j,pos in enumerate(data):
                        vals[pos]=z.private('data',db>>j&1,j)
                    for j,pos in enumerate(basis):
                        vals[pos]=z.private('seed',packed>>j&1)
                    files=[]
                    for tagbit in (0,1):
                        vals[tag]=z.private('tag',tagbit)
                        raw=z.file(vals)
                        clauses=parse_proper_dimacs(raw)
                        assert len(clauses)==len(z.rows)+2*z.m
                        for j in range(z.m):
                            a=(z.head_words+2*j)*z.W
                            assert raw[a:a+z.W]==vals[j] and raw[a+z.W:a+2*z.W]==z.next_words[j]
                            assert clauses[len(z.rows)+2*j+1] == ((z.z[j] if (inputs>>j)&1 else z.zero_names[j]),1,2)
                        assert raw[:len(z.head)]==z.head and 8*len(raw)==z.width*(z.head_words+2*z.m)
                        assert recognize(raw)==(equal==bool(tagbit))
                        if Q==1 and equal and ((n==0 and db==0) or (n==1 and db+1==1<<k)):
                            for j in range(z.m):
                                offset=(z.head_words+2*j+1)*z.W-1
                                mutated=bytearray(raw)
                                mutated[offset] ^= 1
                                alternate=bytes(mutated)
                                assert recognize(alternate)!=(equal==bool(tagbit))
                                assert len(parse_proper_dimacs(alternate))==len(clauses)
                                if solver:
                                    result=run([solver,'-q'],input=alternate,capture_output=True,check=False)
                                    assert result.returncode==(20 if equal==bool(tagbit) else 10)
                                    solved+=1
                                pivotal+=1
                        if solver and (checked%17==0 or (db==0 and n==0)):
                            res=run([solver,'-q'],input=raw,capture_output=True,check=False)
                            assert res.returncode==(10 if equal==bool(tagbit) else 20), (k,Q,db,x,tagbit)
                            solved+=1
                        files.append(raw)
                    a=(z.head_words+2*tag)*z.W
                    delta=[(j,v^w) for j,(v,w) in enumerate(zip(files[0][a:a+z.W], files[1][a:a+z.W],strict=True)) if v!=w]
                    assert delta==[(0,1)]
                    assert files[0][:a]==files[1][:a] and files[0][a+z.W:]==files[1][a+z.W:]
                    checked+=1
                    headercomparisons+=2
        silly=[z.private('seed',0)]*z.m
        silly[0]=z.private('tag',1)
        assert recognize(z.file(silly)) is None
        silly[1]=z.private('tag',0)
        assert recognize(z.file(silly)) is None
        assert recognize(z.file(silly).replace(b'c pair-equality',b'c pair-failcode',1)) is None
    print(f'{checked:,} one-bit opposite-tag pairs, {headercomparisons:,} complete DIMACS files, '
          f'{solved} CaDiCaL verdicts; {pivotal} individually pivotal private-slot flips at both signs in the one-group family.')


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--solver',help='Optional CaDiCaL path.')
    physical(parser.parse_args().solver)
