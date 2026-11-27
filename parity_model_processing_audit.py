"""Physical parity-compiler files, crossing names, and source-local model prediction."""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product
from random import Random
from subprocess import run


def expander_edges(side):
    """Bipartite double cover of eight shears and nine identity labels."""
    edges = []
    for x, y in product(range(side), repeat=2):
        left = x*side+y
        destinations = [(x,y)]*9
        for delta in (0, 1):
            for sign in (-1, 1):
                destinations.extend(((x+sign*(2*y+delta),y), (x,y+sign*(2*x+delta))))
        for u, v in destinations:
            edges.append((left, side*side+(u%side)*side+(v%side)))
    return edges


def parity(bits):
    return sum(bits) % 2


def native_trace(side, source):
    """A word-RAM execution using loads of the two endpoints at each edge."""
    block = [parity(source[i:i+side]) for i in range(0, len(source), side)]
    memory = [p for p in block for _ in range(side)]
    result = 0
    for u, v in expander_edges(side):
        result ^= memory[u] ^ memory[v]
    return memory, result


class Formula:
    def __init__(self):
        self.last = 5
        self.rows = [tuple(-j if pattern>>(j-1)&1 else j for j in (1,2,3))
                     for pattern in range(1,8)]
        self.rows.extend(((4,5,1),(-4,-5,1)))

    def new(self):
        self.last += 1
        return self.last

    def pin(self, name, value):
        self.rows.append((name if value else -name,1,2))

    def copy(self, source, dest):
        self.rows.extend(((-source,dest,1),(source,-dest,1)))

    def xor(self, x, y):
        z = self.new()
        self.rows.extend(((x,y,-z),(-x,-y,-z),(-x,y,z),(x,-y,z)))
        return z

    def xor_chain(self, names):
        result = names[0]
        for name in names[1:]:
            result = self.xor(result,name)
        return result

    def encode(self, extras=()):
        rows = self.rows + list(extras)
        assert all(len(set(map(abs,row)))==3 for row in rows)
        lines = [f'p cnf {self.last} {len(rows)}']
        # An explicit sign column prevents the source bits from shifting any later token.
        lines.extend(' '.join(f'{i: d}' for i in row)+' 0' for row in rows)
        return ('\n'.join(lines)+'\n').encode('ascii')


def compiler(side, source, tag):
    assert side % 2 == 1 and len(source) == 2*side**2
    f = Formula()
    block = []
    for begin in range(0,len(source),side):
        inputs = []
        for bit in source[begin:begin+side]:
            v = f.new()
            f.pin(v,bit)
            inputs.append(v)
        block.append(f.xor_chain(inputs))
    labels = []
    for i in range(2*side**2):
        v = f.new()
        labels.append(v)
        f.copy(block[i//side],v)
    edges = [f.xor(labels[u],labels[v]) for u,v in expander_edges(side)]
    f.copy(f.xor_chain(edges),4)
    f.pin(4 if tag else 5,True)
    return f, labels


def actual_files(solver):
    rng = Random(16594)
    count = forced = source_mutations = 0
    for side in (1,3,5):
        n = 2*side**2
        for trial in range(8):
            data = tuple(rng.randrange(2) for _ in range(n))
            labels, value = native_trace(side,data)
            assert value == parity(data)
            good, names = compiler(side,data,value)
            bad, _ = compiler(side,data,1-value)
            positive, negative = good.encode(), bad.encode()
            assert sum((a^b).bit_count() for a,b in zip(positive,negative,strict=True)) == 1
            mutation = trial % n
            other = data[:mutation]+(1-data[mutation],)+data[mutation+1:]
            f2,_ = compiler(side,other,value)
            b2 = f2.encode()
            assert len(positive)==len(b2) and sum(a!=b for a,b in zip(positive,b2))==1
            source_mutations += 1
            if solver:
                def solve(raw):
                    p = run([solver,'-q'],input=raw,capture_output=True,check=False)
                    assert p.returncode in (10,20)
                    return p.returncode==10
                assert solve(positive) and not solve(negative) and not solve(b2)
                sampled = sorted({0,n-1,trial % n})
                for site in sampled:
                    wrong = -names[site] if labels[site] else names[site]
                    assert not solve(good.encode(((wrong,1,2),)))
                    forced += 1
            count += 2
    return count,forced,source_mutations


def cube_crossings():
    # Exhaust every equal partition of the cube edges into two or three parts.
    edges = [(a,a^(1<<k)) for a in range(8) for k in range(3) if a < (a^(1<<k))]
    def test(parts):
        owners = [set() for _ in range(8)]
        for color,part in enumerate(parts):
            for e in part:
                u,v=edges[e]
                owners[u].add(color)
                owners[v].add(color)
        crossed = sum(len(f)>1 for f in owners)
        # The cube has edge expansion 1 on sets of at most four vertices.
        assert 3*crossed >= 8-crossed
        return crossed
    all_edges = set(range(12))
    cases = 0
    minima = []
    for k in (6,4):
        least = 8
        for choice in combinations(range(1,12),k-1):
            first = set((0,*choice))
            rest = all_edges-first
            if k==6:
                least=min(least,test((first,rest)))
                cases+=1
            else:
                least_rest = min(rest)
                for next_part in combinations(sorted(rest-{least_rest}),k-1):
                    second = set((least_rest,*next_part))
                    least=min(least,test((first,second,rest-second)))
                    cases+=1
        minima.append(least)
    return cases,minima


def exhaustive_one_probe(d):
    """Optimal one advice bit and <=1 read per parity, two d-bit source blocks."""
    bits=2*d
    allrows=(1<<(1<<bits))-1
    raw=[0]*bits
    parities=[0,0]
    for a in range(1<<bits):
        for i in range(bits):
            raw[i] |= ((a>>i)&1)<<a
        for g in range(2):
            b=((a>>(g*d)) & ((1<<d)-1)).bit_count()%2
            parities[g] |= b<<a
    rules=[0,allrows]+raw+[r^allrows for r in raw]
    # On one probe every Boolean guess is constant, the raw bit, or its complement.
    losses=[]
    for u,v in product(rules, repeat=2):
        e0,e1=u^parities[0],v^parities[1]
        losses.append((e0 | e1,e0 & e1))
    score=2*(1<<bits)
    tests=0
    for i,(some,both) in enumerate(losses):
        for other_some,other_both in losses[i:]:
            errors=(some & other_some).bit_count() + (both & other_both).bit_count()
            score=min(score,errors)
            tests+=1
    assert 4*score == 2*(1<<bits)
    return tests


def adaptive_erasure_audit():
    rng=Random(91511)
    m,d,D=3,3,2
    source_count=1<<(m*d)
    random_trees=[rng.sample(range(m*d),3) for _ in range(2*m)]
    decorations=[rng.randrange(16) for _ in range(2*m)]
    def predictor(x,s,g):
        control=s*m+g
        root,left,right=random_trees[control]
        a=(x>>root)&1
        t=right if a else left
        b=(x>>t)&1
        label=(decorations[control]>>(2*a+b))&1
        return label,{root,t}
    misses=altered=tests=errors=decoded=0
    for x in range(source_count):
        target=[((x>>(i*d)) & ((1<<d)-1)).bit_count()%2 for i in range(m)]
        s=min(range(2),key=lambda s: sum(predictor(x,s,i)[0]!=p for i,p in enumerate(target)))
        for pick in product(range(d),repeat=m):
            hidden={d*i+k for i,k in enumerate(pick)}
            y=x
            for j in hidden: y &= ~(1<<j)
            for g,p in enumerate(target):
                predicted,path=predictor(x,s,g)
                simulated,_=predictor(y,s,g)
                hit=bool(hidden & path)
                assert simulated==predicted or hit
                tests+=1
                misses+=hit
                altered+=simulated!=predicted
                errors+=predicted!=p
                decoded+=simulated!=p
    assert misses*d <= tests*D and decoded <= errors+misses and altered<=misses
    return tests,misses,altered


def simplex_prediction(solver):
    """A [7,3,4] simplex code, enhanced to dimension four and length fourteen."""
    source_bits = 14
    supports = []
    for bit in range(3):
        word = sum(((v>>bit)&1) << i for i,v in enumerate(range(1,8)))
        supports.append(word | (word<<7))
    last = 127<<7
    for word in supports:
        last ^= word
    supports.append(last)
    weights=[]
    for mask in range(1,16):
        combination=0
        for g in range(4):
            if mask>>g&1: combination ^= supports[g]
        weights.append(combination.bit_count())
    assert min(weights)==7 and weights[-1]==7
    fixed=Counter()
    adaptive=Counter()
    rng=Random(88236)
    trees=[rng.sample(range(source_bits),3) for _ in range(4)]
    for data in range(1<<source_bits):
        errors_a=errors_b=0
        for g,word in enumerate(supports):
            actual=(data&word).bit_count()%2
            # Four two-bit predictions together compute the true aggregate parity.
            # Consequently their error vector is three-wise but not four-wise uniform.
            partition=((data>>(7+2*g))&3).bit_count()%2
            root,left,right=trees[g]
            a=(data>>root)&1
            b=(data>>(right if a else left))&1
            errors_a |= (actual^partition)<<g
            errors_b |= (actual^a^b)<<g
        fixed[errors_a]+=1
        adaptive[errors_b]+=1
    marginals=0
    for hist in (fixed,adaptive):
        for mask in range(1,15):
            observed=Counter()
            for val,count in hist.items(): observed[val&mask]+=count
            assert len(observed)==1<<mask.bit_count()
            assert set(observed.values())=={1<<(source_bits-mask.bit_count())}
            marginals+=1
    assert set(fixed.values())=={1<<11} and all(x.bit_count()%2==0 for x in fixed)
    physical=0
    if solver:
        for trial in range(8):
            data=rng.randrange(1<<source_bits)
            f=Formula()
            raw=[]
            for i in range(source_bits):
                v=f.new(); f.pin(v,(data>>i)&1); raw.append(v)
            outputs=[f.xor_chain([raw[i] for i in range(source_bits) if word>>i&1]) for word in supports]
            edge_labels=[f.xor(outputs[i],outputs[j]) for i,j in combinations(range(4),2)]
            f.copy(f.xor_chain(edge_labels),4)
            wanted=(data>>7).bit_count()%2
            for sign in (0,1):
                encoded=f.encode(((4 if sign else 5,1,2),))
                ans=run([solver,'-q'],input=encoded,capture_output=True,check=False)
                assert ans.returncode==(10 if sign==wanted else 20)
                physical+=1
    return marginals,physical


def compact_byte(n, block_size, tag, position, read):
    """Local output byte of the replacement compiler, computing at most one source block."""
    relevant = n//2
    blocks = (relevant+block_size-1)//block_size
    assert blocks >= 1
    last = 5+blocks+(blocks-1)
    count = 9 + blocks + 4*(blocks-1) + 3
    stride = max(27, 5*(len(str(max(last,count)))+2))
    length = (1+count)*stride
    if position is None: return length
    row,offset=divmod(position,stride)
    if row == 0:
        line=f'p cnf {last} {count}'
    else:
        r=row-1
        if r<7:
            lits=tuple(-j if (r+1)>>(j-1)&1 else j for j in (1,2,3))
        elif r<9:
            lits=((4,5,1),(-4,-5,1))[r-7]
        elif r<9+blocks:
            g=r-9
            val=parity([read(relevant+i) for i in range(g*block_size,min(relevant,(g+1)*block_size))])
            lits=(6+g if val else -(6+g),1,2)
        elif r<9+blocks+4*(blocks-1):
            g,k=divmod(r-9-blocks,4)
            a=6 if g==0 else 6+blocks+g-1
            b=7+g
            out=6+blocks+g
            lits=((a,b,-out),(-a,-b,-out),(-a,b,out),(a,-b,out))[k]
        else:
            q=r-9-blocks-4*(blocks-1)
            lits=((-last,4,1),(last,-4,1),(4 if tag else 5,1,2))[q]
        line=' '.join(f'{lit: d}' for lit in lits)+' 0'
    text=line.ljust(stride-1)+'\n'
    assert len(text)==stride
    return ord(text[offset])


def compact_audit(solver):
    rng=Random(44129)
    files=probes=0
    for n,block_size in ((2,1),(14,2),(38,4),(102,9)):
        source=[rng.randrange(2) for _ in range(n)]
        for tag in (0,1):
            seen=[]
            def read(i):
                seen.append(i)
                return source[i]
            size=compact_byte(n,block_size,tag,None,read)
            assert not seen
            data=bytearray()
            for j in range(size):
                seen.clear()
                data.append(compact_byte(n,block_size,tag,j,read))
                assert len(seen)<=block_size and all(n//2<=i<n for i in seen)
                probes+=len(seen)
            if solver:
                ans=run([solver,'-q'],input=data,capture_output=True,check=False)
                assert ans.returncode==(10 if tag==parity(source[n//2:]) else 20)
            files+=1
    return files,probes


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--solver')
    args=parser.parse_args()
    physical,forced,mutations=actual_files(args.solver)
    parts,minima=cube_crossings()
    code_pairs=sum(exhaustive_one_probe(d) for d in (3,4,5))
    traces,hits,changed=adaptive_erasure_audit()
    marginals,coded=simplex_prediction(args.solver)
    compact,compact_probes=compact_audit(args.solver)
    print(f'{physical} signed files; {forced} contrary model pins; {mutations} source flips; '
          f'{parts:,} cube partitions, minimum shared names {minima}; {code_pairs:,} '
          f'one-advice-bit predictor pairs, optimal error 1/4; {traces:,} adaptive erasure paths, '
          f'{hits:,} hitting a hidden source bit and {changed:,} changed predictions; '
          f'{marginals} exact coded-error marginals, 16,384 sources and {coded} coded physical files; '
          f'{compact} local replacement files, {compact_probes:,} audited source probes.')
