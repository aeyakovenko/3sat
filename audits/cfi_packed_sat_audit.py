"""Hidden cubic parity as unannotated, uniformly renamed proper DIMACS."""
from collections import defaultdict
from itertools import combinations
from random import Random


def canonical_file(n, edges, twists, shuffle, fixed_sorts=False):
    incident = [[] for _ in range(n)]
    for e,(v,w) in enumerate(edges):
        incident[v].append(e)
        incident[w].append(e)
    assert all(len(es)==3 for es in incident)
    keys = [(typ,v,e,i) for typ in range(3) for v in range(n)
            for e in incident[v] for i in (0,1)]
    if fixed_sorts:
        keys += [(typ,v,-1,i) for typ in range(3) for v in range(n)
                 for i in range(8) if i.bit_count()%2==0]
    rng = Random(shuffle)
    low = 10**len(str(len(keys)))
    names = list(range(low,low+len(keys)))
    rng.shuffle(names)
    name = dict(zip(keys,names))
    clauses = []
    for v in range(n):
        for mask in range(8):
            if mask.bit_count()%2==0:
                clauses.append(tuple(name[0,v,e,(mask>>i)&1] for i,e in enumerate(incident[v])))
                if fixed_sorts:
                    clauses.extend([tuple(name[typ,v,-1,mask] for typ in (0,1,2))]*8)
        for e in incident[v]:
            other_v = edges[e][int(edges[e][0] == v)]
            for bit in (0,1):
                x = name[0,v,e,bit]
                twin = name[0,v,e,1-bit]
                other = name[0,other_v,e,bit ^ ((twists>>e)&1)]
                if fixed_sorts:
                    clauses.append(tuple(name[typ,v,e,bit] for typ in (0,1,2)))
                for sign in (1,-1):
                    clauses.extend([(x,twin,sign*name[1,v,e,bit]),
                                    (-x,-twin,sign*name[1,v,e,bit]),
                                    (x,-other,sign*name[2,v,e,bit]),
                                    (-x,other,sign*name[2,v,e,bit])])
    for i,c in enumerate(clauses):
        signed = list(c)
        rng.shuffle(signed)
        clauses[i] = signed
    rng.shuffle(clauses)
    return (f"p cnf {max(names)} {len(clauses)}\n" +
            "".join(" ".join(map(str,c))+" 0\n" for c in clauses)).encode()


def parse(raw):
    hdr,*lines = raw.splitlines()
    p,cnf,n,m = hdr.split()
    assert (p,cnf)==(b'p',b'cnf') and int(m)==len(lines)
    clauses = []
    for line in lines:
        a,b,c,end = map(int,line.split())
        assert end==0 and len({abs(a),abs(b),abs(c)})==3
        assert all(0<abs(l)<=int(n) for l in (a,b,c))
        clauses.append((a,b,c))
    return clauses


def tables(clauses):
    out = {}
    for c in clauses:
        c = sorted(c,key=abs)
        ids = tuple(map(abs,c))
        row = sum((lit<0)<<i for i,lit in enumerate(c))
        out[ids] = out.get(ids,255) & ~(1<<row)
    return out


PAIR_TABLES = {sum(1<<x for x in range(8) if ((x>>i)^(x>>j))&1==rhs):(i,j,rhs)
               for i,j in combinations(range(3),2) for rhs in (0,1)}
PARITY = {sum(1<<x for x in range(8) if x.bit_count()%2==rhs):rhs for rhs in (0,1)}


def recover(clauses):
    """Returns None if the residual format is unrecognized, otherwise a verdict/model."""
    small = tables(clauses)
    adj = defaultdict(list)
    residual = []
    for scope,table in small.items():
        if table in PAIR_TABLES:
            i,j,p = PAIR_TABLES[table]
            adj[scope[i]].append((scope[j],p))
            adj[scope[j]].append((scope[i],p))
        else:
            for v in range(8):
                if not table>>v&1:
                    residual.append(tuple(-lit if v>>i&1 else lit for i,lit in enumerate(scope)))
    names = {abs(l) for c in clauses for l in c}
    origin = {}
    for v in sorted(names):
        if v in origin:
            continue
        origin[v] = (v,0)
        queue = [v]
        while queue:
            x = queue.pop()
            for y,p in adj[x]:
                target = (v,origin[x][1]^p)
                if y in origin:
                    if origin[y]!=target:
                        return False,{}
                else:
                    origin[y]=target
                    queue.append(y)
    normalized = []
    for c in residual:
        row = []
        for lit in c:
            root,offset = origin[abs(lit)]
            row.append(-root if (lit<0)^offset else root)
        if len(set(map(abs,row)))!=3:
            return None
        normalized.append(row)
    signs = defaultdict(set)
    for c in normalized:
        for l in c:
            signs[abs(l)].add(l>0)
    pure = {x:int(next(iter(s))) for x,s in signs.items() if len(s)==1}
    normalized=[c for c in normalized if not any(abs(l) in pure for l in c)]
    eqs = []
    cols = defaultdict(list)
    for scope,t in tables(normalized).items():
        if t not in PARITY:
            return None
        eqs.append(PARITY[t])
        for var in scope:
            cols[var].append(len(eqs)-1)
    if any(len(es)!=2 for es in cols.values()):
        return None
    graph = defaultdict(list)
    for x,(a,b) in cols.items():
        graph[a].append((b,x))
        graph[b].append((a,x))
    roots = dict(pure)
    seen = set()
    for v in range(len(eqs)):
        if v in seen:
            continue
        seen.add(v)
        order = [v]
        parent = {}
        for a in order:
            for b,x in graph[a]:
                if b not in seen:
                    seen.add(b)
                    parent[b]=(a,x)
                    order.append(b)
        for b in order[1:][::-1]:
            a,x = parent[b]
            roots[x]=eqs[b]
            eqs[a]^=eqs[b]
        if eqs[v]:
            return False,{}
    return True,{x:(roots.get(idx,0)^bit) for x,(idx,bit) in origin.items()}


def packed_digit_audit(raw,width_bytes):
    """Test boundary-spanning chunk summaries; tabulate encountered chunks lazily here."""
    # The theorem builds all fixed-width summaries beforehand. This finite audit
    # compares emitted tokens for each encountered chunk to an independent parse.
    body = raw.split(b'\n',1)[1]
    out, partial, val, sign = [],False,0,1
    summaries = {}
    for p in range(0,len(body),width_bytes):
        cc = body[p:p+width_bytes]
        if cc not in summaries:
            i = 0
            pieces = []
            while i < len(cc):
                if 48<=cc[i]<=57:
                    j=i+1
                    while j<len(cc) and 48<=cc[j]<=57:
                        j+=1
                    pieces.append((0,int(cc[i:j]),j-i))
                    i=j
                elif cc[i] == 45:
                    pieces.append((1,0,0))
                    i+=1
                elif cc[i] in (10,32):
                    pieces.append((2,0,0))
                    i+=1
                else:
                    raise ValueError(cc)
            summaries[cc]=pieces
        for kind,d,l in summaries[cc]:
            if kind==0:
                val=val*(10**l)+d
                partial=True
            elif kind==1:
                assert not partial and sign==1
                sign=-1
            else:
                if partial:
                    out.append(sign*val)
                    partial,val,sign=False,0,1
                else:
                    assert sign==1
    assert not partial and sign==1
    assert out==[int(v) for v in body.split()]


def fixed_clause_form(rows):
    active = {abs(x) for c in rows for x in c}
    columns = {}
    for v in active:
        col = tuple((v in c) - (-v in c) for c in rows)
        columns[v] = col
    bins = defaultdict(list)
    for col in columns.values():
        bins[next(j for j,sg in enumerate(col) if sg)].append(col)
    out = [[] for _ in rows]
    for first,cols in bins.items():
        assert len(cols)<=3
        for k,col in enumerate(sorted(cols)):
            for j,sg in enumerate(col):
                if sg:out[j].append(sg*(3*first+k+1))
    return [sorted(c) for c in out]


def audit_one_side():
    rng = Random(541)
    for k in range(250):
        rows = [tuple(v if rng.randrange(2) else -v for v in rng.sample(range(1,8),3))
                for _ in range(1+k%8)]
        if k%10==0:
            rows=[(1,2,3),(-1,-2,3),(1,2,-3),(-1,-2,-3)]
        labels=rng.sample(range(10,120),7)
        other=[tuple(labels[abs(x)-1] if x>0 else -labels[abs(x)-1] for x in c) for c in rows]
        normal=fixed_clause_form(rows)
        assert normal==fixed_clause_form(other)
        def project(sol,clauses):
            vars=sorted({abs(l) for c in clauses for l in c})
            a={x:bool(sol>>j&1) for j,x in enumerate(vars)}
            return all(any(a[abs(l)]==(l>0) for l in c) for c in clauses)
        n=len({abs(l) for c in rows for l in c})
        assert sum(project(t,rows) for t in range(1<<n)) == sum(project(t,normal) for t in range(1<<n))
    return 250


def main():
    try:
        from pysat.solvers import Cadical195
    except ImportError:
        Cadical195 = None
    graphs = [list(combinations(range(4),2)),[(i,j) for i in range(3) for j in range(3,6)],
              [(i,(i+1)%5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]+[(i,i+5) for i in range(5)]]
    # A disconnected case ensures that cancellation between components is rejected.
    graphs.append(graphs[0]+[(x+4,y+4) for x,y in graphs[0]])
    rng = Random(812)
    checked,secondary = 0,0
    loads = []
    for g,edges in enumerate(graphs):
        n=max(v for e in edges for v in e)+1
        twists = range(1<<len(edges)) if g<=1 else [rng.randrange(1<<len(edges)) for _ in range(128)]
        for m,fixed in ((m,z) for m in twists for z in (False,True)):
            raw=canonical_file(n,edges,m,shuffle=m+207,fixed_sorts=fixed)
            clauses=parse(raw)
            verdict,model=recover(clauses)
            expected=m.bit_count()%2==0 if g<3 else ((m&63).bit_count()%2==0 and (m>>6).bit_count()%2==0)
            assert verdict==expected
            if verdict:
                assert all(any(model[abs(l)]==(l>0) for l in c) for c in clauses)
            if Cadical195 is not None:
                with Cadical195(bootstrap_with=clauses) as solver:
                    assert solver.solve()==verdict
                secondary+=1
            checked+=1
        if g<3:
            for baseline,fixed in ((0,False),(1,False),(0,True),(1,True)):
                raw=canonical_file(n,edges,baseline,shuffle=99,fixed_sorts=fixed)
                for q in (1,2,3,4,5,7,8,13,16):
                    packed_digit_audit(raw,q)
                wbytes=(3*(8*len(raw)+2).bit_length()+7)//8
                incidence=defaultdict(set)
                for e in range(len(edges)):
                    changed=canonical_file(n,edges,baseline^(1<<e),shuffle=99,fixed_sorts=fixed)
                    assert len(raw)==len(changed)
                    affected={i//wbytes for i,(a,b) in enumerate(zip(raw,changed)) if a!=b}
                    assert affected
                    for a in affected:incidence[a].add(e)
                loads.append((len(edges),max(map(len,incidence.values()))))
    print("actual DIMACS files, both verdicts, reconstructed models:",checked)
    print("independent CaDiCaL decisions:",secondary)
    print("(edges, maximum fields of different twists per changed packed word):",loads)
    print("boundary-spanning token traces:",12*9)
    print("fixed-clause canonical multiplicity checks:",audit_one_side())


if __name__ == '__main__':
    main()
