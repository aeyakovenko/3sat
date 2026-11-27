"""All Schur transversality queries through dimension three over GF(2)."""
from functools import lru_cache
from itertools import combinations, product


def span(rows):
    entries=[0]
    for row in rows:
        entries += [x ^ row for x in entries]
    return entries


def bases(k,d):
    """Reduced echelon bases for the k-planes in d coordinates."""
    for pivots in combinations(range(d), k):
        free=[(i,j) for i,p in enumerate(pivots) for j in range(p+1,d) if j not in pivots]
        for coefficients in range(1<<len(free)):
            rows=[1<<p for p in pivots]
            for pos,(i,j) in enumerate(free):
                rows[i] |= (coefficients>>pos&1)<<j
            yield rows


def apply(n,m,u):
    return sum((((m>>(n*i)) & u).bit_count()%2)<<i for i in range(n))


def rank(n,m):
    rows=[m>>(n*i)&((1<<n)-1) for i in range(n)]
    r=0
    for j in range(n):
        pivot=next((h for h in range(r,n) if rows[h]>>j&1),None)
        if pivot is None:
            continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        for h in range(r+1,n):
            if rows[h]>>j&1:
                rows[h]^=rows[r]
        r+=1
    return r


def is_matching(n,m):
    used=0
    for i in range(n):
        row=m>>(n*i)&((1<<n)-1)
        if row&(row-1) or row&used:
            return False
        used |= row
    return True


def matrices_times(n,a,b):
    columns=[apply(n,a,apply(n,b,1<<j)) for j in range(n)]
    return sum((col>>i&1)<<(n*i+j) for j,col in enumerate(columns) for i in range(n))


def sparse_three_tree(x):
    n=3
    identity=sum(1<<(n*i+i) for i in range(n))
    ones=(1<<(n*n))-1
    q=rank(n,identity ^ matrices_times(n,x,identity^ones))==3
    if not q:
        return rank(n,x)==3
    e13=1<<2
    return rank(n,identity ^ matrices_times(n,x,identity^e13))!=3


def plane_queries(n,matrices):
    full=(1<<len(matrices))-1
    points=[0]*(1<<(2*n))
    for i,m in enumerate(matrices):
        for u in range(1,1<<n):
            points[u+(apply(n,m,u)<<n)] |= 1<<i
    planes=[]
    masks=[]
    for rows in bases(n,2*n):
        members=span(rows)[1:]
        mask=full
        for x in members:
            mask &= ~points[x]
        planes.append(members)
        masks.append(mask)
    return full,points,planes,masks


def enumerate_costs(n,partial):
    matrices=[m for m in range(1<<(n*n)) if not partial or is_matching(n,m)]
    full,points,planes,masks=plane_queries(n,matrices)
    queries=set(masks)
    assert len(queries)==len(planes)=={2:35,3:1395}[n]
    counts=[0]*(n+1)
    for r in range(1<<(n*n)):
        target=sum(((r&m).bit_count()%2)<<i for i,m in enumerate(matrices))
        if target in (0,full): depth=0
        elif target in queries or (target^full) in queries: depth=1
        elif any((target^g) in queries or (target^g^full) in queries for g in queries): depth=2
        else: depth=3
        assert depth==rank(n,r)
        counts[depth]+=1
    ident=sum(1<<(i+n*i) for i in range(n))
    target=sum(((m&ident).bit_count()%2)<<i for i,m in enumerate(matrices))
    differences=[target^g for g in queries]
    @lru_cache(None)
    def one_more(domain):
        return any((d&domain) in (0,domain) for d in differences)
    two=any(one_more(mask) and one_more(full^mask) for mask in queries)
    assert two==(n==2 or partial)
    if n==3 and partial:
        for m in matrices:
            assert sparse_three_tree(m)==bool((m&ident).bit_count()%2)
    if n==3 and not partial:
        extensions=0
        # Test every rank<=2 prescribed map against every possible next plane.
        # The candidate set is represented as the exact bitset of completions.
        for dim in range(n):
            for domain_basis in bases(dim,n):
                domain=span(domain_basis)
                for images in product(range(1<<n),repeat=dim):
                    values=span(images)
                    domain_map=dict(zip(domain,values))
                    kept=full
                    for u,v in zip(domain_basis,images):
                        kept &= points[u+(v<<n)]
                    assert kept and kept&target and kept&(full^target)
                    for K,mask in zip(planes,masks):
                        if any(u in domain_map and domain_map[u]==v
                               for u,v in ((z&7,z>>3) for z in K) if u):
                            assert not kept&mask
                            continue
                        point=next((z for z in K if (z&7) not in domain_map),None)
                        if point is None:
                            assert kept&mask==kept
                        else:
                            new=kept&points[point]
                            assert new and not new&mask
                            extensions+=1
        print("Actual one-column adversary extensions",extensions)
    print(n,"sparse" if partial else "all",len(matrices),"matrices;",len(planes),
          "planes; XOR target counts by optimal depth",counts,"trace depth<=2",two)


if __name__=="__main__":
    for dimension in (2,3):
        for sparse in (False,True):
            enumerate_costs(dimension,sparse)
