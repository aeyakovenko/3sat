"""Four-coordinate GF(4) transfer, sector packing, and the central cutoff."""
from itertools import product
from random import Random


def times(a,b):
    result=(a if b&1 else 0)^(a<<1 if b&2 else 0)
    return result ^ (7 if result&4 else 0)


def plus(values):
    total=0
    for entry in values:
        total ^= entry
    return total


IDENTITY=tuple(tuple(int(i==j) for j in range(4)) for i in range(4))
ZETA=tuple(tuple(int((j & ~i)==0) for j in range(4)) for i in range(4))


def diag(pos,val):
    return tuple(tuple(val if i==j==pos else int(i==j) for j in range(4)) for i in range(4))


def product_matrix(*terms):
    out=IDENTITY
    for matrix in terms:
        out=tuple(tuple(plus(times(out[i][j],matrix[j][k]) for j in range(4))
                        for k in range(4)) for i in range(4))
    return out


def perm(src,dst):
    rows=list(IDENTITY)
    rows[src],rows[dst]=rows[dst],rows[src]
    return tuple(rows)


def transfer():
    def monomial(matrix):
        return all(sum(x!=0 for x in row)==1 for row in matrix) and all(
            sum(row[i]!=0 for row in matrix)==1 for i in range(4))

    def inverse(word):
        result=[]
        for matrix in reversed(word):
            if matrix==ZETA or product_matrix(matrix,matrix)==IDENTITY:
                result.append(matrix)
            else:
                assert monomial(matrix)
                # Only single-coordinate nontrivial diagonals occur here.
                result.append(tuple(tuple(times(x,x) for x in row) for row in matrix))
        return result

    d3=diag(3,2)
    d0=diag(0,2)
    spread=[ZETA,d3,ZETA,*inverse([d3])]
    isolate=[*spread,d0,*inverse(spread),*inverse([d0])]
    unit=product_matrix(*isolate)[3][0]
    assert unit
    # Conjugating the isolated transvection by a row scale gives unit value.
    norm=diag(3,times(unit,unit))
    ele=[norm,*isolate,*inverse([norm])]
    assert product_matrix(*ele)==tuple(tuple(x ^ int(i==3 and j==0) for j,x in enumerate(row))
                                      for i,row in enumerate(IDENTITY))

    def operation(i,j,scalar):
        # Fixed coordinate relabeling sends source j and target i to 0,3.
        labels=[j,*[h for h in range(4) if h not in (j,i)],i]
        change=tuple(tuple(int(labels[c]==r) for c in range(4)) for r in range(4))
        back=tuple(zip(*change))
        scale=diag(i,scalar)
        return [scale,change,*ele,back,*inverse([scale])]

    omega=(1,2,3)
    fourier=tuple(tuple(omega[i*j%3] if i<3 and j<3 else int(i==j) for j in range(4))
                  for i in range(4))
    word=[]
    current=fourier
    for j in range(4):
        r=next(i for i in range(j,4) if current[i][j])
        swap=perm(j,r)
        scale=diag(j,times(current[r][j],current[r][j]))
        word.extend([swap,scale])
        current=product_matrix(scale,swap,current)
        for i in range(4):
            if i!=j and current[i][j]:
                elementary=operation(i,j,current[i][j])
                current=product_matrix(*elementary,current)
                # The full operation is a self-inverse transvection.
                word.extend(reversed(elementary))
    assert current==IDENTITY
    assert product_matrix(*reversed(word),fourier)==IDENTITY
    assert all(g==ZETA or monomial(g) for g in word)
    return len(word),sum(g==ZETA for g in word)


def sector_order(q):
    sizes=[3**mask.bit_count() for mask in range(1<<q)]
    offsets=[]
    total=0
    for n in sizes:
        offsets.append(total)
        total+=n
    assert total==4**q
    order=[]
    def visit(depth,mask,rank):
        if depth==q:
            order.append(offsets[mask]+rank)
            return
        for digit in range(4):
            active=(digit<3)
            visit(depth+1,2*mask+active,3*rank+digit if active else rank)
    visit(0,0,0)
    assert sorted(order)==list(range(total))
    for index,coords in enumerate(product(range(4),repeat=q)):
        mask=0
        rank=0
        for digit in coords:
            mask=2*mask+(digit<3)
            if digit<3: rank=3*rank+digit
        assert order[index]==offsets[mask]+rank
    return total


def zeta(values):
    result=list(values)
    for j in range((len(values)-1).bit_length()):
        for i in range(len(values)):
            if i>>j & 1:
                result[i] ^= result[i^(1<<j)]
    return result


def central_reconstruction():
    rng=Random(1933)
    cases=0
    for m in range(1,13):
        n=1<<m
        d=m//2
        for _ in range(12):
            x=[rng.getrandbits(13) for i in range(n)]
            low=zeta([a if i.bit_count()<=d else 0 for i,a in enumerate(x)])
            # The transposed, complemented truncated circuit computes all
            # unrestricted high rows; this direct small table is its matrix.
            transposed=list(reversed(x))
            for j in reversed(range(m)):
                for i in range(n):
                    if not ((i>>j)&1):
                        transposed[i]^=transposed[i^(1<<j)]
            for i in range(n):
                if i.bit_count()>d:
                    transposed[i]=0
            high=list(reversed(transposed))
            assert [a if i.bit_count()<=d else high[i] for i,a in enumerate(low)]==zeta(x)
            cases+=1
    return cases


if __name__=='__main__':
    print('fixed Fourier-block word length and zeta slots',transfer())
    print('sector packing coordinates',sum(sector_order(q) for q in range(8)))
    print('central-cut extensions',central_reconstruction())
