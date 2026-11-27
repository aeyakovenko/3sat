"""Exact tests of the scalar triple center, framed translations and true carries.

NumPy performs integer modular matrix arithmetic for small tensor fibers.
The large parameter check uses only ordinary integer combinatorics.
"""
from itertools import combinations, product
from math import comb
from random import Random
import numpy as np


def center_and_count():
    h=22
    entries=[sum(1<<i for i in tr) for tr in combinations(range(h),3)]
    v=len(entries)
    degree=3*comb(h-3,2)
    neighbors=sum((a&b).bit_count()==1 for a in entries for b in entries)
    assert neighbors==v*degree
    for a in entries:
        for b in entries:
            inter=(a&b).bit_count()
            assert (inter%2)^int(inter-1==0)==int(a==b)
    m=(h+1)**3
    W=2*v**3+3*v*v*(neighbors+h)
    S=2*v**3*(m-1)+3*v*v*(neighbors*m+h*(m+2*(h+1)))
    assert W*m-S==2*v*v*(v-3*h*(h+1))>0
    return v*v,W,S,W*m-S


def scalar_invocations(h, trials):
    triples=[set(t) for t in combinations(range(h),3)]
    neighbors=[(i,j) for i,s in enumerate(triples) for j,t in enumerate(triples)
               if len(s&t)==1]
    rng=Random(14111+h)
    def run(x,y,side,center,reverse):
        def add_side():
            for p,(i,j) in enumerate(neighbors): y[i]^=side[p]
        def add_center():
            for i,tri in enumerate(triples):
                for b in tri: y[i]^=center[b]
        def side_input():
            for p,(i,j) in enumerate(neighbors): side[p]^=x[j]
        def center_input():
            for i,tri in enumerate(triples):
                for b in tri: center[b]^=x[i]
        ops=[add_side,add_center,side_input,center_input,add_center,add_side,center_input,side_input]
        for op in (reversed(ops) if reverse else ops): op()
    for _ in range(trials):
        x=[rng.randrange(256) for t in triples]
        y=[rng.randrange(256) for t in triples]
        a=[rng.randrange(256) for p in neighbors]
        c=[rng.randrange(256) for i in range(h)]
        xx,yy,aa,cc=x[:],y[:],a[:],c[:]
        run(x,y,a,c,False)
        assert y==[u^v for u,v in zip(xx,yy)] and a==aa and c==cc
        run(y,x,a,c,True)
        run(x,y,a,c,False)
        assert x==yy and y==xx and a==aa and c==cc
    return trials


def identity(size):
    return np.eye(size,dtype=np.int64)


def tensor(*terms):
    answer=np.ones((1,1),dtype=np.int64)
    for value in terms:
        answer=np.kron(answer,value)
    return answer


def rank_pivots(mat):
    array=mat.copy()%3
    rows=list(range(len(array)))
    pivot_rows=[]
    pivot_columns=[]
    r=0
    for j in range(array.shape[1]):
        active=np.flatnonzero(array[r:,j])
        if not len(active): continue
        i=r+int(active[0])
        array[[r,i]]=array[[i,r]]
        rows[r],rows[i]=rows[i],rows[r]
        pivot_rows.append(rows[r])
        pivot_columns.append(j)
        row=array[r]*pow(int(array[r,j]),-1,3)%3
        array[r+1:]=(array[r+1:]-array[r+1:,j,None]*row)%3
        r+=1
        if r==len(array): break
    return pivot_rows,pivot_columns


def inverse_mod(matrix,r):
    n=len(matrix)
    a=np.concatenate([matrix%r,identity(n)],axis=1)
    for j in range(n):
        pivot=j+int(np.flatnonzero(a[j:,j]%3)[0])
        a[[j,pivot]]=a[[pivot,j]]
        a[j]=(a[j]*pow(int(a[j,j]),-1,r))%r
        multiples=a[:,j].copy()
        multiples[j]=0
        a=(a-multiples[:,None]*a[j])%r
    assert np.array_equal(a[:,:n],identity(n))
    return a[:,n:]


def edge_test(x,y,modulus):
    mat=(y-x)%modulus
    rows,cols=rank_pivots(mat)
    if not rows:
        assert not np.any(mat)
        return 0
    sub=mat[np.ix_(rows,cols)]
    fac=inverse_mod(sub,modulus)
    assert np.array_equal((mat[:,cols]@fac@mat[rows,:])%modulus,mat)
    return len(cols)


def rank_incidence(h=5,r=27):
    d=h+1
    jform=identity(d)
    jform[-1,-1]=-1
    def projection(coords):
        u=np.zeros(d,dtype=np.int64)
        u[coords]=1
        u[-1]=1
        return (np.outer(u,u@jform)*pow(2,-1,r))%r
    tx=projection([0,1,2])
    ty=projection([0,3,4])
    assert not np.any((tx@ty)%r)
    assert np.array_equal(tx@tx%r,tx)
    assert np.array_equal(ty@ty%r,ty)
    m=d**3
    full=identity(m)
    zero=np.zeros_like(full)
    count=0
    for stage in range(3):
        pre=identity(d**stage)
        prev=tensor(*([tx]*stage))%r
        B=(pre-prev)%r
        Q=tensor(*([tx]*(2-stage)))%r
        space=tensor(pre,identity(d),Q)%r
        l0=tensor(B,ty,Q)%r
        l1=tensor(B,identity(d),Q)%r
        l2=(l1+tensor(prev,tx,Q))%r
        l5=(l1+tensor(prev,identity(d)-ty,Q))%r
        in_x=tensor(pre,tx,Q)%r
        in_y=tensor(B,ty,Q)%r
        for seq,predicted in [
            ([in_x,l2,space,space,space],d**stage*(d-1)),
            ([in_y,l0,l1,l1,l5],d**stage*(d-1)),
            ([zero,l0,l2,l5,space,full],m),
            ([zero,l1,space,l1,space,full],m+2*d),
        ]:
            total=0
            for left,right in zip(seq,seq[1:]):
                total+=edge_test(left,right,r)
                count+=1
            assert total==predicted
    line=tensor(tx,tx,tx)%r
    change=(full-2*line)%r
    assert np.array_equal(change@change%r,full)
    return count


def source_sink_frames():
    """A two-wire XOR swap with genuinely nonzero input/output frames."""
    rng=Random(531)
    count=0
    for r in (3,9):
        inds=list(product(range(r), repeat=2))
        zero=((0,0),(0,0))
        full=((1,0),(0,1))
        X=((1,0),(0,0))
        Y=((0,0),(0,1))
        Ms=[zero,X,full,Y,zero]
        def mv(M,v):
            return tuple(sum(a*b for a,b in zip(row,v))%r for row in M)
        def diff(a,b):
            return tuple(tuple((x-y)%r for x,y in zip(p,q)) for p,q in zip(a,b))
        def translate(a,v):
            return {u:a[tuple((x+y)%r for x,y in zip(u,v))] for u in inds}
        # Matched inputs X/zero go to Y/full, so AY=Y-X=diag(-1,1), AX=I.
        A=diff(Y,X)
        for s in inds:
            x={u:rng.randrange(2) for u in inds}
            y={u:rng.randrange(2) for u in inds}
            regs=[{u:x[mv(A,u)] for u in inds},y.copy()]
            labels=[X,zero]
            for label,dest in zip(Ms[:3],(1,0,1)):
                for i in range(2):
                    regs[i]=translate(regs[i],mv(diff(label,labels[i]),s))
                    labels[i]=label
                regs[dest]={u:regs[dest][u]^regs[1-dest][u] for u in inds}
            for i,final in enumerate((full,Y)):
                regs[i]=translate(regs[i],mv(diff(final,labels[i]),s))
            assert regs[0]==translate(y,s)
            assert {u:regs[1][mv(A,u)] for u in inds}==translate(x,s)
            count+=1
    return count


def carries():
    total=0
    for radices in [(3,3),(3,3,3),(9,9),(3,9,3),(2,4,2),(4,4,2)]:
        volume=1
        lows=[]
        for base in radices:
            lows.append(volume)
            volume*=base
        for s in range(volume):
            # Pullback by independent digit additions on an address-identity bank.
            values=[sum(((j//low+s//low)%base)*low for low,base in zip(lows,radices))
                    for j in range(volume)]
            for low,base in zip(lows[1:],radices[1:]):
                prev=values
                values=[]
                for j in range(volume):
                    carry=(j%low+s%low)>=low
                    digit=(j//low)%base
                    new=j+(((digit+carry)%base)-digit)*low
                    values.append(prev[new])
            assert values==[(j+s)%volume for j in range(volume)]
            total+=volume
    return total


if __name__=='__main__':
    print('h=22: entries of RG, W, S, Wm-S',center_and_count())
    print('random complete forward/reverse swaps',sum(scalar_invocations(h,12) for h in range(5,10)))
    print('tensor edge ranks and factorizations modulo 27',rank_incidence())
    print('nonzero source/sink frame translations',source_sink_frames())
    print('fully composed carry positions',carries())
