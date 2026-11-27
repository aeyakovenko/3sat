"""Physical one-bit files, numerical addresses, and a fixed three-step scan."""
from itertools import product
from random import Random

from ramsey_dimacs_word_audit import OPS, calculate


def positions(width):
    k = 0
    while 256**(k+1) <= width//128:
        k += 1
    assert width/32768 < 256**k <= width/128 and k > 0
    return k


def raw(width,k,d,tag):
    word = bytearray(b" "*(width//8))
    inside = f"{d} 1 0\n".encode()
    word[k:k+len(inside)] = inside
    word[-1] = ord(str(tag))
    return bytes(word)


def circular(a,b,mod):
    delta=(a-b)%mod
    return min(delta,mod-delta)


def layout(width,m):
    W=width//8
    head=f"p cnf 9 {m+17}\n".encode()
    # Every candidate low digit has the same printed length.
    def prefix(d):
        rows=[f"{l} {u} {v} 0\n".encode() for l in (-1,-d,4,-5)
              for u,v in product((2,-2),(3,-3))]
        data=head+b"".join(rows)
        return data+b" "*((-len(data)-1)%W)+b"4"
    first=len(prefix(6))//W
    ell=(first+m-1).bit_length()
    k=positions(width)
    for d in (6,7,8,9):
        a=raw(width,k,d,4)
        r=int.from_bytes(a,"little")%width
        if all(circular(r,z,width)>=width/100000 for z in (0,width/2,width-ell)):
            assert len(prefix(d))==first*W
            return prefix(d),a,raw(width,k,d,5),f" {d} 1 0\n".encode(),ell
    raise AssertionError("no residue")


def sat(file):
    header,rest=file.split(b"\n",1)
    p,cnf,n,c=header.split()
    assert (p,cnf,n)==(b"p",b"cnf",b"9")
    ints=list(map(int,rest.split()))
    assert len(ints)==4*int(c)
    rows=[]
    for i in range(0,len(ints),4):
        u,v,w,ending=ints[i:i+4]
        assert ending==0 and len({abs(u),abs(v),abs(w)})==3
        rows.append((u,v,w))
    names=sorted({abs(i) for row in rows for i in row})
    assert len(names)==6 and max(names)<=9
    for assign in product((0,1),repeat=len(names)):
        vals=dict(zip(names,assign))
        if all(any(vals[abs(t)]==(t>0) for t in row) for row in rows):
            return True
    return False


def file_test(width,m):
    prefix,a,b,trailer,_=layout(width,m)
    W=len(a)
    first=len(prefix)//W
    base=prefix+a*m+trailer
    for bits in product((0,1),repeat=m):
        file=prefix+b"".join((a,b)[x] for x in bits)+trailer
        diff={j//W for j,(u,v) in enumerate(zip(base,file)) if u!=v}
        assert diff=={first+i for i,x in enumerate(bits) if x}
        assert sum((x^y).bit_count() for x,y in zip(file,base))==sum(bits)
        assert sat(file)==(not any(bits))
        # The branch on equality doubles as the native loop backedge.
        pointer=first-1
        clock=0
        while True:
            pointer+=1
            word=file[pointer*W:(pointer+1)*W].ljust(W,b"\0")
            clock+=3
            if word!=a: break
        assert (pointer==first+m)==(not any(bits))
        if not any(bits): assert clock==3*m+3
    return 2**m


def small_values(width,m):
    prefix,wa,wb,_,ell=layout(width,m)
    a,b=[int.from_bytes(x,"little") for x in (wa,wb)]
    U=1<<width
    at=len(prefix)//len(wa)
    addr=range(at,at+m)
    assert (a-b)%(1<<ell)==0 and a%32==0
    rng=Random(width+m)
    pool=set(rng.getrandbits(width) for _ in range(96))
    # Include all close XOR, modular addition, and subtraction collaborators
    # and both inverse rotations, even at widths far exceeding the sample size.
    r=a%width
    for t in addr:
        pool.update(((a+t)%U,(a-t)%U,(t-a)%U,a^t,
                     ((t<<r)|(t>>(width-r)))%(U),
                     ((t>>r)|(t<<(width-r)))%(U)))
    checked=0
    ordinary={0,1,2,3,4}
    for y in sorted(pool|set(addr)):
        small_arithmetic=set()
        for rev in (False,True):
            left=calculate(y,a,width) if rev else calculate(a,y,width)
            right=calculate(y,b,width) if rev else calculate(b,y,width)
            for op,(t,alternative) in enumerate(zip(left,right)):
                if t not in addr or t==alternative:
                    continue
                if op in ordinary:
                    small_arithmetic.add(t)
                if op==5:
                    assert t%32==0
                if op in (9,10,11,12,13) and rev and a%width==b%width:
                    raise AssertionError("equal native shift counts disagreed")
            checked+=2*len(OPS)
        if y in addr: assert not small_arithmetic
        else: assert len(small_arithmetic)<=2
    return checked


def case_coverage():
    # A tiny independent fixed-width test hits the rare two-output arithmetic
    # situation in the general argument and checks the needed dichotomy.
    w,l=11,5
    U,D=1<<w,1<<l
    pairs=0
    for a in (390,403,415,422):
        for y in range(U):
            v={a&y,a|y,a^y,(a+y)%U,(a-y)%U,(y-a)%U}
            small={u for u in v if 0<u<D}
            assert len(small)<=2
            if len(small)==2:
                pairs+=1
    assert pairs
    return pairs



def reserve_shapes():
    # Full toy-word domain, with a congruent alternate. A candidate high scalar
    # needs two DIFFERENT later fresh addresses, hence its input scalar cannot
    # equal either of them, even if that input came from another instruction.
    w=12
    U=1<<w
    a=831
    b=a+12*64
    small=range(1,160)
    counts={}
    for z in range(U):
        for rev in (False,True):
            def run(raw):
                return calculate(z,raw,w) if rev else calculate(raw,z,w)
            for op,(y,edited) in enumerate(zip(run(a),run(b))):
                tau=a^y
                sigma=abs(a-y)
                if (y==edited or tau not in small or sigma not in small or tau==sigma
                    or z in (tau,sigma)):
                    continue
                if op in (6,7,8,9,10,11,12,13):
                    assert not rev
                    tag="shifted raw"
                elif op==5:
                    assert y==a*z%U
                    tag="product"
                elif z==(-sigma)%U:
                    assert op in (3,4)
                    tag="negative address"
                elif z==(a+y)%U:
                    assert op==4 and rev
                    tag="translated scalar"
                else:
                    raise AssertionError((op,z,y,rev,tau,sigma))
                counts[tag]=counts.get(tag,0)+1
    assert {"product","negative address","translated scalar"} <= set(counts)
    return counts


if __name__=="__main__":
    files=sum(file_test(w,6) for w in (32768,33024,49152))
    operations=sum(small_values(w,96) for w in (32768,33024,49152))
    print(f"{files} strict physical files, {operations} oriented numerical evaluations, "
          f"{case_coverage()} two-arithmetic-output controls")
    print("Exhaustive congruent reserve shapes", reserve_shapes())
