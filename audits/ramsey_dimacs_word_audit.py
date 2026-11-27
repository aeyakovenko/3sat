"""Check native unary term colors and their physical ordinary-DIMACS realization."""
from itertools import product

OPS = ('and','or','xor','add','sub','mul','shl','shr','sar','shlmod','shrmod','sarmod','rol','ror','eq','lt','slt','ne','ge','sge')


def calculate(x, y, width):
    m = (1 << width) - 1
    sign = 1 << (width-1)
    signed = lambda a: a-(1 << width) if a & sign else a
    s = y % width
    sx, sy = signed(x), signed(y)
    return (
        x & y, x | y, x ^ y, (x+y)&m, (x-y)&m, (x*y)&m,
        ((x << y)&m) if y < width else 0, (x >> y) if y < width else 0,
        (sx >> min(y,width))&m, (x << s)&m, x >> s, (sx >> s)&m,
        ((x << s)|(x >> (width-s)))&m, ((x >> s)|(x << (width-s)))&m,
        int(x==y), int(x<y), int(sx<sy), int(x!=y), int(x>=y), int(sx>=sy))


def terms(x, width, gates):
    exact = [[x]]
    for num in range(1,gates+1):
        entries = []
        for left in range(num):
            right = num-1-left
            for a,b in product(exact[left],exact[right]):
                entries.extend(calculate(a,b,width))
        exact.append(entries)
    return [v for layer in exact for v in layer]


def record(name, width_bytes):
    data = (str(name)+" 1 2 0\n").encode()
    assert len(data) <= width_bytes
    return data.ljust(width_bytes,b" ")


def signature(exprs, width):
    levels = sorted(set(exprs))
    ranks = {v:i for i,v in enumerate(levels)}
    # Signed order is the unsigned cyclic order split at the sign bit.
    unsigned = tuple(ranks[x] for x in exprs)
    below_sign = sum(x < 1 << (width-1) for x in levels)
    return unsigned, below_sign


def collide(width_bytes, gates, first, limit, endian="little"):
    seen = {}
    for name in range(first, first+limit):
        a = int.from_bytes(record(name,width_bytes), endian)
        key = signature(terms(a, width_bytes*8, gates), width_bytes*8)
        if key in seen:
            return seen[key],name
        seen[key] = name
    return None


def check_ranks(a,b,width):
    assert len(a)==len(b)
    sign=1 << (width-1)
    comparisons=0
    for i,(x,u) in enumerate(zip(a,b)):
        for j in range(i):
            y,v=a[j],b[j]
            assert (x==y)==(u==v) and (x<y)==(u<v)
            assert ((x ^ sign) < (y ^ sign)) == ((u ^ sign) < (v ^ sign))
            comparisons+=3
    return comparisons


def encode(a,b,width_bytes,word_count,edits,total_bytes):
    pins=[]
    for literal in (-1,-2,a,-b):
        for u,v in product((3,-3),(4,-4)):
            pins.append(f"{literal} {u} {v} 0\n".encode())
    header=f"p cnf {max(a,b)} {word_count+len(pins)}\n".encode()
    prefix=header+b"".join(pins)
    prefix+=b" "*(-len(prefix)%width_bytes)
    assert prefix and len(prefix)%width_bytes==0
    body=b"".join(record(b if i in edits else a,width_bytes) for i in range(word_count))
    assert len(prefix+body)<=total_bytes
    return (prefix+body).ljust(total_bytes,b" "),len(prefix)//width_bytes


def ordinary_sat(file):
    line,rest=file.split(b"\n",1)
    fmt,kind,nvars,nclauses=line.split()
    assert (fmt,kind)==(b"p",b"cnf")
    tokens=list(map(int,rest.split()))
    assert len(tokens)==4*int(nclauses)
    clauses=[tuple(tokens[i:i+3]) for i in range(0,len(tokens),4)]
    assert all(tokens[4*i+3]==0 and len(set(map(abs,c)))==3 for i,c in enumerate(clauses))
    names=sorted({abs(z) for c in clauses for z in c})
    assert 0<min(names) and max(names)==int(nvars) and len(names)==6
    for bits in product((False,True),repeat=len(names)):
        assignment=dict(zip(names,bits))
        if all(any(assignment[abs(v)]==(v>0) for v in row) for row in clauses):
            return True
    return False


def main():
    total_comparisons=files_checked=0
    for W,gates,endian in ((16,1,"little"),(20,2,"little"),(24,2,"little"),
                            (32,2,"little"),(32,1,"big")):
        pair=collide(W,gates,10000,2000,endian)
        assert pair is not None
        a,b=pair
        raw=[int.from_bytes(record(x,W),endian) for x in (a,b)]
        levels=[terms(x,8*W,gates) for x in raw]
        assert len(levels[0])==[1,21,821][gates]
        total_comparisons+=check_ranks(*levels,8*W)
        count=7
        total_bytes=(count+30)*W+3
        base,at=encode(a,b,W,count,set(),total_bytes)
        assert at>0 and ordinary_sat(base)
        for bits in product((False,True),repeat=count):
            edits={i for i,v in enumerate(bits) if v}
            file,start=encode(a,b,W,count,edits,total_bytes)
            assert start==at and len(file)==len(base)==total_bytes
            changed={j//W for j,(u,v) in enumerate(zip(base,file)) if u!=v}
            assert changed=={at+i for i in edits}
            assert ordinary_sat(file)==(not edits)
            files_checked+=1
        print(f"{8*W} bits, {endian}-endian, {gates} gates, names {a}/{b}, "
              f"{len(levels[0])} unary terms")
    assert files_checked==640
    print(f"{files_checked} ordinary files, {total_comparisons:,} independent comparison outcomes")


if __name__=="__main__":
    main()
