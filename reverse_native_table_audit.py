"""Reverse quotient and remainder lookup with one scalar and all divisor lanes."""
from itertools import product
from random import Random

from compiled_horn_receipt_audit import Circuit, exact_sat
from opposite_dense_clock_audit import xor


def reference(data, scalar, saturating):
    v = len(data)
    if saturating:
        zero_pair = (data[-1],data[scalar])
    else:
        zero_pair = (data[0],data[0])
    return ([zero_pair[0], *(data[scalar//i] for i in range(1,v))],
            [zero_pair[1], *(data[scalar%i] for i in range(1,v))])


def split_tables(data,scalar,log_cut,saturating):
    v = len(data)
    k = v.bit_length()-1
    assert 0<=log_cut<=k
    cut = 1<<log_cut
    cap = v//cut
    quot,rem = reference(data,scalar,saturating)
    threshold = [t<=scalar for t in range(v)]+[False]*v
    shifted = [data[(scalar-t)%v] for t in range(v)]
    delta = [0]*v
    for q in range(1,cap):
        delta[scalar//q] ^= data[q]^data[q-1]
    tail = data[0]
    for i in reversed(range(cut,v)):
        tail ^= delta[i]
        quot[i] = tail
        power = 1<<(i.bit_length()-1)
        survivors = [q for q in range(v//power)
                     if threshold[q*i] and not threshold[(q+1)*i]]
        assert len(survivors)==1
        rem[i] = shifted[(survivors[0]*i)%v]
    return quot,rem


def signed_eq(net,a,b):
    net.add(-a,b)
    net.add(a,-b)


def equal_words(net,left,right):
    value = net.one
    for a,b in zip(left,right):
        value = net.both(value,-xor(net,a,b))
    return value


def population(net,bits):
    if len(bits)==1:
        return list(bits)
    half = len(bits)//2
    a,b = population(net,bits[:half]),population(net,bits[half:])
    size = max(len(a),len(b))
    a += [-net.one]*(size-len(a))
    b += [-net.one]*(size-len(b))
    carry = -net.one
    out = []
    for x,y in zip(a,b):
        pair = xor(net,x,y)
        out.append(xor(net,pair,carry))
        carry = net.either(net.both(x,y),net.both(pair,carry))
    return out+[carry]


def little_unary(net,address,k,func):
    return [net.lookup(address,[net.literal(func(a)>>j&1) for a in range(1<<len(address))])
            for j in range(k)]


def file(v,cut,data_value,scalar_value,quotient_value,remainder_value,saturating):
    # Small finite arithmetic/lookup circuits can be explicit scalar tables.
    # Large-lane incidence, duplicate cancellation and popcount follow the manuscript.
    k = v.bit_length()-1
    cap = v//cut
    net = Circuit(True)
    data = [net.fresh() for _ in range(v)]
    scalar = [net.fresh() for _ in range(k)]  # Most significant first for Circuit.lookup.
    claimed_q = [net.fresh() for _ in range(v)]
    claimed_r = [net.fresh() for _ in range(v)]
    for words,bits in ((data,data_value),(claimed_q,quotient_value),(claimed_r,remainder_value)):
        for w,b in zip(words,bits):
            net.add(w if b else -w)
    for j,w in enumerate(reversed(scalar)):
        net.add(w if scalar_value>>j&1 else -w)
    signed_eq(net,claimed_q[0],data[-1] if saturating else data[0])
    signed_eq(net,claimed_r[0],net.lookup(scalar,data) if saturating else data[0])
    for i in range(1,cut):
        for words,op in [(claimed_q,lambda x:x//i),(claimed_r,lambda x:x%i)]:
            address = little_unary(net,scalar,k,op)
            signed_eq(net,words[i],net.lookup(list(reversed(address)),data))
    events = [little_unary(net,scalar,k,lambda x,q=q:x//q) for q in range(1,cap)]
    weights = [xor(net,data[q],data[q-1]) for q in range(1,cap)]
    flags = []
    for j,e in enumerate(events):
        first = net.one
        parity = -net.one
        for l,e2 in enumerate(events):
            eq = equal_words(net,e,e2)
            if l<j:
                first = net.both(first,-eq)
            parity = xor(net,parity,net.both(eq,weights[l]))
        flags.append(net.both(first,parity))
    delta = [net.fresh() for _ in range(v)]
    for flag,e in zip(flags,events):
        net.add(-flag,net.lookup(list(reversed(e)),delta))
    totals = population(net,delta)
    wanted = population(net,flags) if flags else [-net.one]
    for j in range(max(len(totals),len(wanted))):
        signed_eq(net,totals[j] if j<len(totals) else -net.one,
                  wanted[j] if j<len(wanted) else -net.one)
    tail = data[0]
    for i in reversed(range(cut,v)):
        tail = xor(net,tail,delta[i])
        signed_eq(net,claimed_q[i],tail)
    thresholds = [net.lookup(scalar,[net.literal(s>=t) for s in range(v)]) for t in range(v)]
    thresholds += [-net.one]*v
    shifted = [net.lookup(scalar,[data[(s-t)%v] for s in range(v)]) for t in range(v)]
    for i in range(cut,v):
        qcap = v//(1<<(i.bit_length()-1))
        bit = -net.one
        for q in range(qcap):
            active = net.both(thresholds[q*i],-thresholds[(q+1)*i])
            bit = net.either(bit,net.both(active,shifted[(q*i)%v]))
        signed_eq(net,claimed_r[i],bit)
    return net.bytes()


def semantic_tests():
    pairs = shifts = changes = 0
    for k in range(1,9):
        v = 1<<k
        # A bit mask of v independent coordinates checks every binary table
        # simultaneously by linearity, without choosing a single random table.
        data = [1<<i for i in range(v)]
        for s,cut,saturating in product(range(v),range(k+1),(False,True)):
            got = split_tables(data,s,cut,saturating)
            assert got==reference(data,s,saturating)
            pairs += 1
        for h,j in product(range(v),repeat=2):
            big = 4*v
            s=3*v+h
            i=2*v+j
            assert 0<=s<big and 0<i<big and s//i==1 and (s%i)%v==(h-j)%v
            shifts += 1
        for cut_log in range(k+1):
            cut = 1<<cut_log
            pairs_used = sum((v//(1<<(i.bit_length()-1))) for i in range(cut,v))
            assert pairs_used == v*(k-cut_log)
            changes += 1
    return pairs,shifts,changes


def select_little(net,bits,values):
    assert 0<len(values)<=1<<len(bits)
    return net.lookup(list(reversed(bits)),values+[-net.one]*((1<<len(bits))-len(values)))


def local_shift(net,bank,small_scalar,digit=2):
    size=len(bank)
    width=size.bit_length()-1
    for start in range(0,len(small_scalar),digit):
        bits=small_scalar[start:start+digit]
        radix=1<<len(bits)
        out=[]
        for i in range(size):
            high=i>>(start+len(bits))
            low=i% (1<<start)
            d=(i>>start)%(radix)
            # Duplicated adjacent digit blocks, including cyclic wrap.
            pair=[bank[(((high*radix+j)<<start) | low)%size] for j in range(2*radix)]
            out.append(select_little(net,bits,pair[d:d+radix]))
        bank=out
    assert len(bank)==1<<width
    return bank


def short_file(v,cut,xd,sdata,yd):
    k=v.bit_length()-1
    net=Circuit(True)
    data=[net.fresh() for _ in range(v)]
    claimed=[net.fresh() for _ in range(v)]
    sbits=[net.fresh() for _ in range(k)]
    for wires,values in ((data,xd),(claimed,yd)):
        for w,val in zip(wires,values):
            net.add(w if val else -w)
    for j,w in enumerate(reversed(sbits)):
        net.add(w if sdata>>j&1 else -w)
    target=net.lookup(sbits,data)
    signed_eq(net,claimed[0],target)
    for i in range(1,cut):
        addr=little_unary(net,sbits,k,lambda s,i=i:s%i)
        signed_eq(net,claimed[i],select_little(net,addr,data))
    for i in range(cut,v):
        zero_q=net.lookup(sbits,[net.literal(s<i) for s in range(v)])
        net.add(-zero_q,-claimed[i],target)
        net.add(-zero_q,claimed[i],-target)
    def at(t):
        return data[t] if 0<=t<v else -net.one
    def claim(t):
        return claimed[t] if 0<=t<v else -net.one
    for q in range(1,v//cut):
        M=power_cover(1+(v-1)//(q*(q+1)))
        mw=M.bit_length()-1
        B=power_cover(q)
        groups=power_cover((M+B-1)//B)
        spanbits=groups.bit_length()-1
        eword=little_unary(net,sbits,k,lambda s,q=q:s//q)
        rword=little_unary(net,sbits,(q-1).bit_length(),lambda s,q=q:s%q)
        # Select the preceding/current M-bit blocks from the claimed output.
        blocks=(v-1)//(q*M)+1
        high=eword[mw:]
        last=[select_little(net,high,[claim((h-1)*M+d) for h in range(blocks)]) for d in range(M)]
        current=[select_little(net,high,[claim(h*M+d) for h in range(blocks)]) for d in range(M)]
        shifted=local_shift(net,last+current,eword[:mw],1+(q%2))
        # Each aligned source block contributes at most two residues.
        pairs=[]
        public_residue=[0]*(q*groups)
        for p in range(q*groups):
            if p:
                public_residue[p]=(2*public_residue[p//2]+(p&1))%q
            values=[]
            for slot in (0,1):
                leaves=[]
                for r in range(1<<len(rword)):
                    u=(r-(B%q)*public_residue[p])%q +slot*q
                    leaves.append(at(B*p+u) if u<B else -net.one)
                values.append(select_little(net,rword,leaves))
            pairs.append(values)
        for j in range(M):
            active=net.lookup(sbits,[net.literal(j<max(0,s//q-max(cut-1,s//(q+1)))) for s in range(v)])
            h,d=divmod(j,B)
            leaves=[]
            for r in range(1<<len(rword)):
                if r>=q:
                    leaves.append(-net.one)
                    continue
                e,u=divmod(q*d+r,B)
                p=explicit_radix(h,e,q,spanbits,1+(q%2))
                leaves.append(pairs[p][int(u>=q)])
            xval=select_little(net,rword,leaves)
            yval=shifted[M-j]
            net.add(-active,-xval,yval)
            net.add(-active,xval,-yval)
    return net.bytes()


def power_cover(n):
    return 1<<(max(1,n)-1).bit_length()


def explicit_radix(j,e,q,span,chunk):
    # Normalize address q*j+e to high residual and ordinary low bits.
    h,low,width = j,0,0
    while width<span:
        step = min(chunk,span-width)
        base = 1<<step
        h,d = divmod(h,base)
        e,digit = divmod(q*d+e,base)
        assert e<q
        low |= digit<<width
        width += step
    assert h==0
    return (e<<span) | low


def window_validation(v,s,cut,check_each_bit=False):
    k=v.bit_length()-1
    indices = [None]*v
    indices[0]=0
    for i in range(1,min(cut,v)):
        indices[i]=s%i
    for i in range(max(cut,s+1),v):
        indices[i]=s
    packed_windows = scanned_inputs = reordered_scalars = routes = 0
    cap=v//cut
    for q in range(1,cap):
        endpoint,r = divmod(s,q)
        width=power_cover(1+(v-1)//(q*(q+1)))
        B=power_cover(q)
        # Pad j=B*h+d to a dyadic number of B-wide blocks, including small scales.
        groups=power_cover((width+B-1)//B)
        lookahead=q*groups+q
        source_pairs=[]
        residues=[0]*lookahead
        for p in range(lookahead):
            if p:
                residues[p]=(2*residues[p//2]+(p&1))%q
            u=(r-(B%q)*residues[p])%q
            source_pairs.append((B*p+u,B*p+u+q if u+q<B else None))
        scanned_inputs+=lookahead*B
        reordered_scalars+=2*q*groups
        packed_windows+=width
        start=max(cut,s//(q+1)+1)
        live=max(0,endpoint-start+1)
        assert live<=width
        hi,a=divmod(endpoint,width)
        for j in range(live):
            h,d=divmod(j,B)
            e,u=divmod(q*d+r,B)
            step=1+(k+q)%3
            p=explicit_radix(h,e,q,groups.bit_length()-1,step)
            target=source_pairs[p][int(u>=q)]
            out=(hi-1)*width+(width+a-j)%(2*width)
            assert out==endpoint-j and indices[out] is None
            indices[out]=target
            routes+=1
            if check_each_bit:
                assert target==s%out
        # Last e can equal q in q*d+r only if d=B, which is excluded.
    assert indices[1:]==[s%i for i in range(1,v)]
    return packed_windows,scanned_inputs,reordered_scalars,routes


def window_tests():
    configs=routes=transitions=0
    for k in range(1,9):
        v=1<<k
        for s in range(v):
            for l in range(k+1):
                _,_,_,rt=window_validation(v,s,1<<l,True)
                routes+=rt
                configs+=1
    for q in range(1,25):
        for width in range(6):
            for chunk in range(1,4):
                for j,e in product(range(1<<width),range(q)):
                    assert explicit_radix(j,e,q,width,chunk)==q*j+e
                    transitions+=1
    print(configs,"short-window instances;",routes,"live sites;",transitions,"mixed-radix normalization checks")


if __name__=='__main__':
    print("All-table linear checks, all cyclic projections, exact dyadic gate counts:",semantic_tests())
    rng = Random(2294710)
    files = total_bytes = 0
    for v in (4,8):
        for data_case in range(3):
            data = [rng.randrange(2) for _ in range(v)]
            for s in range(v):
                cut = 1<<(1+s%(v.bit_length()-1))
                for saturating in (False,True):
                    qt,rm = reference(data,s,saturating)
                    for fault in (0,1,2):
                        claim_q,claim_r = qt[:],rm[:]
                        if fault==1:
                            claim_q[(s+data_case)%v]^=1
                        if fault==2:
                            claim_r[(2*s+data_case+1)%v]^=1
                        raw = file(v,cut,data,s,claim_q,claim_r,saturating)
                        assert exact_sat(raw)==(fault==0)
                        files += 1
                        total_bytes += len(raw)
    print(files,"proper DIMACS verdicts;",total_bytes,"total bytes")
    window_tests()
    records=0
    for v in (4,8,16):
        for sdata in sorted({0,1,v//2,v-1}):
            xd=[rng.randrange(2) for _ in range(v)]
            expected=reference(xd,sdata,True)[1]
            for cut in (1,2,v//2):
                for fault in (None,0,sdata%v,(sdata+1)%v):
                    yd=expected[:]
                    if fault is not None:
                        yd[fault]^=1
                    raw=short_file(v,cut,xd,sdata,yd)
                    assert exact_sat(raw)==(fault is None)
                    records+=1
    print(records,"proper-CNF short-window certificates including one-bit corruptions")
