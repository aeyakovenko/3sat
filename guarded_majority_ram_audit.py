"""Exact full-word counts and guarded DIMACS short-circuiting. Stdlib only."""

from collections import Counter
from itertools import combinations, product
from math import comb
from random import Random


def skeleton(height):
    leaves = 3**height
    size = (3*leaves - 1)//2
    first_leaf = (leaves - 1)//2
    pins = [tuple(-j if mask >> (j-1) & 1 else j for j in (1,2,3))
            for mask in range(8) if mask != 4]
    rows = pins + [(4,1,2)]
    for i in range(first_leaf):
        a,b,c = (5+3*i+j for j in range(3))
        z = 4+i
        rows.extend([(-z,a,b),(-z,a,c),(-z,b,c)])
    declared = len(rows) + leaves
    prefix = f"p cnf {size+3} {declared}\n" + "".join(
        " ".join(map(str, row))+" 0\n" for row in rows)
    nbytes = 512*(leaves+1)*(leaves+2).bit_length()
    width = 2*(((8*nbytes+1).bit_length()+15)//16)
    raw = bytearray(prefix.encode())
    raw.extend(b" "*(-len(raw)%width))
    slots = []
    for i in range(leaves):
        prefix = f"-{4+first_leaf+i} 1 ".encode()
        assert len(prefix) < 8*width
        raw.extend(prefix.ljust(8*width))
        slots.append(len(raw))
        raw.extend(b" "*(width-1) + b"2")
        raw.extend(b"\n0\n".ljust(3*width))
    assert len(raw) < nbytes and all(offset%width == 0 for offset in slots)
    raw.extend(b" "*(nbytes-len(raw)))
    return raw, slots, width


def set_words(base, slots, width, bits):
    data = base.copy()
    for start,b in zip(slots,bits):
        data[start+width-1] = 50+b
    return data


def parse(data):
    header, tail = data.split(b"\n", 1)
    name, fmt, bound, count = header.split()
    assert (name,fmt) == (b"p",b"cnf")
    rows = []
    current = []
    for tok in tail.split():
        lit = int(tok)
        if lit:
            assert abs(lit) <= int(bound)
            current.append(lit)
        else:
            rows.append(tuple(current))
            current = []
    assert not current and len(rows) == int(count)
    return rows


def sat(rows):
    """Small DPLL, independent of the tree and slot layout."""
    def fixed(lit, clauses):
        return [tuple(x for x in row if x != -lit) for row in clauses if lit not in row]
    while rows:
        shortest = min(rows, key=len)
        if not shortest:
            return False
        lit = shortest[0]
        if len(shortest) > 1:
            return sat(fixed(lit, rows)) or sat(fixed(-lit, rows))
        rows = fixed(lit, rows)
    return True


def direct(bits, height, reverse=False):
    """Read each pending child until its parent's value is determined."""
    seen = []
    def descend(start, h):
        if h == 0:
            seen.append(start)
            return bits[start]
        stride = 3**(h-1)
        offsets = (2,1,0) if reverse else (0,1,2)
        a,b,c = (start+i*stride for i in offsets)
        u,v = descend(a,h-1),descend(b,h-1)
        return u if u==v else descend(c,h-1)
    return descend(0,height), seen


def majority(bits):
    vals = list(bits)
    while len(vals)>1:
        vals = [int(sum(vals[i:i+3]) >= 2) for i in range(0,len(vals),3)]
    return vals[0]


def entries(size):
    """A chunk encodes most significant frame at its root."""
    table = []
    for frame in range(4**size):
        offset = 0
        for i in reversed(range(size)):
            offset = 3*offset+(0,1,1,2)[(frame>>(2*i))&3]
        updates = []
        for b in (0,1):
            for i in range(size):
                status = (frame>>(2*i))&3
                if status==0 or status==2-b:
                    replacement = 1+b if status==0 else 3
                    top = (frame>>(2*i+2))<<(2*i+2)
                    updates.append(top | (replacement<<(2*i)))
                    break
            else:
                updates.append(None)
        table.append((offset,updates))
    return table


def transducer(height):
    """Returns an evaluator using at most four chunk transitions per read."""
    chunk = max(1,(height+3)//4)
    sizes = [min(chunk,height-i) for i in range(0,height,chunk)]
    tables = [entries(s) for s in sizes]
    weights = [3**sum(sizes[:j]) for j in range(len(sizes))]
    def evaluate(bits):
        chunks = [0]*len(sizes)
        trace = []
        while True:
            i = sum(w*t[c][0] for w,t,c in zip(weights,tables,chunks))
            trace.append(i)
            bit = bits[i]
            for j,t in enumerate(tables):
                change = t[chunks[j]][1][bit]
                if change is not None:
                    chunks[j] = change
                    break
                chunks[j] = 0
            else:
                return bit, trace
    return evaluate


def first_complete_edges(height):
    size = 3**height
    masks = list(product((0,1), repeat=size))
    evaluate = transducer(height)
    leaves = Counter()
    full_edges = set()
    total = 0
    for bits in masks:
        answer,path = evaluate(bits)
        assert (answer,path)==direct(bits,height) and answer==majority(bits)
        assert len(path)==len(set(path))
        total += (-1)**(size-sum(bits))*answer
        if len(path)==size:
            leaves[answer] += 1
            y = list(bits)
            y[path[-1]] ^= 1
            verdict, other_path = evaluate(y)
            assert verdict != answer and path == other_path
            full_edges.add(tuple(sorted((bits,tuple(y)))))
    expected = 2**((size-1)//2)
    assert leaves == {0:expected,1:expected} and len(full_edges) == abs(total) == expected
    return leaves[1]


def physical():
    checked = corrupted = 0
    for h in range(3):
        base,slots,width = skeleton(h)
        for bits in product((0,1), repeat=len(slots)):
            raw = set_words(base,slots,width,bits)
            rows = parse(raw)
            assert all(len(row)==len(set(map(abs,row)))==3 for row in rows)
            ans,seen = direct(bits,h)
            assert sat(rows) == bool(ans)
            checked += 1
            if h!=1:
                continue
            # Missing slots can declare an arbitrary literal, extra literals,
            # or a binary clause; the fixed terminators keep one clause each.
            for i in set(range(len(bits)))-set(seen):
                for word in (b"",b"1",b"-1",b"2",b"3",b"4",b"-4",b"6",b"-6",b"2 3"):
                    if len(word) > width:
                        continue
                    data = raw.copy()
                    data[slots[i]:slots[i]+width] = word.rjust(width)
                    assert sat(parse(data))==bool(ans)
                    corrupted += 1
    return checked,corrupted


def hybrid_short(bits, height, radius):
    """Branch-free stack navigation apart from returning or taking the next leaf."""
    width = 2*radius+1
    even_bits = (4**height-1)//3
    block = ones = visited = 0
    trace = []
    while True:
        i = width*block + visited
        trace.append(i)
        ones += bits[i]
        visited += 1
        if ones <= radius and visited-ones <= radius:
            continue
        b = int(ones > radius)
        eligible = even_bits & ~(block if b else block>>1)
        if not eligible:
            return b,trace
        t = eligible & -eligible
        block = ((block & ~(t-1)) | t) if b else ((block & ~(4*t-1)) | (2*t))
        ones = visited = 0


def hybrid_recursive(bits, height, radius):
    width = 2*radius+1
    trace = []
    def descend(block,level):
        if level:
            args = [block+i*4**(level-1) for i in range(4)]
            return (descend(args[0],level-1) and descend(args[1],level-1) or
                    descend(args[2],level-1) and descend(args[3],level-1))
        yes = 0
        for j in range(width):
            i = width*block+j
            trace.append(i)
            yes += bits[i]
            if yes > radius or j+1-yes > radius:
                return int(yes > radius)
    return descend(0,height),trace


def hybrid_rows(height, radius, bits):
    """Build and count with the explicit gate equivalences of the wider tree."""
    width = 2*radius+1
    k = 4**height
    first_block = (k-1)//3
    leaf_base = 4 + first_block + k
    fresh = leaf_base+len(bits)
    rows = [tuple(-j if mask >> (j-1) & 1 else j for j in (1,2,3))
            for mask in range(8) if mask != 4]
    rows.append((4,1,2))

    def emit(row):
        if any(-u in row for u in row):
            return
        unique = list(dict.fromkeys(row))
        for dummy in (1,2,-3):
            if len(unique)==3:
                break
            if abs(dummy) not in map(abs,unique):
                unique.append(dummy)
        assert len(unique)==len(set(map(abs,unique)))==3
        rows.append(tuple(unique))

    def gate(u,v,func):
        nonlocal fresh
        output = fresh
        fresh += 1
        for a,b in product((0,1),repeat=2):
            emit((-u if a else u,-v if b else v,output if func(a,b) else -output))
        return output

    xor = lambda u,v: gate(u,v,lambda a,b:a^b)
    conjunction = lambda u,v: gate(u,v,lambda a,b:a&b)
    disjunction = lambda u,v: gate(u,v,lambda a,b:a|b)
    def full_adder(a,b,c):
        d = xor(a,b)
        return xor(d,c),disjunction(conjunction(a,b),conjunction(c,d))

    for i in range(first_block):
        a,b,c,d = (5+4*i+j for j in range(4))
        for p,q in product((a,b),(c,d)):
            emit((-(4+i),p,q))
    for i in range(k):
        buckets = [[leaf_base+i*width+j for j in range(width)]]
        j = 0
        while j < len(buckets):
            bucket = buckets[j]
            while len(bucket)>=3:
                total,carry = full_adder(bucket.pop(),bucket.pop(),bucket.pop())
                bucket.append(total)
                if j+1==len(buckets):
                    buckets.append([])
                buckets[j+1].append(carry)
            j += 1
        carry = 1
        result = []
        for bucket in buckets:
            a,b = (bucket+[1,1])[:2]
            total,carry = full_adder(a,b,carry)
            result.append(total)
        result.append(carry)
        # Compare binary sum against r+1 from least significant upward.
        ge = 3
        for j,u in enumerate(result):
            ge = conjunction(u,ge) if (radius+1)>>j & 1 else disjunction(u,ge)
        emit((-(4+first_block+i),ge))
    for i,b in enumerate(bits):
        emit((-(leaf_base+i),1,2+b))
    return rows


def hybrid_audit():
    rng = Random(7483)
    for h,r in ((0,0),(0,1),(0,2),(0,3),(1,0),(1,1)):
        blocks = 4**h
        size = blocks*(2*r+1)
        full_count = Counter()
        signs = [set(),set()]
        for vals in product((0,1),repeat=size):
            b,seen = hybrid_short(vals,h,r)
            assert (b,seen)==hybrid_recursive(vals,h,r)
            signs[b].add(sum(value<<i for i,value in enumerate(vals)))
            if len(seen)==size:
                full_count[b] += 1
                flip = list(vals)
                flip[seen[-1]] ^= 1
                assert hybrid_short(flip,h,r) == (1-b,seen)
        count = comb(2*r,r)**blocks
        assert full_count == {0:count,1:count}
        # For every assignment, exactly k is the minimum certificate. Mark
        # all monochromatic fibers at depths k and k-1 independently.
        k = (r+1)*2**h
        for depth in (k,k-1):
            certified = set()
            for subset in combinations(range(size),depth):
                mask = sum(1<<i for i in subset)
                outputs = [{x & mask for x in sign} for sign in signs]
                clash = outputs[0] & outputs[1]
                certified.update(x for x in range(1<<size) if x & mask not in clash)
            assert len(certified) == (1<<size if depth==k else 0)
    for h,r in ((2,4),(3,7),(6,3)):
        for _ in range(30):
            vals = [rng.randrange(2) for _ in range(4**h*(2*r+1))]
            assert hybrid_short(vals,h,r)==hybrid_recursive(vals,h,r)
    physical_cases = 0
    for h,r,trials in ((0,2,32),(1,1,16),(1,2,16)):
        size = (2*r+1)*4**h
        for trial in range(trials):
            bits = ([(trial>>i)&1 for i in range(size)] if h==0
                    else [rng.randrange(2) for _ in range(size)])
            rows = hybrid_rows(h,r,bits)
            assert sat(rows)==bool(hybrid_recursive(bits,h,r)[0])
            physical_cases += 1
    print(f"Exact certificate and last-word counts on six hybrid trees, 90 larger navigation traces, "
          f"{physical_cases} threshold-circuit CNFs checked with DPLL")


if __name__ == "__main__":
    print("Full-read disjoint pivotal edges by height 0,1,2:",
          [first_complete_edges(h) for h in range(3)])
    rng = Random(743)
    count = 0
    for h in range(3,9):
        evaluate = transducer(h)
        for _ in range(30):
            bits = [rng.randrange(2) for _ in range(3**h)]
            assert evaluate(bits)==direct(bits,h)
            count += 1
    print(f"{count} larger traces reproduce every probe through height 8")
    checked, corrupt = physical()
    print(f"{checked} whole proper DIMACS files and {corrupt} off-face guarded completions")
    hybrid_audit()
