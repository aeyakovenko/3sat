"""Check the literal interpolation payload and an anchored three-test census."""

from itertools import combinations, product
from math import lcm

from anchored_literal_census_audit import decode as prefix_bits, encode as tagged_literal
from table_probe_context_audit import parse, truth_table_sat


def smallest_modulus(words):
    integers = [int('1'+bits, 2) for bits in words]
    assert len(set(integers)) == len(integers)
    modulus = 1
    while len({x % modulus for x in integers}) < len(words):
        modulus += 1
    bound = 2 + (max(map(len, words))+1)*len(words)*(len(words)-1)//2
    assert modulus <= bound
    return modulus


def residue(bits, modulus):
    r = 1 % modulus
    for bit in bits:
        r = (2*r + int(bit)) % modulus
    return r


def tree(rows):
    if len(rows) == 1:
        return rows[0][1]
    first = rows[0][0]
    # Any distinguishing column suffices. Every residue in the input is unique.
    xor = next(x ^ first for x, _ in rows if x != first)
    pos = (xor & -xor).bit_length()-1
    left = [row for row in rows if not (row[0] >> pos) & 1]
    right = [row for row in rows if (row[0] >> pos) & 1]
    return pos, tree(left), tree(right)


def delta(n):
    raw = bin(n)[2:]
    length = bin(len(raw))[2:]
    return '0'*(len(length)-1) + length + raw[1:]


def encode_tree(node, field):
    if isinstance(node, bool):
        return '0' + str(int(node))
    pos, left, right = node
    bits = format(pos, f'0{field}b') if field else ''
    return '1' + bits + encode_tree(left,field) + encode_tree(right,field)


def make_literal(words, labels, modulus):
    field = (modulus.bit_length()-1).bit_length()
    root = tree([(residue(bits, modulus), label) for bits,label in zip(words,labels)])
    bits = delta(modulus) + encode_tree(root,field)
    assert len(bits) == len(delta(modulus)) + 2*len(words) + (len(words)-1)*(1+field)
    return tagged_literal(tuple(map(int,bits))), len(bits)


class PayloadReader:
    def __init__(self, bits):
        self.bits = tuple(bits)
        self.used = 0

    def read(self, count):
        if self.used + count > len(self.bits):
            raise ValueError("truncated field")
        value = 0
        for j in range(self.used, self.used+count):
            value = 2*value + self.bits[j]
        self.used += count
        return value

    def delta(self):
        zeros = 0
        while self.read(1) == 0:
            zeros += 1
        length = (1 << zeros) | self.read(zeros)
        tail = self.read(length-1)
        return (1 << (length-1)) | tail

    def node(self, length):
        if self.read(1) == 0:
            return bool(self.read(1))
        pos = self.read((length-1).bit_length())
        if pos >= length:
            raise ValueError("invalid residue bit position")
        return pos, self.node(length), self.node(length)


def unpack(word, width):
    data = prefix_bits(word,width)
    if data is None:
        return None
    reader = PayloadReader(data)
    try:
        m = reader.delta()
        root = reader.node(m.bit_length())
        return (m,root) if reader.used == len(reader.bits) else None
    except ValueError:
        return None


def evaluate(model, bits):
    m, node = model
    r = residue(bits,m)
    while not isinstance(node,bool):
        j, left, right = node
        node = right if r & (1<<j) else left
    return node


def table(words, labels, modulus):
    lit, length = make_literal(words,labels,modulus)
    width = 2*(length+1)
    model = unpack(lit,width)
    assert model is not None and model[0] == modulus
    assert [evaluate(model,bits) for bits in words] == list(labels)
    for smaller in (0, width-2, width-1):
        assert unpack(lit,smaller) is None
    for extension in (-1,0,13):
        extended = (extension<<width) | lit
        assert unpack(extended,width+22) == model
    return width


def all_tiny():
    words = [format(x, f'0{n}b') if n else '' for n in range(4) for x in range(1<<n)]
    tables = 0
    for k in (1,2,3,4):
        for sample in combinations(words,k):
            m = smallest_modulus(sample)
            assert [residue(s,m) for s in sample] == [int('1'+s,2)%m for s in sample]
            for labels in product((False,True),repeat=k):
                table(sample,labels,m)
                tables += 1
    return tables


def dimacs_files():
    public = [(a,b,c) for a in (1,-1) for b,c in ((2,-3),(-2,3),(-2,-3))]
    prefix = b'p cnf 3 8\n'+b''.join(('%d %d %d 0\n'%row).encode() for row in public)
    return [prefix + s+b'1 2 3 0\n'+t+b'1 2 3 0\n'
            for s,t in product((b' ',b'-'),repeat=2)]


def packed_stream(raw, modulus, lane):
    # Read least-addressed bytes first from little-endian memory. The
    # integer being hashed appends each byte in its printed/MSB-first order.
    r = 1 % modulus
    for k in range(0,len(raw),lane):
        fragment = raw[k:k+lane]
        word = int.from_bytes(fragment, 'little')
        for j in range(len(fragment)):
            r = (256*r + ((word >> (8*j)) & 255)) % modulus
    return r


def length_metadata():
    # Only lengths and labels are required in this classifier mode.
    # Encode the binary length without leading zeros.
    count = 0
    base = (128, 129, (1<<67)+7, (1<<513)+11, (1<<2107)+37)
    for lengths in combinations(base,3):
        words = [format(n,'b') for n in lengths]
        m = smallest_modulus(words)
        for labels in product((False,True), repeat=3):
            table(words,labels,m)
            count += 1
    return count


def nontrivial_moduli():
    rows = 0
    for h in (2,3,8,20,64,128,300):
        diff = lcm(*range(1,h+1))
        width = diff.bit_length()
        words = [format(x,f'0{width}b') for x in (0,diff)]
        m = smallest_modulus(words)
        assert m > h
        rows += table(words,(True,False),m)>0
    return rows


def dimacs_tables():
    records = dimacs_files()
    labels = [truth_table_sat(*parse(raw)) for raw in records]
    assert labels == [True,False,False,True]
    tables = 0
    for count in range(1,5):
        for indices in combinations(range(4),count):
            words = [ ''.join(f'{b:08b}' for b in records[i]) for i in indices]
            m = smallest_modulus(words)
            width = table(words, [labels[i] for i in indices], m)
            # Exact payload visibility at this particular unrounded width.
            assert width >= 2*(len(delta(m)) + 2*count + 1)
            for j,bits in zip(indices,words):
                assert all(packed_stream(records[j],m,lane) == residue(bits,m)
                           for lane in (1,2,3,4,8,16))
            tables += 1
    return tables


def syntax_checks():
    for m in range(1,900):
        r = PayloadReader(tuple(map(int,delta(m))))
        assert r.delta() == m and r.used == len(r.bits)
        assert len(delta(m)) == m.bit_length() + 2*(m.bit_length().bit_length()-1)
    for bad in ('','000','1','1010',delta(4)+'1'+'11'+'00'+'00'):
        word = tagged_literal(tuple(map(int,bad)))
        assert unpack(word,2*(len(bad)+1)) is None
    for word in (0, 3<<2, (3<<4)|1):
        assert unpack(word,12) is None


def synthetic_reply(payload, raw, is_anchor):
    # A finite semantic fixture. The first mode is a timeout. Other modes
    # examine the file prefix or its length. No native time bound is modeled.
    if payload is None:
        return None
    num = sum(int(b)<<j for j,b in enumerate(payload))
    if num % 4 == 0:
        return None
    if num % 4 == 1:
        return bool(raw[0] & (1<<(num%8)))
    if num % 4 == 2:
        return (len(raw)+num) % 3 == 2
    return not is_anchor


def anchor_signatures():
    yes,no,*_ = dimacs_files()
    anchor = b'p cnf 3 8\n'+b''.join(('%d %d %d 0\n'%row).encode()
                for row in product((1,-1),(2,-2),(3,-3)))
    assert not truth_table_sat(*parse(anchor))
    assert truth_table_sat(*parse(yes)) and not truth_table_sat(*parse(no))
    observed = set()
    trials = 0
    for width in (8,10,12):
        reps = {prefix_bits(z,width) for z in range(1<<width)}
        survivors = [b for b in reps if synthetic_reply(b,anchor,True) is False]
        assert survivors and None not in survivors
        for other_width in (width-4,width,width+6):
            def signature(raw):
                return tuple(synthetic_reply(prefix_bits(tagged_literal(b),other_width),raw,False)
                             for b in survivors)
            sy, sn = signature(yes), signature(no)
            assert sy == sn
            observed.update(sy)
            for low in range(1<<width):
                for high in (-1,0,7):
                    param = (high<<width) | low
                    start = prefix_bits(param,width)
                    if synthetic_reply(start,anchor,True) is not False:
                        continue
                    side = prefix_bits(param,other_width)
                    rep = tagged_literal(start)
                    assert side == prefix_bits(rep,other_width)
                    pair = (synthetic_reply(side,yes,False),synthetic_reply(side,no,False))
                    assert pair != (True,False)
                    trials += 1
    assert observed == {None,True,False}
    return trials


def poly_remainder(a, b):
    while a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a


def irreducible(s):
    # Sufficient for the small degrees used here: any proper factorization
    # contains a monic factor of degree at most floor(s/2).
    for f in range((1<<s)|1, 1<<(s+1), 2):
        if all(poly_remainder(f,g) != 0
               for degree in range(1,s//2+1)
               for g in range(1<<degree, 1<<(degree+1))):
            return f
    raise AssertionError("no irreducible polynomial")


def gf_product(a, b, f):
    carry = 1 << (f.bit_length()-1)
    z = 0
    while b:
        if b & 1:
            z ^= a
        b >>= 1
        a <<= 1
        if a & carry:
            a ^= f
    return z


def gf_power(a, u, f):
    z = 1
    while u:
        if u & 1:
            z = gf_product(z,a,f)
        a = gf_product(a,a,f)
        u >>= 1
    return z


def linear_mask(vectors, labels):
    equations = {}
    for row, rhs in zip(vectors,labels):
        while row:
            pivot = row.bit_length()-1
            if pivot not in equations:
                equations[pivot] = row,rhs
                break
            other, bit = equations[pivot]
            row ^= other
            rhs ^= bit
        else:
            # Report failure of full row rank even for a consistent system.
            return None
    mask = 0
    for j,(row,rhs) in sorted(equations.items()):
        if ((row & mask).bit_count() & 1) != rhs:
            mask ^= 1<<j
    assert [((mask & row).bit_count() & 1) for row in vectors] == list(labels)
    return mask


def field_model(words):
    k = len(words)
    p = smallest_modulus(words)
    table = [residue(bits,p) for bits in words]
    q = 1
    while len({x%q for x in table}) < k:
        q += 1
    assert q <= 2 + p.bit_length()*k*(k-1)//2
    exponents = [x%q for x in table]
    s = k+q.bit_length()+1
    f = irreducible(s)
    good = None
    bad = 0
    for alpha in range(1<<s):
        vectors = [gf_power(alpha,u,f) for u in exponents]
        if linear_mask(vectors,[0]*k) is None:
            bad += 1
        elif good is None:
            good = (alpha,vectors)
    assert bad <= ((1<<k)-1)*(q-1) < 1<<s
    alpha, vectors = good
    return p,q,s,f,alpha,vectors


def field_tables():
    actual = dimacs_files()
    actual = [''.join(f'{b:08b}' for b in raw) for raw in actual]
    cases = [('',), ('','0','00','000'), ('01','10','001','101','110'), actual]
    cases.extend(combinations(('','0','1','00','01','10','11'),3))
    checks = 0
    for words in cases:
        p,q,s,f,alpha,vectors = field_model(words)
        for labels in product((0,1),repeat=len(words)):
            mask = linear_mask(vectors,labels)
            payload = delta(p)+delta(q)+delta(s)+''.join(
                format(v,f'0{s}b') for v in (f^(1<<s),alpha,mask))
            assert len(payload) == len(delta(p))+len(delta(q))+len(delta(s))+3*s
            lit = tagged_literal(tuple(map(int,payload)))
            width = 2*(len(payload)+1)
            assert prefix_bits(lit,width-1) is None
            reader = PayloadReader(prefix_bits(lit, width))
            hp,hq,hs = (reader.delta() for _ in range(3))
            hf = (1<<hs) | reader.read(hs)
            ha, hm = reader.read(hs), reader.read(hs)
            assert reader.used == len(payload) and (hp,hq,hs,hf,ha,hm) == (p,q,s,f,alpha,mask)
            for bits,label in zip(words,labels):
                u = residue(bits,hp)%hq
                v = gf_power(ha,u,hf)
                assert ((v & hm).bit_count() & 1) == label
            checks += 1
    return checks


if __name__ == '__main__':
    syntax_checks()
    print(f'{all_tiny()} arbitrary tiny labelings, including empty strings and leading zeros')
    print(f'{dimacs_tables()} actual DIMACS subset labelings, six little-endian load widths')
    print(f'{length_metadata()} length-only classifier tables, including 2108-bit length metadata')
    print(f'{nontrivial_moduli()} colliding-prefix LCM fixtures')
    print(f'{anchor_signatures()} anchored signed-literal extensions across three test widths')
    print(f'{field_tables()} GF power-vector payloads, every field element examined for the rank bound')
