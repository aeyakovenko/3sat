"""Check affine restrictions of shared RAM reads and their proper DIMACS encoding."""
from itertools import product


def subspaces(dimension):
    """Enumerate every binary linear space once via increasing reduced pivots."""
    def extend(first, pivots, basis, elements):
        yield basis, elements
        for p in range(first, dimension):
            for low in range(1 << p):
                if low & pivots:
                    continue
                v = (1 << p) | low
                yield from extend(p + 1, pivots | (1 << p), basis + (v,),
                                  elements + tuple(v ^ x for x in elements))
    yield from extend(0, 0, (), (0,))


def affine_on(differences, basis, elements):
    # Elements are indexed by subsets of the basis in binary order.
    for i, v in enumerate(basis):
        for j in range(1 << i):
            if differences[elements[j] ^ v] != differences[elements[j]] ^ differences[v]:
                return False
    return True


def packed_replies(table, addresses, width, bits, count):
    mask = (1 << width) - 1
    word_mask = (1 << bits) - 1
    result = 0
    for i in range(count):
        address = (addresses >> (i * width)) & mask
        result |= ((table >> (bits * address)) & word_mask) << (i * bits)
    return result


def check_size(width, bits, count, bases):
    cells = 1 << width
    table_bits = cells * bits
    address_bits = width * count
    table_flats = [(len(bs), vs) for bs, vs in subspaces(table_bits)]
    address_flats = list(subspaces(address_bits))
    tables = range(1 << table_bits)
    templates = [[packed_replies(t, a, width, bits, count)
                  for a in range(1 << address_bits)] for t in tables]
    for base in bases:
        one_read = [((base >> (a * bits)) ^ base) & ((1 << bits) - 1) for a in range(cells)]
        witnesses = [(len(b), v) for b, v in subspaces(width) if affine_on(one_read, b, v)]
        expected, dim, region = min((count * (width-p) + bits * ((1 << p)-1), p, vs)
                                    for p, vs in witnesses)
        target = table_bits + address_bits - expected
        # Lower bound on achievable dimension from the proposed explicit flat.
        table_shifts = [t for t in tables if
                        len({((t ^ base) >> (a * bits)) & ((1 << bits)-1) for a in region}) == 1]
        assert len(table_shifts) * len(region)**count == 1 << target
        for t in table_shifts:
            delta = (t ^ base) & ((1 << bits)-1)
            for aa in product(region, repeat=count):
                a = sum(val << (i * width) for i, val in enumerate(aa))
                affine_value = sum(((one_read[val] ^ delta ^ (base & ((1 << bits)-1)))
                                     << (i * bits)) for i, val in enumerate(aa))
                assert affine_value == templates[t][a]

        # Independently rule out every larger flat. Enumerate its possible
        # pure-address kernel U. At every projected table some base address
        # must realize the exact derivatives of the true run on U.
        for basis, elements in address_flats:
            need = target + 1 - len(basis)
            if need > table_bits:
                continue
            original = templates[base]
            differences = [v ^ original[0] for v in original]
            if not affine_on(differences, basis, elements):
                continue
            possible = set()
            for table, replies in enumerate(templates):
                if any(all((replies[a ^ u] ^ replies[a]) == differences[u] for u in elements)
                       for a in range(1 << address_bits)):
                    possible.add(table ^ base)
            assert not any(n >= need and all(d in possible for d in ds) for n, ds in table_flats)
    return len(bases)


def proper_file(table, addresses, claims, width, bits):
    cells = 1 << width
    count = len(addresses)
    digits = max(1, (max(width, bits, count.bit_length()) + 2)//3)
    def name(bank, i):
        return int(str(bank) + format(i, f'0{digits}o'))
    clauses = [tuple(-(i+1) if z >> i & 1 else i+1 for i in range(3)) for z in range(1, 8)]
    for a, value in enumerate(table):
        clauses.append((-name(1,a), name(2,value), 1))
    for j, (a,b) in enumerate(zip(addresses,claims)):
        choice = name(3,j)
        clauses.extend(((-choice, name(1,a), 1), (-choice,-name(2,b),1),
                        (-name(4,j), choice, name(4,j+1))))
    clauses.extend(((name(4,0),1,2),(-name(4,count),1,2)))
    assert len(table) == cells and all(len(set(map(abs,c))) == 3 for c in clauses)
    return (f'p cnf {name(4,count)} {len(clauses)}\n' +
            ''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode()


def solve_file(raw):
    header, *rows = raw.splitlines()
    _, _, v, m = header.split()
    assert len(rows) == int(m)
    clauses = []
    for row in rows:
        a,b,c,zero = map(int,row.split())
        assert zero == 0 and 0 < min(map(abs,(a,b,c))) and max(map(abs,(a,b,c))) <= int(v)
        clauses.append((a,b,c))
    def search(rows):
        if not rows:
            return True
        unit = min(rows, key=len)
        if not unit:
            return False
        for lit in (unit[0],) if len(unit) == 1 else (unit[0],-unit[0]):
            if search([tuple(l for l in row if l != -lit) for row in rows if lit not in row]):
                return True
        return False
    return search(clauses)


def check_files():
    width, bits, t = 2, 1, 2
    n = (1 << width)*bits + t*(width+bits)
    def encode(x):
        def take(k):
            nonlocal x
            v=x % (1 << k)
            x >>= k
            return v
        table = [take(bits) for _ in range(1 << width)]
        address = [take(width) for _ in range(t)]
        reply = [take(bits) for _ in range(t)]
        raw = proper_file(table,address,reply,width,bits)
        assert solve_file(raw) == any(table[a] != y for a,y in zip(address,reply))
        return int.from_bytes(raw,'little')
    zero = encode(0)
    changes = [encode(1 << i)^zero for i in range(n)]
    assert all(delta.bit_count() == 1 for delta in changes) and len(set(changes))==n
    for word in range(1 << n):
        assert encode(word) == zero ^ sum(d for i,d in enumerate(changes) if word >> i & 1)
    print(f'{1<<n} proper ASCII files; every editable bit occurs in exactly one physical bit')


def check_distinct_anchors():
    # Independently search whole graph flats, including coherent table-to-address
    # sections, to test strictness when the cells used do not fit in one line.
    s, b, t = 2, 1, 3
    table0 = 8  # the two-input AND is nonaffine on the whole address plane
    address_count = 1 << (s*t)
    replies = [[packed_replies(table, a, s, b, t) for a in range(address_count)]
               for table in range(16)]
    kernels = list(subspaces(s*t))
    table_flats = list(subspaces(4))
    def achievable(anchor, dimension):
        base_reply = replies[table0][anchor]
        for basis, kernel in kernels:
            q = dimension - len(basis)
            if q < 0 or q > 4:
                continue
            diff = [z ^ base_reply for z in (replies[table0][anchor ^ i] for i in range(address_count))]
            if not affine_on(diff,basis,kernel):
                continue
            # One address representative per coset in the pure-address kernel.
            representatives = [a for a in range(address_count) if a == min(a^u for u in kernel)]
            usable = {}
            for td in range(16):
                choices = {}
                row = replies[table0 ^ td]
                for v in representatives:
                    a = anchor ^ v
                    if all((row[a ^ u] ^ row[a]) == diff[u] for u in kernel):
                        choices[v] = row[a] ^ base_reply
                usable[td] = choices
            def lift(directions, existing):
                if not directions:
                    return True
                d,*rest = directions
                for v, out in usable[d].items():
                    new = [(x^d,y^v,z^out) for x,y,z in existing]
                    # RREF quotient representatives have pivot positions zero
                    # and are closed under XOR.
                    if all(usable[x].get(y) == z for x,y,z in new):
                        if lift(rest,existing+new):
                            return True
                return False
            for directions, points in table_flats:
                if len(directions) == q and all(usable[x] for x in points):
                    if lift(directions,[(0,0,0)]):
                        return True
        return False
    # 10 table/address bits in total. Compare two and three distinct addresses.
    for addresses, expected in (((0,0,0),4),((0,0,1),4),((0,1,2),5)):
        anchor=sum(x << (s*i) for i,x in enumerate(addresses))
        assert achievable(anchor,10-expected)
        assert not achievable(anchor,11-expected)
    print('Exact affine costs 4, 4, 5 on runs visiting one, two and three distinct cells')


def check_guarded_sources():
    # Table banks on this scale start with 1..4, source names with 6.
    # Protect their respective gates with opposite directions of selector 9.
    source_rows = [tuple(-(60+i) if z >> i & 1 else 60+i for i in range(3)) for z in range(8)]
    tested = 0
    for count in (0, 7, 8):
        source = source_rows[:count]
        for t0,t1,a0,a1,y0,y1 in product(range(2), repeat=6):
            table, aa, yy = (t0,t1),(a0,a1),(y0,y1)
            raw = proper_file(table,aa,yy,1,1)
            tests = [tuple(map(int,row.split()))[:3] for row in raw.splitlines()[1:]]
            expanded = []
            for guard, rows, fresh in [(9,source,800),(-9,tests,700)]:
                for j,(u,v,w) in enumerate(rows):
                    z=fresh+j
                    expanded.extend(((guard,u,z),(-z,v,w)))
            file = (f'p cnf 899 {len(expanded)}\n' +
                    ''.join(f'{a} {b} {c} 0\n' for a,b,c in expanded)).encode()
            assert solve_file(file) == (count < 8 or any(table[a]!=y for a,y in zip(aa,yy)))
            tested += 1
    print(f'{tested} guarded SAT files from positive and negative source formulas')


def check_rigidity():
    # Three disjoint two-bit target blocks and one unrestricted bit.
    width = 7
    n = 1 << width
    full = (1 << n) - 1
    planes = [sum(1 << x for x in range(n) if (a & x).bit_count() % 2 == 0)
              for a in range(n)]
    targets = [sum(1 << x for x in range(n) if ((x >> k) & 3) == 0)
               for k in (0, 2, 4)]
    covered = targets[0] | targets[1] | targets[2]
    hits = set()
    checked = 0
    for a in range(1,n):
        for b in range(a+1,n):
            if a ^ b < b:
                continue  # a,b are the first two of the three nonzero dual vectors
            for pa,pb in product((planes[a],full ^ planes[a]),(planes[b],full ^ planes[b])):
                flat = pa & pb
                checked += 1
                if flat & ~covered == 0:
                    hits.add(flat)
    assert hits == set(targets)
    print(f'{checked} codimension-two flats tested for equality in the block lemma')


def check_cubing_and_feedback():
    # Irreducible moduli over F_2 of degrees 2,3,4,5.
    for width, modulus in ((2,7),(3,11),(4,19),(5,37)):
        size=1<<width
        def mul(x,y):
            result=0
            while y:
                if y & 1:
                    result ^= x
                x <<= 1
                if x & size:
                    x ^= modulus
                y >>= 1
            return result
        cube = [mul(mul(a,a),a) for a in range(size)]
        for u in range(1,size):
            for v in range(1,u):
                assert all(cube[x]^cube[x^u]^cube[x^v]^cube[x^u^v] for x in range(size))
    # Off-graph claims are allowed. A seed is XORed with the actual preceding reply.
    for table in product(range(4),repeat=4):
        for z0,z1,y0,y1 in product(range(4),repeat=4):
            true0=table[z0]
            actual=(true0,table[z1^true0])
            assert ((y0,y1)==actual) == ((y0,y1)==(table[z0],table[z1^y0]))
    print('Field-cube second differences in degrees 2..5 and 65,536 adaptive graph tests')


if __name__ == '__main__':
    tested = check_size(1,1,3,range(4)) + check_size(1,2,2,range(16))
    tested += check_size(2,1,2,range(16)) + check_size(2,1,3,[0,8,15])
    print(f'{tested} complete upper/lower comparisons by independent subspace exhaustion')
    check_files()
    check_guarded_sources()
    check_distinct_anchors()
    check_cubing_and_feedback()
    check_rigidity()
