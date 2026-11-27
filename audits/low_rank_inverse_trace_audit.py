"""Pointwise trace certificates and actual two-copy SAT surveys over GF(2)."""

from itertools import product
from random import Random

from compiled_horn_receipt_audit import Circuit, exact_sat
from opposite_dense_clock_audit import block_product, xor
from sparse_schur_border_audit import apply, bases, rank, span


def col_apply(cols, value):
    image = 0
    while value:
        bit = value & -value
        image ^= cols[bit.bit_length() - 1]
        value ^= bit
    return image


def make_rows(cols, height):
    return [sum((col >> i & 1) << j for j, col in enumerate(cols)) for i in range(height)]


def mv_map(matrix, n):
    return tuple(apply(n, matrix, x) for x in range(1 << n))


def subspace_image(mapping, space):
    return frozenset(mapping[u] for u in space)


def audit_certificates(n):
    matrices = range(1 << (n*n))
    mappings = [mv_map(x, n) for x in matrices]
    spaces = [(s, tuple(basis), frozenset(span(basis)))
              for s in range(n+1) for basis in bases(s, n)]
    targets = [sum(((matrix >> (n*i+j) & 1) << (n*j+i))
                   for i in range(n) for j in range(n)) for matrix in matrices]
    pairs = 0
    trace_histograms = []
    for k in range(n):
        cohort = [x for x in matrices if rank(n, x) == k]
        inspected = []
        for s, basis, _ in spaces:
            buckets = {}
            for idx,x in enumerate(cohort):
                key = tuple(mappings[x][u] for u in basis)
                buckets[key] = buckets.get(key, 0) | (1 << idx)
            inspected.append((s,list(buckets.values())))
        images = [frozenset(mappings[x]) for x in cohort]
        full = (1 << len(cohort)) - 1
        for r,transposed in enumerate(targets):
            target = sum(((transposed & x).bit_count() % 2) << idx
                         for idx,x in enumerate(cohort))
            first = [None] * len(cohort)
            found = 0
            for cost, buckets in inspected:
                for bucket in buckets:
                    if bucket & target in (0,bucket):
                        new = bucket & ~found
                        found |= new
                        while new:
                            bit = new & -new
                            first[bit.bit_length() - 1] = cost
                            new ^= bit
                if found == full:
                    break
            r_rank = rank(n, r)
            for idx,x in enumerate(cohort):
                ry = subspace_image(mappings[r],images[idx])
                xry = subspace_image(mappings[x],ry)
                expected = min(r_rank, k + len(ry).bit_length() - len(xry).bit_length())
                assert first[idx] == expected, (n,k,r,x,first[idx],expected)
            identity = sum(1 << (n*i+i) for i in range(n))
            if r == identity:
                trace_histograms.append((k, {c:first.count(c) for c in sorted(set(first))}))
            pairs += len(cohort)
    print(f"Dimension {n}: {pairs} matrix/mask pairs with exact pointwise certificates; trace", trace_histograms)


def read_survey(n,k,rng,do_sat):
    # Build maps by columns, including nontriangular small cores as the SAT input.
    while True:
        core = [rng.randrange(1<<n) for _ in range(n)]
        if len(set(span(core))) == 1<<n:
            break
    core_inv = {col_apply(core,u):u for u in range(1<<n)}
    # X=M^{-1}Q. Present Q in the file; X and R X are not given to the query.
    while True:
        u = [rng.randrange(1<<n) for _ in range(k)]
        v = [rng.randrange(1<<k) for _ in range(n)]
        if len(set(span(u))) == 1<<k and len(set(span(v))) == 1<<k:
            break
    x = [col_apply(u,z) for z in v]
    q = [col_apply(core,z) for z in x]
    r = [rng.randrange(1<<n) for _ in range(n)]
    assert all(core_inv[z] == a for z,a in zip(q,x))
    trials = 0
    while True:
        trials += 1
        a = [rng.randrange(1<<n) for _ in range(k)]
        b = [rng.randrange(1<<k) for _ in range(n)]
        t = [col_apply(b,col_apply(x,h)) for h in a]
        if len(set(span(t))) == 1<<k:
            break
    invert_t = {col_apply(t,z):z for z in range(1<<k)}
    target = sum(col_apply(r,z) >> i & 1 for i,z in enumerate(x)) % 2
    s = [invert_t[col_apply(b,col_apply(x,col_apply(r,col_apply(x,z))))] for z in a]
    assert (sum(z>>i&1 for i,z in enumerate(s)) % 2) == target
    # One-copy additive-translate identity, testing genuinely unshifted X.
    for h in ([rng.randrange(1<<k) for _ in range(k)] for _ in range(8)):
        small = [(1<<j)^s[j]^col_apply(h,t[j]) for j in range(k)]
        large = [(1<<j)^col_apply(x,r[j]^col_apply(a,col_apply(h,b[j]))) for j in range(n)]
        assert (len(set(span(small))) == 1<<k) == (len(set(span(large))) == 1<<n)
    if not do_sat:
        return trials,0
    def mat(net, cols, ht, wires):
        return block_product(net,wires,make_rows(cols,ht),1)
    def equal(net, left, right):
        for a0,b0 in zip(left,right):
            net.add(-a0,b0)
            net.add(a0,-b0)
    tested = 0
    for i,bit in product(range(k),range(2)):
        net = Circuit(True)
        y = [net.fresh() for _ in range(n)]
        z = [net.fresh() for _ in range(k)]
        u2 = [net.fresh() for _ in range(n)]
        rhs = col_apply(q,a[i])
        equal(net,mat(net,core,n,y),[net.one if rhs>>j&1 else -net.one for j in range(n)])
        arg = [xor(net,h,j) for h,j in zip(mat(net,a,n,z),mat(net,r,n,y))]
        equal(net,mat(net,core,n,u2),mat(net,q,n,arg))
        for w in mat(net,b,k,u2):
            net.add(-w)
        net.add(z[i] if bit else -z[i])
        raw = net.bytes()
        assert exact_sat(raw) == (bit == ((s[i]>>i)&1))
        tested += 1
    return trials,tested


def multiply(terms, linear):
    product_terms = set()
    for t in terms:
        for d in linear:
            monomial = t | d
            if monomial in product_terms:
                product_terms.remove(monomial)
            else:
                product_terms.add(monomial)
    return product_terms


def audit_private_coefficients():
    tested = files = 0
    for width in range(2,6):
        groups = [list(range(g*width,(g+1)*width)) for g in range(3)]
        offsets = (1<<(3*width))-1
        parameters = 3*width
        background = []
        aux_groups = []
        for group in groups:
            aux = list(range(parameters,parameters+max(0,width-3)))
            parameters += len(aux)
            aux_groups.append(aux)
            background += [[(i,1),(j,1)] for j in group for i in group if i<j]
            if not aux:
                background.append([(i,0) for i in group])
            else:
                background.append([(group[0],0),(group[1],0),(aux[0],0)])
                for h in range(1,len(aux)):
                    background.append([(aux[h-1],1),(group[h+1],0),(aux[h],0)])
                background.append([(aux[-1],1),(group[-2],0),(group[-1],0)])
        # Original choice and OR-chain variables are the fixed identity rows.
        copied = list(range(parameters))
        physical = list(background)
        triples = list(product(*groups))
        starts = []
        for triple in triples:
            row = len(copied)
            starts.append(row)
            copied.extend(triple)
            physical.append([(row+d,1) for d in range(3)])
        def encode(altered=None):
            net = Circuit(True)
            latent = [net.fresh() for _ in range(parameters)]
            wires = []
            for i,p in enumerate(copied):
                wire = -latent[p] if offsets>>p&1 else latent[p]
                if altered and i==altered[0]:
                    wire = xor(net,wire,latent[altered[1]])
                wires.append(wire)
            for clause in physical:
                net.add(*[-wires[i] if neg else wires[i] for i,neg in clause])
            return net.bytes()
        if width<=4:
            assert not exact_sat(encode())
            files += 1
        for h,triple in enumerate(triples):
            unshifted = sum(1<<c for c in triple)
            for group,aux in zip(groups,aux_groups):
                for j,u in enumerate(aux):
                    if not any(unshifted>>g&1 for g in group[:2+j]):
                        unshifted |= 1<<u
            z = unshifted ^ offsets
            active = [c for group in groups for c in group if z>>c&1]
            assert len(active)==3*width-3
            values = [unshifted>>p&1 for p in copied]
            failed = [j for j,cl in enumerate(physical) if not any(values[i]^neg for i,neg in cl)]
            assert failed == [len(background)+h]
            for row,coordinate in product(range(starts[h],starts[h]+3),active):
                corrected = values[row] ^ (z>>coordinate&1)
                assert corrected==0 and values[row]==1
                assert sum(any(i==row for i,_ in cl) for cl in physical)==1
                if width<=4 and h in (0,len(triples)-1) and row==starts[h] and coordinate==active[0]:
                    assert exact_sat(encode((row,coordinate)))
                    files += 1
                tested += 1
    print(f"{tested} individually pivotal coefficient edits, {files} proper-CNF baseline or edited checks")


def audit_clause_histograms(rng):
    count = assignments = core_files = 0
    for k in range(1,9):
        for case in range(32):
            names = 3 + rng.randrange(10)
            rows = [rng.randrange(1<<k) for _ in range(names)]
            offsets = [rng.randrange(2) for _ in range(names)]
            clauses = [[(i,rng.randrange(2)) for i in rng.sample(range(names),3)]
                       for _ in range(rng.randrange(1,25))]
            monomials = {m:i for i,m in enumerate(x for x in range(1<<k) if x.bit_count()<=3)}
            echelon = {}
            kept = []
            for clause in clauses:
                terms = {0}
                for i,negative in clause:
                    literal_false = [1<<b for b in range(k) if rows[i]>>b&1]
                    if not (offsets[i]^negative):
                        literal_false.append(0)
                    terms = multiply(terms,literal_false)
                bits = sum(1<<monomials[t] for t in terms)
                while bits:
                    pivot = bits.bit_length()-1
                    if pivot not in echelon:
                        echelon[pivot] = bits
                        kept.append(clause)
                        break
                    bits ^= echelon[pivot]
            assert len(kept) <= len(monomials)
            accum = [0] * (1<<k)
            for clause in clauses:
                for subset in range(8):
                    freq = polarity = 0
                    for j,(i,negative) in enumerate(clause):
                        if subset>>j&1:
                            freq ^= rows[i]
                            polarity ^= offsets[i] ^ negative
                    accum[freq] += 1 if not polarity else -1
            assert sum(abs(entry) for entry in accum) <= 8*len(clauses)
            for bit in range(k):
                for i in range(1<<k):
                    if not i>>bit&1:
                        j = i^(1<<bit)
                        accum[i],accum[j] = accum[i]+accum[j],accum[i]-accum[j]
                assert max(map(abs,accum)) <= 8*len(clauses)
            for z,value in enumerate(accum):
                actual = [offset ^ ((u&z).bit_count()%2) for offset,u in zip(offsets,rows)]
                violated = sum(not any(actual[i]^negative for i,negative in clause) for clause in clauses)
                assert value == 8*violated
                assert (value == 0) == all(any(actual[i]^neg for i,neg in clause) for clause in kept)
            if k<=4 and case<8:
                net = Circuit(True)
                bits = [net.fresh() for _ in range(k)]
                wires = block_product(net,bits,rows,1)
                for cluster in kept:
                    net.add(*[-wires[i] if offsets[i]^neg else wires[i] for i,neg in cluster])
                assert exact_sat(net.bytes()) == (0 in accum)
                core_files += 1
            count += 1
            assignments += 1<<k
    print(f"{count} proper clause lists; all {assignments} affine-coset violation counts and core verdicts checked, {core_files} physical core files")


if __name__ == "__main__":
    for dimension in (2,3):
        audit_certificates(dimension)
    rng = Random(97831)
    trials = files = successes = 0
    for dimension in range(2,9):
        for k in range(1,min(4,dimension-1)+1):
            for case in range(24):
                count, tested = read_survey(dimension,k,rng,dimension<=4 and case<4)
                trials += count
                files += tested
                successes += 1
    print(f"{successes} exact-rank charts, {trials} trials, {8*successes} independent one-copy translates, {files} proper DIMACS calls")
    audit_clause_histograms(rng)
    audit_private_coefficients()
