"""Exact small audits for ordered-diagram certificates of row-indexed circuits."""
from itertools import product
from random import Random


def intern(values):
    labels = {}
    indices = []
    for val in values:
        if val not in labels:
            labels[val] = len(labels)
        indices.append(labels[val])
    return list(labels), indices


def diagram(values):
    d = (len(values) - 1).bit_length()
    assert len(values) == 1 << d
    leaves, ids = intern(values)
    levels = []
    for i in reversed(range(d)):
        width = 1 << i
        rows, ids = intern(zip(ids[:width], ids[width:]))
        levels.append(rows)
    return list(reversed(levels)), leaves


def transition_diagram(depth, initial, step, output):
    states = [initial]
    levels = []
    for i in range(depth):
        states, ids = intern(step(i, s, b) for s in states for b in range(2))
        levels.append(list(zip(ids[::2], ids[1::2])))
    return levels, [output(s) for s in states]


def evaluate(dg, addr):
    states, labels = dg
    node = 0
    for i, row in enumerate(states):
        node = row[node][addr >> i & 1]
    return labels[node]


def pull(dg, operation, parameter):
    levels, leaves = dg

    def state_step(i, state, bit):
        node, carry = state
        const = parameter >> i & 1
        if operation == 'xor':
            transformed, carry = bit ^ const, 0
        elif operation == 'mask':
            transformed, carry = bit & const, 0
        else:
            assert operation == 'add'
            z = bit + const + carry
            transformed, carry = z & 1, z >> 1
        return levels[i][node][transformed], carry

    return transition_diagram(len(levels), (0, 0), state_step, lambda s: leaves[s[0]])


def combine(a, b, fun):
    assert len(a[0]) == len(b[0])
    return transition_diagram(len(a[0]), (0,0),
                              lambda i, s, bit: (a[0][i][s[0]][bit], b[0][i][s[1]][bit]),
                              lambda s: fun(a[1][s[0]], b[1][s[1]]))


def equivalent(a, b):
    if len(a[0]) != len(b[0]):
        return False
    _, labels = intern(a[1] + b[1])
    left, right = labels[:len(a[1])], labels[len(a[1]):]
    for x, y in zip(reversed(a[0]), reversed(b[0])):
        pairs = [(left[u], left[v]) for u, v in x] + [(right[u], right[v]) for u, v in y]
        _, labels = intern(pairs)
        left, right = labels[:len(x)], labels[len(x):]
    return left[0] == right[0]


def mul(x, y):
    z = 0
    while y:
        if y & 1:
            z ^= x
        x <<= 1
        if x & 16:
            x ^= 19
        y >>= 1
    return z


def field_value(dg, points):
    values = dg[1]
    for layer, p in zip(reversed(dg[0]), reversed(points)):
        values = [mul(1 ^ p, values[a]) ^ mul(p, values[b]) for a,b in layer]
    return values[0]


def restrict(table, bit, domain):
    return sum(((table >> (2*x+bit)) & 1) << x for x in range(domain//2))


def linear_combination(coordinates, vectors):
    val = 0
    for k, basis in enumerate(vectors):
        if coordinates >> k & 1:
            val ^= basis
    return val


def basis_coordinates(vectors):
    pivots, basis = {}, []
    def reduce(v):
        coords = 0
        while v and v.bit_length() in pivots:
            w, c = pivots[v.bit_length()]
            v ^= w
            coords ^= c
        return v, coords
    for v in vectors:
        reduced, used = reduce(v)
        if reduced:
            pivots[reduced.bit_length()] = reduced, used ^ (1 << len(basis))
            basis.append(v)
    def coordinates(v):
        rem, val = reduce(v)
        assert rem == 0
        return val
    return basis, coordinates


def xor_witness(diagrams):
    depth = len(diagrams[0][0])
    suffix = [dg[1] for dg in diagrams]
    all_suffixes = [suffix]
    for i in reversed(range(depth)):
        domain = 1 << (depth-i)
        new = []
        for dg, children in zip(diagrams, suffix):
            row = []
            for a, b in dg[0][i]:
                val = sum(((children[b if x & 1 else a] >> (x//2)) & 1) << x
                          for x in range(domain))
                row.append(val)
            new.append(row)
        suffix = new
        all_suffixes.append(suffix)

    data = list(reversed(all_suffixes))
    bases = [basis_coordinates([v for layer in level for v in layer]) for level in data]
    coordinates = [[[bases[i][1](v) for v in layer] for layer in level]
                   for i,level in enumerate(data)]
    matrices = []
    for i in range(depth):
        matrices.append([[bases[i+1][1](restrict(v, bit, 1 << (depth-i))) for v in bases[i][0]]
                         for bit in range(2)])
    return coordinates, matrices, bases[-1][0]


def verify_xor(diagrams, witness):
    coords, matrices, readout = witness
    for j, dg in enumerate(diagrams):
        for i, level in enumerate(dg[0]):
            for node, pair in enumerate(level):
                for bit in range(2):
                    if linear_combination(coords[i][j][node], matrices[i][bit]) != coords[i+1][j][pair[bit]]:
                        return False
        if any(linear_combination(c, readout) != val for c, val in zip(coords[-1][j], dg[1])):
            return False
    return coords[0][0][0] ^ coords[0][1][0] == coords[0][2][0]


def audit():
    rng = Random(299)
    counts = dict(transductions=0, products=0, field_checksums=0, affine_tests=0, bitonic_layers=0)
    for depth in range(1, 7):
        n = 1 << depth
        for _ in range(8):
            values = [rng.randrange(2) for _ in range(n)]
            dg = diagram(values)
            other = [rng.randrange(2) for _ in range(n)]
            rhs = diagram(other)
            for name, c in product(('add','xor','mask'), (0, 1, 2, n-1, rng.randrange(n))):
                index = {'add': lambda x: (x+c)%n, 'xor': lambda x: (x^c)%n, 'mask': lambda x: x&c}[name]
                assert equivalent(pull(dg,name,c), diagram([values[index(x)] for x in range(n)]))
                counts['transductions'] += 1
            for table in range(16):
                f = lambda x,y: table >> (x+2*y) & 1
                merged = combine(dg,rhs,f)
                target = [f(a,b) for a,b in zip(values,other)]
                assert equivalent(merged,diagram(target))
                target[-1] ^= 1
                assert not equivalent(merged,diagram(target))
                counts['products'] += 1
            pts = [rng.randrange(16) for _ in range(depth)]
            expected = 0
            for i, val in enumerate(values):
                coeff = val
                for k, p in enumerate(pts):
                    coeff = mul(coeff, p if i >> k & 1 else 1 ^ p)
                expected ^= coeff
            assert field_value(dg,pts) == expected
            counts['field_checksums'] += 1
            xor = [a^b for a,b in zip(values,other)]
            three = [dg,rhs,diagram(xor)]
            witness = xor_witness(three)
            assert verify_xor(three,witness)
            xor[-1] ^= 1
            altered = [dg,rhs,diagram(xor)]
            assert not verify_xor(altered,xor_witness(altered))
            witness[0][0][0][0] ^= 1
            assert not verify_xor(three,witness)
            counts['affine_tests'] += 3
        for _ in range(7):
            keys = [rng.randrange(2) for _ in range(n)]
            before = list(keys)
            for a in range(1, depth+1):
                for r in reversed(range(a)):
                    dg = diagram(keys)
                    partner = pull(dg,'xor',1<<r)
                    pair = combine(dg,partner,lambda u,v: (u,v))
                    updated = []
                    for x in range(n):
                        u,v = evaluate(pair,x)
                        assert (u,v) == (keys[x],keys[x^(1<<r)])
                        high = ((x >> r) ^ (x >> a)) & 1
                        updated.append(max(u,v) if high else min(u,v))
                    keys = updated
                    counts['bitonic_layers'] += 1
            assert keys == sorted(before)
    for e in range(1, 5):
        w = 1 << e
        vals = [((a&t).bit_count()%2,(b&t).bit_count()%2)
                for t in range(w) for b in range(w) for a in range(w)]
        for i in range(3):
            bits = [x if i==0 else y if i==1 else x^y for x,y in vals]
            assert max(map(len,diagram(bits)[0])) == w
        assert len(diagram(vals)[0][2*e]) == w*w
    return counts


if __name__ == '__main__':
    print(audit())
