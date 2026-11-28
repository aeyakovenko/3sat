#!/usr/bin/env python3
"""Independent generator, written during review, for the bounded-alphabet, padded, translated table-index files, written from the text
of notes/private-probe-contexts-in-read-only-sat.md (encoding; small-alphabet paragraph; "Moving the pins").
Free choices are parameters.  Variables: selectors s1..st, heap nodes 1..2^{t+1}-1 (node i at level
bit_length(i), children 2i (selected by s_j = 0) and 2i+1 (s_j = 1)), dummies a, b, z.
Clauses as displayed: (u v' l) (u v l') (u' v' r) (u' v r'); pins (+-x a b); gadget forbids all but a=b=z=0."""
import math, random


def make_clauses(t, T, u, lit_order='theorem', gadget_order=('a', 'b', 'z')):
    """Clauses as lists of (var, positive?) where var is a hashable key."""
    cl = []
    # gadget: forbid every assignment except (0,0,0); clause forbidding assignment s is OR of literals
    # that are false under s, i.e. x if s_x = 0 else not x  -> for s != 000 this clause excludes s
    for s in range(1, 8):
        assign = {'a': (s >> 2) & 1, 'b': (s >> 1) & 1, 'z': s & 1}
        cl.append(('gadget', [(g, assign[g] == 0) for g in gadget_order]))
    for i in range(1, 1 << t):
        j = i.bit_length()
        uj, v, l, r = ('s', j), ('n', i), ('n', 2 * i), ('n', 2 * i + 1)
        four = [[(uj, True), (v, False), (l, True)], [(uj, True), (v, True), (l, False)],
                [(uj, False), (v, False), (r, True)], [(uj, False), (v, True), (r, False)]]
        if lit_order == 'audit':
            four = [[c[0], c[2], c[1]] for c in four]
        for c in four:
            cl.append(('tree', c))
    for k in range(1 << t):
        cl.append(('leaf', [(('n', (1 << t) + k), T[k] == 1), ('a', True), ('b', True)]))
    cl.append(('root', [(('n', 1), True), ('a', True), ('b', True)]))
    sel = [('sel', [(('s', j), u[j - 1] == 1), ('a', True), ('b', True)]) for j in range(1, t + 1)]
    return cl, sel


def build(t, T, u, z, W, C=96, D=1, nbits=None, order='canonical', naming='heap', seed=0, lit_order='theorem',
          short=('1', '2', '3'), gadget_order=('a', 'b', 'z'), extra=0, final_newline=False):
    rng = random.Random(seed)
    cl, sel = make_clauses(t, T, u, lit_order, gadget_order)
    keys = [('s', j) for j in range(1, t + 1)] + [('n', i) for i in range(1, 1 << (t + 1))]
    nv = len(keys)
    if naming == 'heap':
        idx = {k: (k[1] if k[0] == 's' else t + k[1]) for k in keys}
        K = max(idx.values()).bit_length()
    else:
        K = nv.bit_length() + 1
        idx = dict(zip(keys, rng.sample(range(1, 1 << K), nv)))
    sh = dict(zip(('a', 'b', 'z'), short))

    def nm(var):
        if var in sh:
            return sh[var]
        bits = bin(idx[var])[2:].zfill(K)
        return '1' + ''.join('0' * (W - 1) + c for c in bits)

    def lit(var, pos):
        return ' ' * (W - 2) + (' ' if pos else '-') + nm(var)

    term = ' 0\n'.ljust(W)

    def ser(c):
        return ''.join(lit(v, p) for v, p in c[1]) + term
    others = list(cl)
    if order == 'shuffled':
        rng.shuffle(others)
        sel = list(sel); rng.shuffle(sel)
        cut = rng.randrange(len(others) + 1)
    else:
        cut = len(others)
    head = 'p cnf %s %d\n' % ('1' + ('0' * (W - 1) + '1') * K, len(cl) + len(sel))
    head = head + ' ' * (-len(head) % W)
    before = ''.join(ser(c) for c in others[:cut])
    selsec = ''.join(ser(c) for c in sel)
    after = ''.join(ser(c) for c in others[cut:])
    if nbits is None:
        nbytes = -(-C * (D + 1) * (2 ** t) * t * t // 8) + extra
    else:
        nbytes = nbits // 8
    used = len(head) + len(before) + len(selsec) + len(after) + (1 if final_newline else 0)
    L = (nbytes - used) // W
    if L < 1 or z >= L:
        return None
    s = head + before + ' ' * (W * z) + selsec + after
    pad = nbytes - len(s)
    s += (' ' * (pad - 1) + '\n') if final_newline else ' ' * pad
    data = s.encode('ascii')
    assert len(data) == nbytes
    w = 8 * W
    return dict(data=data, w=w, W=W, L=L, K=K, n=8 * nbytes)


def width(n, D=1):
    L = (n + 2 - 1).bit_length()
    return 16 * (-(-D * L // 16))


def truth(T, u):
    return T[int(''.join(map(str, u)), 2)] == 1


def dimacs_clauses(data):
    toks = data.decode('ascii').split()
    assert toks[0] == 'p' and toks[1] == 'cnf'
    V, Cn = int(toks[2]), int(toks[3])
    out, cur = [], []
    for x in toks[4:]:
        x = int(x)
        if x == 0:
            out.append(cur); cur = []
        else:
            assert 1 <= abs(x) <= V
            cur.append(x)
    assert not cur and len(out) == Cn
    for c in out:
        assert len(c) == 3 and len({abs(x) for x in c}) == 3
    return out




if __name__ == '__main__':
    # Run from audits/: python3 table_index_family_generator_independent.py
    # Byte-compares this generator's canonical, heap-named files with table_index_family_generator.py's at
    # t = 5, 6, 7 and four translations each (a few seconds). Nothing is written.
    import sys
    sys.dont_write_bytecode = True
    import table_index_family_generator as F
    rng = random.Random(3)
    same = tot = 0
    for t in (5, 6, 7):
        for k in range(4):
            u = [rng.randrange(2) for _ in range(t)]
            T = [rng.randrange(2) for _ in range(1 << t)]
            W = width(8 * -(-96 * 2 * (2 ** t) * t * t // 8)) // 8
            L = build(t, T, u, 0, W)['L']
            z = [0, 1, L // 2, L - 1][k]
            f = build(t, T, u, z, W)
            g = F.build(t, T, u, z=z)
            tot += 1
            same += f['data'] == g['data'] and f['w'] == g['w']
    print('canonical heap-named files byte-identical to table_index_family_generator.py: %d of %d' % (same, tot))
    sys.exit(0 if same == tot else 1)
