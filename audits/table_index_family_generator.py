#!/usr/bin/env python3
"""Generator for the five-slot proof's table-index family F5: the bounded-alphabet, padded,
translated files of notes/private-probe-contexts-in-read-only-sat.md ("Encoding arbitrary truth
tables by satisfiability", its small-alphabet paragraph, and "Moving the pins"), as used by
read-only step 3 and by WR's raw-word row W5.

Free choices the proof leaves open, fixed here (each is a parameter):
  * names: selectors u_1..u_t get indices 1..t, heap node i (1..2^{t+1}-1) gets index t+i
    (naming='heap'), or a random injective map into [1, 2^K) (naming='random');
    a, b, z get the short names 1, 2, 3;
  * aligned name of index i: '1' then, for each of its K bits (MSB first), W-1 '0's and the bit;
  * a literal starts on a word boundary: W-2 spaces, sign byte (' ' or '-'), then the first digit
    ('1' for aligned names, the digit itself for a short name); a clause ends with the block
    ' 0\\n' + spaces;
  * literal order inside clauses as displayed in the theorem: (u v l) with signs (+,-,+), (+,+,-),
    (-,-,+), (-,+,-) [r for the last two]; pins (+-v, a, b); seven gadget clauses on (a, b, z);
  * section order (order='canonical'): gadget, tree clauses, leaf pins, root pin, [z all-space
    words], selector pins, trailing padding.  order='shuffled' permutes the other clauses and puts
    the (internally permuted, contiguous) selector section at a random clause boundary;
    order='scattered' (NOT the proof's family; robustness only) also scatters the selector pins
    and puts the z all-space words at random clause boundaries;
  * length: B = ceil(C*(D+1)*2^t*t^2/8) + extra bytes, w = 16*ceil(D*log2(8B+2)/16) unless forced;
    trailing padding is spaces (optionally ending in a newline); translation z all-space words
    are taken from the trailing padding, 0 <= z < L.
"""
import math, random, sys
sys.dont_write_bytecode = True


def width(n, D=1):
    return 16 * math.ceil(D * math.log2(n + 2) / 16)


def tree_clauses(t, lit_order='theorem'):
    """Clauses over abstract variables ('s', j), ('n', i), ('a',), ('b',), ('z',); literal = (var, neg)."""
    a, b, zz = ('a',), ('b',), ('z',)
    gadget = []
    for al in range(1, 8):
        bits = [(al >> 2) & 1, (al >> 1) & 1, al & 1]
        # forbid assignment bits: literal x if bit 0 else -x
        gadget.append([(a, bits[0] == 1), (b, bits[1] == 1), (zz, bits[2] == 1)])
    tree = []
    for i in range(1, 1 << t):
        j = i.bit_length()            # level of node i; selector u_j
        u, v, l, r = ('s', j), ('n', i), ('n', 2 * i), ('n', 2 * i + 1)
        if lit_order == 'theorem':   # (u_j, v, child) as displayed in the theorem
            tree += [[(u, False), (v, True), (l, False)], [(u, False), (v, False), (l, True)],
                     [(u, True), (v, True), (r, False)], [(u, True), (v, False), (r, True)]]
        else:                        # 'audit': (u_j, child, v) as written by audits/table_probe_context_audit.py
            tree += [[(u, False), (l, True), (v, False)], [(u, False), (l, False), (v, True)],
                     [(u, True), (r, True), (v, False)], [(u, True), (r, False), (v, True)]]
    return gadget, tree


def build(t, table, u_bits, z=0, C=96, D=1, w=None, order='canonical', naming='heap', rng=None,
          extra=0, newline=False, lit_order='theorem'):
    """table: list of 2^t bits (T); u_bits: list of t bits, u_bits[0] = u_1 = MSB.
    Returns dict(data, w, W, sel_words, L, ...); None if the formula does not fit."""
    rng = rng or random.Random(0)
    gadget, tree = tree_clauses(t, lit_order)
    a, b = ('a',), ('b',)
    leafpins = [[(('n', (1 << t) + k), table[k] == 0), (a, False), (b, False)] for k in range(1 << t)]
    rootpin = [[(('n', 1), False), (a, False), (b, False)]]
    selpins = [[(('s', j), u_bits[j - 1] == 0), (a, False), (b, False)] for j in range(1, t + 1)]
    nvars = t + (1 << (t + 1)) - 1
    K = nvars.bit_length()
    if naming == 'heap':
        index = {('s', j): j for j in range(1, t + 1)}
        index.update({('n', i): t + i for i in range(1, 1 << (t + 1))})
    else:
        K += 1
        pool = rng.sample(range(1, 1 << K), nvars)
        keys = [('s', j) for j in range(1, t + 1)] + [('n', i) for i in range(1, 1 << (t + 1))]
        index = dict(zip(keys, pool))
    short = {('a',): '1', ('b',): '2', ('z',): '3'}
    B0 = math.ceil(C * (D + 1) * (1 << t) * t * t / 8) + extra
    if w is None:
        w = width(8 * B0, D)
    W = w // 8
    assert W >= 4

    def name(var):
        if var in short:
            return short[var]
        return '1' + ''.join('0' * (W - 1) + bit for bit in format(index[var], '0%db' % K))

    def lit(var, neg):
        s = ' ' * (W - 2) + ('-' if neg else ' ') + name(var)
        return s

    endc = ' 0\n' + ' ' * (W - 3)

    def clause(c):
        return ''.join(lit(v, n) for v, n in c) + endc

    others = gadget + tree + leafpins + rootpin
    sel = list(selpins)
    if order == 'canonical':
        pieces = [clause(c) for c in others] + ['@Z'] + [clause(c) for c in sel]
    elif order == 'shuffled':
        rng.shuffle(others); rng.shuffle(sel)
        pos = rng.randrange(len(others) + 1)
        pieces = [clause(c) for c in others[:pos]] + ['@Z'] + [clause(c) for c in sel] + \
                 [clause(c) for c in others[pos:]]
    elif order == 'scattered':
        allc = others + sel
        rng.shuffle(allc)
        pieces = [clause(c) for c in allc]
    else:
        raise ValueError(order)
    ncl = len(others) + len(sel)
    header = 'p cnf %s %d\n' % ('1' + ''.join('0' * (W - 1) + '1' for _ in range(K)), ncl)
    header += ' ' * ((-len(header)) % W)
    body_len = len(header) + sum(len(p) for p in pieces if p != '@Z')
    L = (B0 - body_len - (1 if newline else 0)) // W
    if L < 1 or z >= L:
        return None
    if order == 'scattered':
        # z all-space words at random clause boundaries
        cuts = [rng.randrange(len(pieces) + 1) for _ in range(z)]
        out = []
        for k, p in enumerate(pieces + ['']):
            out.append(' ' * W * cuts.count(k))
            out.append(p)
        body = header + ''.join(out)
    else:
        body = header + ''.join((' ' * (W * z)) if p == '@Z' else p for p in pieces)
    pad = B0 - len(body)
    body += (' ' * (pad - 1) + '\n') if newline else ' ' * pad
    data = body.encode('ascii')
    assert len(data) == B0
    # selector sign words (their sign byte is the only private byte of the file)
    sel_words = []
    for j in range(1, t + 1):
        k = data.find((' ' * (W - 2) + ('-' if u_bits[j - 1] == 0 else ' ') + name(('s', j))).encode()
                      + (' ' * (W - 2) + ' 1' + ' ' * (W - 2) + ' 2' + endc).encode())
        assert k >= 0 and k % W == 0
        sel_words.append(k // W)
    return dict(data=data, w=w, W=W, K=K, L=L, sel_words=sel_words, index=index, t=t,
                n=8 * B0, header_words=len(header) // W, nclauses=ncl)


def words(data, W):
    return [int.from_bytes(data[k:k + W], 'little') for k in range(0, len(data), W)]


def palette(f):
    return set(words(f['data'], f['W'])) | {0}


def truth(table, u_bits):
    return table[int(''.join(map(str, u_bits)), 2)] == 1


def check_properties(t, trials=6, C=96, seed=1, cadical=True):
    """The proof's properties, asserted on generated files.  Returns a summary dict."""
    import equality_file_generator as G
    rng = random.Random(seed)
    T0 = [rng.randrange(2) for _ in range(1 << t)]
    u0 = [rng.randrange(2) for _ in range(t)]
    base = build(t, T0, u0, z=0, C=C)
    assert base is not None, 'does not fit'
    W, w, L = base['W'], base['w'], base['L']
    assert w == width(base['n']), 'width rule'
    # header words: none looks like a literal lead block (low 16 bits two spaces) or a terminator
    hw = words(base['data'][:base['header_words'] * W], W)
    assert all((x & 0xFFFF) not in (0x2020, 0x3020) and x for x in hw)
    pal_sizes, ncad, nsat = set(), 0, 0
    U = set()
    for zz in (0, 1, L // 2, L - 1):
        sel0 = None
        for k in range(trials):
            T = [rng.randrange(2) for _ in range(1 << t)]
            u1 = [rng.randrange(2) for _ in range(t)]
            u2 = [rng.randrange(2) for _ in range(t)]
            f1 = build(t, T, u1, z=zz, C=C); f2 = build(t, T, u2, z=zz, C=C)
            assert len(f1['data']) == len(base['data']) == len(f2['data'])
            assert f1['sel_words'] == f2['sel_words']
            if sel0 is None:
                sel0 = f1['sel_words']
            assert f1['sel_words'] == sel0
            assert sel0 == [s + zz for s in base['sel_words']], 'translation moves the section by z words'
            assert len(set(sel0)) == t
            w1, w2 = words(f1['data'], W), words(f2['data'], W)
            diff = {i for i, (x, y) in enumerate(zip(w1, w2)) if x != y}
            assert diff == {sel0[j] for j in range(t) if u1[j] != u2[j]}, 'only the selector words depend on u'
            # translation moves whitespace only
            assert f1['data'].split() == build(t, T, u1, z=0, C=C)['data'].split()
            pal_sizes.add(len(palette(f1)))
            U |= palette(f1)
            if cadical and k < 2:
                cl = G.validate(dict(data=f1['data']))
                s = G.cadical_sat(cl)
                assert s == truth(T, u1), 'CaDiCaL truth equals T(u)'
                ncad += 1; nsat += s
    return dict(t=t, w=w, W=W, n=base['n'], bytes=len(base['data']), K=base['K'], L=L,
                words=len(base['data']) // W, nclauses=base['nclauses'],
                palette_sizes=sorted(pal_sizes), union_palette=len(U), cadical_runs=ncad, sat=nsat)


if __name__ == '__main__':
    ts = [int(a) for a in sys.argv[1:]] or [5, 6, 7]
    for t in ts:
        print(check_properties(t))
