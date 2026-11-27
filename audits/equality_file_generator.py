#!/usr/bin/env python3
"""Independent generator, written during review, for the constant-word-alphabet equality files of
notes/communication-bound-for-public-crossed-scans.md ("A constant word alphabet for
deterministic equality").  Builds the actual ASCII bytes, packs them into little-endian
W-byte words, and reports the image size h of the initial memory (file words plus the
zero word), the party boundary, and DIMACS validity.  Optional: CaDiCaL satisfiability
of a few equal / unequal pairs on small instances; CaDiCaL is found via $CADICAL, PATH or a Lean
toolchain.  even_multiplier_scan_independent_check.py imports build() and validate().
Run: python3 equality_file_generator.py   (about a second)"""
import math, random, subprocess, sys, os, tempfile
from pathlib import Path

def width(N, D):
    return 16 * math.ceil(D * math.log2(N + 2) / 16)

def build(N, D, CD, a_bits=None, b_bits=None, w=None, rng=None):
    rng = rng or random.Random(1)
    w = w or width(N, D)
    W = w // 8
    assert W >= 3
    k = N // (CD * int(math.log2(N)) ** 2) if False else int(N // (CD * (math.log2(N)) ** 2))
    K = math.ceil(math.log2(k + 3))
    def name(j):
        bits = format(j, '0%db' % K)
        return '1' + ''.join('0' * (W - 1) + b for b in bits)
    ids = {('x', i): i for i in range(1, k + 1)}
    ids['u'] = k + 1; ids['v'] = k + 2
    if a_bits is None: a_bits = [rng.randrange(2) for _ in range(k)]
    if b_bits is None: b_bits = list(a_bits)
    V = name(2 ** K - 1)
    header = 'p cnf %s %d\n' % (V, 8 * k)
    header += ' ' * ((-len(header)) % W)
    def lit(j, neg):
        return ' ' * (W - 2) + ('-' if neg else ' ') + name(j)
    endc = ' 0\n' + ' ' * (W - 3)
    def half(bits):
        out = []
        for i in range(1, k + 1):
            li_neg = (bits[i - 1] == 0)
            for su in (False, True):
                for sv in (False, True):
                    out.append(lit(ids[('x', i)], li_neg) + lit(ids['u'], su) + lit(ids['v'], sv) + endc)
        return ''.join(out)
    A = half(a_bits); B = half(b_bits)
    body = header + A
    alpha_bytes = len(body)            # Alice owns words [0, alpha_bytes/W - 1]
    assert alpha_bytes % W == 0
    body += B
    total = N // 8
    if len(body) + 1 > total:
        return None
    body += ' ' * (total - len(body) - 1) + '\n'
    data = body.encode('ascii')
    assert len(data) == total
    nwords = (len(data) + W - 1) // W
    words = []
    for t in range(nwords):
        chunk = data[t * W:(t + 1) * W]
        words.append(int.from_bytes(chunk, 'little'))   # zero bytes beyond the end
    return dict(N=N, D=D, w=w, W=W, k=k, K=K, data=data, words=words,
                alpha_word=alpha_bytes // W - 1, a=a_bits, b=b_bits, V=int(V))

def validate(f):
    toks = f['data'].decode('ascii').split()
    assert toks[0] == 'p' and toks[1] == 'cnf'
    V = int(toks[2]); C = int(toks[3])
    lits = list(map(int, toks[4:]))
    clauses, cur = [], []
    for t in lits:
        if t == 0:
            clauses.append(cur); cur = []
        else:
            assert 1 <= abs(t) <= V
            cur.append(t)
    assert cur == [] and len(clauses) == C
    for c in clauses:
        assert len(c) == 3 and len({abs(t) for t in c}) == 3
    return clauses

def image(f):
    return set(f['words']) | {0}

def find_cadical():
    from shutil import which
    found = os.environ.get("CADICAL") or which("cadical")
    if found:
        return found
    candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/cadical"))
    if candidates:
        return str(candidates[0])
    raise SystemExit("cadical not found: set CADICAL, put it on PATH or install a Lean toolchain")

def cadical_sat(clauses):
    m = {}
    for c in clauses:
        for t in c:
            m.setdefault(abs(t), len(m) + 1)
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as fh:
        fh.write('p cnf %d %d\n' % (len(m), len(clauses)))
        for c in clauses:
            fh.write(' '.join(str(m[abs(t)] * (1 if t > 0 else -1)) for t in c) + ' 0\n')
        path = fh.name
    cad = find_cadical()
    r = subprocess.run([cad, '-q', path], capture_output=True, text=True)
    os.unlink(path)
    return r.returncode == 10

if __name__ == '__main__':
    rng = random.Random(7)
    print('N D w W k K | h(image incl. 0) | alpha_word | words | header-words-distinct')
    for D, CD in ((1, 32), (2, 56), (3, 80)):
        for e in (17, 18, 19, 20, 21, 22):
            N = 2 ** e
            f = build(N, D, CD, rng=rng)
            if f is None or f['k'] < 1:
                print(N, D, 'does not fit'); continue
            validate(f)
            hs = set()
            for trial in range(3):
                g = build(N, D, CD, rng=rng, a_bits=[rng.randrange(2) for _ in range(f['k'])],
                          b_bits=[rng.randrange(2) for _ in range(f['k'])])
                hs.add(len(image(g)))
            hw = len(set(f['words'][:f['alpha_word'] + 1 - 4 * f['k'] * (3 * (f['K'] + 1) + 1)]))
            print(N, D, f['w'], f['W'], f['k'], f['K'], '|', len(image(f)), sorted(hs), '|', f['alpha_word'],
                  '|', len(f['words']), '|', hw)
    # union of images over many random pairs at one size: is the palette independent of the strings?
    N = 2 ** 20
    U = set()
    for t in range(20):
        g = build(N, 1, 32, rng=rng, a_bits=None, b_bits=None)
        g = build(N, 1, 32, rng=rng, a_bits=[rng.randrange(2) for _ in range(g['k'])],
                  b_bits=[rng.randrange(2) for _ in range(g['k'])])
        U |= image(g)
    print('union of images over 20 random pairs at N=2^20, D=1:', len(U))
    # satisfiability == equality on small instances (w forced to 24)
    ok = bad = 0
    for t in range(40):
        N = 2 ** 16
        f0 = build(N, 1, 16, w=24, rng=rng)
        k = f0['k']
        a = [rng.randrange(2) for _ in range(k)]
        b = list(a) if t % 2 == 0 else [x ^ (1 if rng.random() < 0.2 else 0) for x in a]
        if t % 2 == 1 and a == b: b[rng.randrange(k)] ^= 1
        f = build(N, 1, 16, w=24, a_bits=a, b_bits=b, rng=rng)
        cl = validate(f)
        s = cadical_sat(cl)
        if s == (a == b): ok += 1
        else: bad += 1
    print('cadical: sat==equal on %d of %d small files (k=%d, w=24), mismatches=%d' % (ok, ok + bad, k, bad))
