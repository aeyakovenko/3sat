"""bit accounting, the short-integer fooling family, programs.

Sections (python3 -B knapsack_fooling_family_audit.py [section ...]; default: all)
  A  bit-length accounting of Meyer auf der Heide 1985, Theorem 5 (k = 1)
  B  the knapsack family K(m, b0, delta): brute-force check of the fooling
     property on tiny parameters; thresholds T0 of Theorems 1 and 2
  C  exact number of components #N(n,1) of the nonnegative knapsack
     arrangement for n <= 5 (weight certificates / summability certificates)
  D  programs: additive ceiling reader, additive family solver, one escaping
     program per non-additive operation, packed and additive dynamic programs;
     exhaustive global correctness on tiny boxes, step counts on large members
  E  the trivial language PAR ("some word is odd")
  W  Theorem 2 at prescribed (W, w): the window-limited thresholds of
     Corollary 2 for PAR and for the knapsack family (floating point)
"""
import random
import sys
from itertools import product
from math import gcd, log2

sys.dont_write_bytecode = True
from integer_ram_step_model import ADDITIVE, RAM

ADD_OK = ADDITIVE | {'load', 'store'}


# ----------------------------------------------------------------- common
def subset_sum(items, target):
    if target < 0:
        return False
    reach = 1
    for a in items:
        if 0 <= a <= target:
            reach |= reach << a
    return bool((reach >> target) & 1)


def A_bound(T, n):
    """Number of forbidden hyperplanes of one history: T(T-1)/2 + nT."""
    return T * (T - 1) // 2 + n * T


def H_int(T, n):
    """Histories of length <= T in the integer model: 2^T (1 + T(T+n)/2)^n (as a fraction-free bound)."""
    return 2 ** T * (2 + T * (T + n)) ** n, 2 ** n          # numerator, denominator


def H_nat(T, n):
    """Refined histories in the native window: 8^T (1 + T(T+n)/8)^n."""
    return 8 ** T * (8 + T * (T + n)) ** n, 8 ** n


def T0(logF, n, D, H):
    """Largest T with H(T,n) < 2^logF and A(T,n) < D: some member needs more than T0 steps.

    Exact integer comparison for logF <= 2^25 and n <= 10^4; beyond that a floating-point
    comparison with a conservative margin (the returned value is then a valid,
    possibly slightly smaller, threshold)."""
    lo, hi = -1, logF + 1
    base = 2 if H is H_int else 8

    def ok(T):
        if A_bound(T, n) >= D:
            return False
        if logF <= 1 << 25 and n <= 10 ** 4:
            num, den = H(T, n)
            return num < den << logF
        return log2(base) * T + n * log2(1 + T * (T + n) / base) + 1e-6 * (n + 1) < logF

    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    return lo


def family_params(m, b0, H=H_int):
    """Smallest delta such that the counting threshold is not cut short by the lattice condition."""
    delta = 0
    while True:
        n = m + b0 + delta + 2
        t_count = T0(m * b0, n, 1 << 4096, H)             # counting threshold alone
        if A_bound(max(t_count, 0), n) < 1 << delta:
            return delta, n, t_count
        delta += 1


def member(a, b0, delta):
    beta = b0 + delta + 1
    return [(2 << delta) * ai for ai in a] + [2 << j for j in range(beta)] + [(1 << (beta + 1)) - 1]


# ----------------------------------------------------------------- A
def section_A():
    print('== A. Meyer auf der Heide 1985, Theorem 5 with k=1: s=3^(3(n+1)^2) (n+1)^(2(n+1)^2), T >= n(n-1)/2 - n')
    print('n, bits per integer b, N=(n+1)b, T, T/(n+1) [=T/(N/b)], T/N, log T/log N, T/(N/ceil(log2 N)), (N/log2 N)^(2/3)/T')
    for n in (4, 16, 64, 256, 1024, 4096, 65536, 2 ** 20):
        if n <= 1024:                                   # exact bit length of the printed bound s
            s = 3 ** (3 * (n + 1) ** 2) * (n + 1) ** (2 * (n + 1) ** 2)
            b, tag = s.bit_length(), 'exact'
        else:                                           # closed form b = (n+1)^2 (3 log2 3 + 2 log2(n+1))
            b, tag = int((n + 1) ** 2 * (3 * log2(3) + 2 * log2(n + 1))) + 1, 'float'
        N = (n + 1) * b
        T = n * (n - 1) // 2 - n
        wlog = N.bit_length()
        print(f'{n:8d} {b:16d} {N:22d} {T:13d} {T / (n + 1):11.2f} {T / N:.3e} {log2(T) / log2(N):.4f} '
              f'{T / (N / wlog):.3e} {(N / log2(N)) ** (2 / 3) / T:.4f} {tag}')


# ----------------------------------------------------------------- B
def section_B():
    print('== B. Family K(m,b0,delta): items 2D*a_i (D=2^delta), ruler 2,4,..,2^beta, target 2^(beta+1)-1, beta=b0+delta+1')
    for m, b0, delta in ((1, 2, 1), (2, 2, 1), (2, 2, 2), (3, 1, 2), (2, 3, 1), (3, 2, 0)):
        D = 1 << delta
        pts = [member(a, b0, delta) for a in product(range(1 << b0), repeat=m)]
        assert all(not subset_sum(p[:-1], p[-1]) for p in pts)
        least, pairs = None, 0
        for i, p in enumerate(pts):
            for q in pts[:i]:
                g = 0
                for u, v in zip(p, q):
                    g = gcd(g, abs(u - v))
                step = [(v - u) // g for u, v in zip(p, q)]
                yes = 0
                for j in range(1, g):
                    y = [u + j * s for u, s in zip(p, step)]
                    yes += subset_sum(y[:-1], y[-1])
                least = yes if least is None else min(least, yes)
                pairs += 1
        print(f'm={m} b0={b0} delta={delta}: n={len(pts[0])} bits={pts[0][-1].bit_length()} members={len(pts)} all NO; '
              f'pairs={pairs}; fewest YES lattice points strictly inside a segment={least} (required >= D={D})')
        assert least >= D
    print('-- thresholds: every program needs more than T0 steps on some member')
    print('   integer model (Theorem 1), then native model (Theorem 2, w_min = T0 + b + 2)')
    print('mu=m=b0, delta, n words, b bits, N=n*b, T0_int, T0_int/N, T0_int/n | delta8, n8, b8, T0_nat, w_min, N8=n8*w_min, T0_nat/n8')
    for mu in (16, 64, 128, 256, 1024, 4096):
        d, n, t = family_params(mu, mu)
        b = mu + d + 2
        d8, n8, t8 = family_params(mu, mu, H_nat)
        b8 = mu + d8 + 2
        wmin = max(t8, 0) + b8 + 2
        print(f'{mu:5d} {d:3d} {n:6d} {b:6d} {n * b:10d} {t:9d} {t / (n * b):7.4f} {t / n:9.2f} | '
              f'{d8:3d} {n8:6d} {b8:6d} {t8:9d} {wmin:9d} {n8 * wmin:13d} {t8 / n8:9.2f}')


# ----------------------------------------------------------------- C
def decreasing(n):
    """All decreasing f:{0,1}^n->{0,1} as bitmasks over points (point index = integer value of alpha)."""
    fs = [0, 1]
    for k in range(n):
        size = 1 << k
        fs = [f0 | (f1 << size) for f0 in fs for f1 in fs if f1 & ~f0 == 0]
    return fs


def section_C():
    print('== C. Components of R_+^(n+1) minus the knapsack arrangement = decreasing threshold functions with f(0)=1')
    print('n, decreasing functions, #N(n,1), log2 #N, Lemma 2 lower bound 2^(n(n-1)/2)/(2^n-1), n^2, non-threshold (2-/3-summable)')
    for n in range(1, 6):
        fs = [f for f in decreasing(n) if f & 1]
        pts = range(1 << n)
        realized = set()
        K = 6
        for a in product(range(K + 1), repeat=n):
            sums = [sum(ai for i, ai in enumerate(a) if (p >> i) & 1) for p in pts]
            for s in set(sums):
                realized.add(sum(1 << p for p in pts if sums[p] <= s))
        code = [sum(((p >> i) & 1) << (2 * i) for i in range(n)) for p in pts]      # base-4 digits
        thr, two, three = 0, 0, 0
        for f in fs:
            if f in realized:
                thr += 1
                continue
            tp = [code[p] for p in pts if (f >> p) & 1]
            fp = [code[p] for p in pts if not (f >> p) & 1]
            if {x + y for x in tp for y in tp} & {x + y for x in fp for y in fp}:
                two += 1
            elif {x + y + z for x in tp for y in tp for z in tp} & {x + y + z for x in fp for y in fp for z in fp}:
                three += 1
            else:
                raise AssertionError('unsettled function; raise K')
        lower = 2 ** (n * (n - 1) // 2) / (2 ** n - 1)
        print(f'{n} {len(fs) + 1:6d} {thr:6d} {log2(thr):6.2f} {lower:9.2f} {n * n:3d} {two}+{three}')


# ----------------------------------------------------------------- D
def read_word(ram, addr, b):
    """Load one word of the box [0,2^b) and learn its value: 1 + b steps."""
    r = ram.load(addr)
    lo, hi = 0, 1 << b
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ram.br('lt', r, mid):
            hi = mid
        else:
            lo = mid
    return lo


def ceiling_reader(x, b, w=None, decide=None):
    """Correct on the whole box for ANY language: learn every word, verdict from finite control.

    `decide` is the finite-control verdict table (default: brute-force subset sum)."""
    ram = RAM(x, w=w, allowed=ADD_OK)
    vals = [read_word(ram, i, b) for i in range(len(x))]
    assert vals == [v for v in x]
    return (decide or (lambda v: subset_sum(v[:-1], v[-1])))(vals), ram.steps


def additive_family_solver(x, m, b0, delta, w=None):
    """Additive, correct on the whole box [0,2^b)^n, b=b0+delta+2; m(b0+2)+2(beta+1) steps on members."""
    ram = RAM(x, w=w, allowed=ADD_OK)
    beta = b0 + delta + 1
    n, b = m + beta + 1, beta + 1
    public = all(ram.br('eq', ram.load(m + j), 2 << j) for j in range(beta)) and \
        ram.br('eq', ram.load(n - 1), (1 << (beta + 1)) - 1)
    if public:
        for i in range(m):
            r = ram.load(i)
            lo, hi = 0, 1 << b0
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if ram.br('lt', r, (2 << delta) * mid):
                    hi = mid
                else:
                    lo = mid
            if not ram.br('eq', r, (2 << delta) * lo):
                break
        else:
            return False, ram.steps                      # all items even, target odd
    vals = [read_word(ram, i, b) for i in range(n)]      # fallback: the ceiling reader
    return subset_sum(vals[:-1], vals[-1]), ram.steps


def is_odd(ram, r, how):
    w = ram.w
    if how == 'and':
        return ram.br('ne', ram.op('and', r, 1), 0)
    if how == 'or':
        return ram.br('eq', ram.op('or', r, 1), r)
    if how == 'xor':
        return ram.br('lt', ram.op('xor', r, 1), r)
    if how in ('shl', 'shlmod'):
        return ram.br('ne', ram.op(how, r, w - 1), 0)
    if how == 'mul':
        return ram.br('ne', ram.op('mul', r, 1 << (w - 1)), 0)
    if how == 'rol':
        return ram.br('slt', ram.op('rol', r, w - 1), 0)
    if how == 'ror':
        return ram.br('slt', ram.op('ror', r, 1), 0)
    if how in ('shr', 'shrmod', 'sar', 'sarmod'):
        h = ram.op(how, r, 1)
        return ram.br('ne', ram.op('add', h, h), r)
    raise ValueError(how)


ESCAPES = ('and', 'or', 'xor', 'shl', 'shlmod', 'mul', 'rol', 'ror', 'shr', 'shrmod', 'sar', 'sarmod')


def dp_additive(ram, items, target, base):
    """Complete pseudo-polynomial solver with add, sub, compare, indirect load/store only."""
    ram.store(base, 1)
    for a in items:
        s = target
        while not ram.br('lt', s, a):
            if ram.br('ne', ram.load(ram.op('add', ram.op('sub', s, a), base)), 0):
                ram.store(ram.op('add', s, base), 1)
            if ram.br('eq', s, 0):
                break
            s = ram.op('sub', s, 1)
    return ram.br('ne', ram.load(ram.op('add', target, base)), 0)


def fast_solver(x, m, beta, w, how):
    """Globally correct program using add/compare/load/store plus the single operation `how`."""
    ram = RAM(x, w=w, allowed=ADD_OK | {how})
    n = len(x)
    regs = [ram.load(i) for i in range(n)]
    odd = [is_odd(ram, r, how) for r in regs]
    if odd[n - 1] and not any(odd[:n - 1]):
        return False, ram.steps                          # even items cannot reach an odd target
    if all(ram.br('eq', regs[m + j], 2 << j) for j in range(beta)) and \
            ram.br('eq', regs[n - 1], (1 << (beta + 1)) - 1):
        for i in range(m):
            if odd[i] and ram.br('lt', regs[i], 1 << beta):
                return True, ram.steps                   # odd item + even remainder from the ruler
    return dp_additive(ram, regs[:-1], regs[-1], n + 1), ram.steps


def dp_packed(x, w):
    """Word-packed subset sum, correct on the whole box when w >= 2^b: 3n+1 steps."""
    ram = RAM(x, w=w, allowed={'load', 'or', 'shl', 'shr', 'and', 'ne'})
    n = len(x)
    R = 1
    for i in range(n - 1):
        R = ram.op('or', R, ram.op('shl', R, ram.load(i)))
    return ram.br('ne', ram.op('and', ram.op('shr', R, ram.load(n - 1)), 1), 0), ram.steps


def section_D():
    print('== D. Programs')
    for m, b0, delta in ((1, 1, 0), (2, 1, 0)):
        beta = b0 + delta + 1
        n, b, w = m + beta + 1, beta + 1, 16
        worst = {}
        count = 0
        for x in product(range(1 << b), repeat=n):
            truth = subset_sum(x[:-1], x[-1])
            count += 1
            runs = {'ceiling': ceiling_reader(x, b), 'ceiling/native': ceiling_reader(x, b, w),
                    'additive-family': additive_family_solver(x, m, b0, delta),
                    'additive-family/native': additive_family_solver(x, m, b0, delta, w),
                    'packed-dp': dp_packed(x, w)}
            for how in ESCAPES:
                runs['fast/' + how] = fast_solver(x, m, beta, w, how)
            ram = RAM(x, w=None, allowed=ADD_OK)
            regs = [ram.load(i) for i in range(n)]
            runs['additive-dp'] = (dp_additive(ram, regs[:-1], regs[-1], n + 1), ram.steps)
            for name, (verdict, steps) in runs.items():
                assert verdict == truth, (name, x)
                worst[name] = max(worst.get(name, 0), steps)
        print(f'exhaustive box: m={m} b0={b0} delta={delta} n={n} b={b} w={w}: {count} inputs, every program correct on all')
        print('   worst-case steps over the box:', ', '.join(f'{k}={v}' for k, v in worst.items()))
        fam = [member(a, b0, delta) for a in product(range(1 << b0), repeat=m)]
        mid = [[(u + v) // 2 for u, v in zip(p, q)] for p in fam for q in fam if p < q]
        on_fam = {how: max(fast_solver(p, m, beta, w, how)[1] for p in fam) for how in ESCAPES}
        on_mid = {how: max(fast_solver(y, m, beta, w, how)[1] for y in mid) for how in ESCAPES}
        print('   fast solvers on the', len(fam), 'members:', on_fam)
        print('   fast solvers on the', len(mid), 'segment midpoints (YES):', on_mid)
        assert worst['ceiling'] == n * (b + 1) and worst['packed-dp'] == 3 * n + 1
    rng = random.Random(14)
    for mu in (64, 256):
        d, n, t0 = family_params(mu, mu)
        d8, n8, t8 = family_params(mu, mu, H_nat)
        delta = max(d, d8)
        beta = mu + delta + 1
        n, b = mu + beta + 1, beta + 1
        t_int = T0(mu * mu, n, 1 << delta, H_int)
        t_nat = T0(mu * mu, n, 1 << delta, H_nat)
        w = 1 << (t_nat + b + 2).bit_length()
        print(f'large instance: m=b0={mu} delta={delta} n={n} b={b}; T0_int={t_int}, T0_nat={t_nat}, native w={w} '
              f'(window needs w >= T0_nat+b+2 = {t_nat + b + 2})')
        steps = {}
        for _ in range(3):
            a = [rng.randrange(1 << mu) for _ in range(mu)]
            a2 = list(a)
            a2[rng.randrange(mu)] ^= 1 << rng.randrange(mu)
            p, q = member(a, mu, delta), member(a2, mu, delta)
            g = 0
            for u, v in zip(p, q):
                g = gcd(g, abs(u - v))
            y = [u + (v - u) // g for u, v in zip(p, q)]            # first lattice point after p: a YES input
            assert any(v % 2 for v in y[:mu])
            for name, run in (('additive-family', lambda z: additive_family_solver(z, mu, mu, delta)),
                              ('additive-family/native', lambda z: additive_family_solver(z, mu, mu, delta, w)),
                              ('ceiling', lambda z: ceiling_reader(z, b, None, lambda v: False))):
                verdict, st = run(p)
                assert verdict is False
                steps.setdefault(name + ' on member', set()).add(st)
            for how in ESCAPES:
                verdict, st = fast_solver(p, mu, beta, w, how)
                assert verdict is False
                steps.setdefault('fast/' + how + ' on member', set()).add(st)
                verdict, st = fast_solver(y, mu, beta, w, how)
                assert verdict is True
                steps.setdefault('fast/' + how + ' on YES point', set()).add(st)
        for k, v in steps.items():
            print(f'   {k}: steps {sorted(v)}')
        print(f'   formulas: additive-family m(b0+2)+2(beta+1)={mu * (mu + 2) + 2 * (beta + 1)}, ceiling n(b+1)={n * (b + 1)}, '
              f'fast 3n={3 * n} or 4n={4 * n}')


# ----------------------------------------------------------------- E
def section_E():
    print('== E. PAR_W = {x : some word is odd}; family (2D*[0,2^b0))^W, D=2^delta, b=b0+delta+1')
    for W, b0, delta in ((1, 3, 1), (2, 2, 1), (2, 2, 2), (3, 1, 1)):
        D = 1 << delta
        pts = [[(2 << delta) * ai for ai in a] for a in product(range(1 << b0), repeat=W)]
        least = None
        for i, p in enumerate(pts):
            for q in pts[:i]:
                g = 0
                for u, v in zip(p, q):
                    g = gcd(g, abs(u - v))
                yes = sum(any((u + j * (v - u) // g) % 2 for u, v in zip(p, q)) for j in range(1, g))
                least = yes if least is None else min(least, yes)
        assert least >= D
        print(f'W={W} b0={b0} delta={delta}: {len(pts)} all-even members; fewest odd-coordinate lattice points inside a segment={least} >= D={D}')
    print('thresholds for PAR in the integer model: W words of b bits, best split b=b0+delta+1')
    print('W, b, best b0, delta, T0, T0/W, additive reader W(b0+2), 20-operation scan 2W+2')
    for W in (10 ** 3, 10 ** 6):
        for b in (32, 64, 128, 256, 1024):
            best = None
            for delta in range(1, b - 1):
                b0 = b - delta - 1
                t = T0(W * b0, W, 1 << delta, H_int)
                if best is None or t > best[0]:
                    best = (t, b0, delta)
            t, b0, delta = best
            print(f'{W:8d} {b:5d} {b0:5d} {delta:4d} {t:11d} {t / W:8.2f} {W * (b0 + 2):11d} {2 * W + 2:9d}')
    W, w = 1000, 64
    rng = random.Random(1)
    x = [2 * rng.randrange(1 << 62) for _ in range(W)]
    ram = RAM(x, w=w)
    acc = 0
    for i in range(W):
        acc = ram.op('or', acc, ram.load(i))
    verdict = ram.br('ne', ram.op('and', acc, 1), 0)
    assert verdict is False and ram.steps == 2 * W + 2
    print('executed: OR-fold then one AND and one branch on 1000 even 64-bit words: 2002 steps, verdict NO')


# ----------------------------------------------------------------- W
def nat_threshold(logF, W, delta, cap):
    """Largest T <= cap with 3T + W log2(1+T(T+W)/8) < logF and A(T,W) < 2^delta (float, conservative)."""
    lo, hi = -1, max(cap, 0) + 1
    while hi - lo > 1:
        T = (lo + hi) // 2
        if A_bound(T, W) < 1 << delta and 3 * T + W * log2(1 + T * (T + W) / 8) + 1e-6 * (W + 1) < logF:
            lo = T
        else:
            hi = T
    return lo


def section_W():
    print('== W. Theorem 2 at prescribed (W, w): T* = largest T with T <= w-b-2, the count and the lattice condition')
    print('   (floating point with a conservative margin).  PAR: W words, b=b0+delta+1.  K: W=m+b0+delta+2, b=b0+delta+2')
    print('W, w, w/W | PAR: b0, delta, T*, T*/W, T*/w, formula w-3w/W-4log2(w+W)-5 | K: m, b0, delta, T*, T*/W, T*/w')
    for W in (10 ** 3, 10 ** 4, 10 ** 5):
        L = W.bit_length()
        for w in (W, W * L, 4 * W * L, int(W ** 1.5), W * W // 12, W * W):
            best = (-1, 0, 0)
            for delta in range(2, 140):
                lo, hi = 1, w                     # threshold grows with b0, the window shrinks: bisect the crossing
                while hi - lo > 1:
                    b0 = (lo + hi) // 2
                    cap = w - (b0 + delta + 1) - 2
                    if cap >= 0 and nat_threshold(W * b0, W, delta, w) <= cap:
                        lo = b0
                    else:
                        hi = b0
                for b0 in (lo, hi):
                    cap = w - (b0 + delta + 1) - 2
                    t = nat_threshold(W * b0, W, delta, cap) if cap >= 0 else -1
                    best = max(best, (t, b0, delta))
            t, pb0, pdelta = best
            formula = w - 3 * w / W - 4 * log2(w + W) - 5
            assert t >= formula - 1 or formula < 0
            bestk = (-1, 0, 0, 0)
            for delta in range(2, 140):
                top = (W - delta - 2) // 2
                if top < 2:
                    break
                lo, hi = 1, top
                while hi - lo > 1:
                    b0 = (lo + hi) // 2
                    m = W - b0 - delta - 2
                    cap = w - (b0 + delta + 2) - 2
                    if cap >= 0 and nat_threshold(m * b0, W, delta, w) <= cap:
                        lo = b0
                    else:
                        hi = b0
                for b0 in (lo, hi):
                    m = W - b0 - delta - 2
                    cap = w - (b0 + delta + 2) - 2
                    tk = nat_threshold(m * b0, W, delta, cap) if cap >= 0 else -1
                    bestk = max(bestk, (tk, m, b0, delta))
            tk, m, b0k, dk = bestk
            if 6 * w / W + 6 * log2(w + W) + 4 <= W / 2:          # Corollary 2, part 2
                assert tk >= w - 6 * w / W - 6 * log2(w + W) - 6 - 1
            print(f'{W:7d} {w:12d} {w / W:9.1f} | {pb0:7d} {pdelta:3d} {t:12d} {t / W:10.2f} {t / w:6.3f} {formula:14.1f} | '
                  f'{m:7d} {b0k:7d} {dk:3d} {tk:12d} {tk / W:10.2f} {tk / w:6.3f}')


def main():
    todo = sys.argv[1:] or list('ABCDEW')
    for s in todo:
        globals()['section_' + s]()
    print('all assertions passed')


if __name__ == '__main__':
    main()
