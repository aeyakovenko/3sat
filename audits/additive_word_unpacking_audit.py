"""add/sub/compare/load/store simulate all 20 word operations.

Proposition U of round-14.md (hypotheses 2h <= w <= 4^h).  A machine with only add, sub, the comparisons,
and direct/indirect load and store (word width w' = w + O(1), or integers)
  * unpacks a w-bit input word into K = ceil(w/h) chunks of h bits (the top
    chunk may be narrower) in w + K + 1 steps (one load, w adaptive literal
    comparisons, K literal stores), or in at most 8w + 3K steps by one fixed
    loop whose thresholds come from a table of powers of two;
  * after filling tables with O(2^(2h) + (h + K) 2^h) words, performs each of
    the 20 native operations on chunked words, and a chunk-addressed memory
    access, in a number of steps depending on K only.
With h = floor(log2(N)/4) the tables have O(sqrt N) words and K = O(w/log N).

The chunk routines below touch data only through the counted primitives of
integer_ram_step_model.RAM restricted to ADDITIVE + load/store; they never read a value
field.  Each routine is checked against the native reference `alu` on edge
cases and random operands.   Usage: python3 -B additive_word_unpacking_audit.py [seed]
"""
import random
import sys

sys.dont_write_bytecode = True
from integer_ram_step_model import ADDITIVE, ALU20, RAM, alu

ADD_OK = ADDITIVE | {'load', 'store'}


class Sim:
    def __init__(self, w, h, wide, inputs=()):
        assert 2 * h <= w <= 1 << (2 * h)                  # hypotheses of Proposition U
        self.w, self.h, self.K, self.B = w, h, -(-w // h), 1 << h
        self.Bt = 1 << (w - (self.K - 1) * h)             # modulus of the top chunk
        self.ram = RAM(list(inputs), w=wide, allowed=ADD_OK)
        self.next = len(inputs)
        self.table_words = 0
        B, K = self.B, self.K
        r = range(B)
        self.T2 = {}
        for name, f in (('and', lambda a, b: a & b), ('or', lambda a, b: a | b), ('xor', lambda a, b: a ^ b),
                        ('mlo', lambda a, b: (a * b) % B), ('mhi', lambda a, b: (a * b) // B)):
            self.T2[name] = self.table([f(a, b) for a in r for b in r])
        self.Trow = self.table([a * B for a in r])                                # a -> a*2^h
        self.Tsl_lo = self.table([(c << s) % B for s in range(h) for c in r])     # (s,c) -> low part of c<<s
        self.Tsl_hi = self.table([c >> (h - s) if s else 0 for s in range(h) for c in r])
        self.Tsr_lo = self.table([c >> s for s in range(h) for c in r])           # (s,c) -> c>>s
        self.Tsr_hi = self.table([(c << (h - s)) % B if s else 0 for s in range(h) for c in r])
        self.Tq = self.table([s // h for s in range(w)])                          # count -> chunk offset
        self.Trs = self.table([(s % h) * B for s in range(w)])                    # count -> row offset
        self.Tneg = self.table([(w - s) % w for s in range(w)])                   # count -> (w-count) mod w
        self.Tmodw = [self.table([(c << (h * j)) % w for c in r]) for j in range(K)]
        self.Ttop = self.table([c % self.Bt for c in r])                           # reduce a top chunk
        self.Tpow = self.table([1 << j for j in range(w)])                         # thresholds of unpack_loop
        self.scr = self.alloc(3 * K)
        self.block = None
        self.setup_steps = self.ram.steps

    # ---- layout ---------------------------------------------------------
    def alloc(self, size):
        base = self.next
        self.next += size
        return base

    def table(self, values):
        base = self.alloc(len(values))
        for i, v in enumerate(values):
            self.ram.store(base + i, v)               # one literal store per entry
        self.table_words += len(values)
        return base

    # ---- chunk helpers (counted primitives only) ---------------------------
    def chunks_of(self, value, base=None):
        """Opaque chunk registers holding a w-bit value (test harness only: literal stores, loads)."""
        if base is None:
            base = self.alloc(self.K)
        out = []
        for j in range(self.K):
            self.ram.store(base + j, (value >> (self.h * j)) & (self.B - 1))
            out.append(self.ram.load(base + j))
        return out

    def look(self, base, key):
        return self.ram.load(self.ram.op('add', key, base))

    def look2(self, base, a, b):
        return self.look(base, self.ram.op('add', self.look(self.Trow, a), b))

    def bit(self, flag):
        return [1 if flag else 0] + [0] * (self.K - 1)

    def count(self, S, modular):
        """Shift count as one data word: None if a saturating count is >= w (learned by branches)."""
        ram, K, w = self.ram, self.K, self.w
        if modular:
            acc = self.look(self.Tmodw[0], S[0])
            for j in range(1, K):
                acc = ram.op('add', acc, self.look(self.Tmodw[j], S[j]))
            for _ in range(K - 1):
                if ram.br('ge', acc, w):
                    acc = ram.op('sub', acc, w)
            return acc
        for j in range(2, K):
            if ram.br('ne', S[j], 0):
                return None
        s = S[0] if K == 1 else ram.op('add', self.look(self.Trow, S[1]), S[0])
        return None if ram.br('ge', s, w) else s

    def spread(self, X, high):
        """Scratch cells scr..scr+3K-1 = zeros, X, high fill."""
        ram, K = self.ram, self.K
        for j in range(K):
            ram.store(self.scr + j, 0)
            ram.store(self.scr + K + j, X[j])
            ram.store(self.scr + 2 * K + j, high)

    def shifted(self, s, left):
        """After spread(): chunk j of (scratch word) shifted by the data count s."""
        ram, K = self.ram, self.K
        q, row = self.look(self.Tq, s), self.look(self.Trs, s)
        out = []
        for j in range(K):
            if left:
                near = ram.load(ram.op('sub', self.scr + K + j, q))
                far = ram.load(ram.op('sub', self.scr + K + j - 1, q))
                a = self.look(self.Tsl_lo, ram.op('add', row, near))
                c = self.look(self.Tsl_hi, ram.op('add', row, far))
            else:
                near = ram.load(ram.op('add', q, self.scr + K + j))
                far = ram.load(ram.op('add', q, self.scr + K + j + 1))
                a = self.look(self.Tsr_lo, ram.op('add', row, near))
                c = self.look(self.Tsr_hi, ram.op('add', row, far))
            out.append(ram.op('add', a, c))
        return out

    def less(self, X, Y):
        for j in reversed(range(self.K)):
            if self.ram.br('lt', X[j], Y[j]):
                return True
            if self.ram.br('lt', Y[j], X[j]):
                return False
        return False

    # ---- the 20 operations on chunk registers ------------------------------
    def apply(self, name, X, Y):
        ram, K, B = self.ram, self.K, self.B
        if name in ('and', 'or', 'xor'):
            return [self.look2(self.T2[name], X[j], Y[j]) for j in range(K)]
        if name == 'add':
            out, carry = [], False
            for j in range(K):
                mod = B if j < K - 1 else self.Bt
                s = ram.op('add', X[j], Y[j])
                if carry:
                    s = ram.op('add', s, 1)
                carry = ram.br('ge', s, mod)
                out.append(ram.op('sub', s, mod) if carry else s)
            return out
        if name == 'sub':
            out, borrow = [], False
            for j in range(K):
                mod = B if j < K - 1 else self.Bt
                t = ram.op('add', Y[j], 1) if borrow else Y[j]
                borrow = ram.br('lt', X[j], t)
                out.append(ram.op('sub', ram.op('add', X[j], mod), t) if borrow else ram.op('sub', X[j], t))
            return out
        if name == 'mul':
            cols = [0] * K
            for i in range(K):
                for j in range(K - i):
                    cols[i + j] = ram.op('add', cols[i + j], self.look2(self.T2['mlo'], X[i], Y[j]))
                    if i + j + 1 < K:
                        cols[i + j + 1] = ram.op('add', cols[i + j + 1], self.look2(self.T2['mhi'], X[i], Y[j]))
            out, carry = [], 0
            for k in range(K):
                c = ram.op('add', cols[k], carry) if carry else cols[k]
                carry = 0
                while ram.br('ge', c, B):
                    c = ram.op('sub', c, B)
                    carry += 1
                out.append(c)
            out[K - 1] = self.look(self.Ttop, out[K - 1])
            return out
        if name in ('eq', 'ne'):
            same = all(ram.br('eq', X[j], Y[j]) for j in range(K))
            return self.bit(same ^ (name == 'ne'))
        if name in ('lt', 'ge'):
            return self.bit(self.less(X, Y) ^ (name == 'ge'))
        half = self.Bt >> 1
        if name in ('slt', 'sge'):
            nx, ny = ram.br('ge', X[K - 1], half), ram.br('ge', Y[K - 1], half)
            flag = nx if nx != ny else self.less(X, Y)
            return self.bit(flag ^ (name == 'sge'))
        modular = name.endswith('mod') or name in ('rol', 'ror')
        negative = name in ('sar', 'sarmod') and ram.br('ge', X[K - 1], half)
        s = self.count(Y, modular)
        if s is None:
            return [B - 1] * (K - 1) + [self.Bt - 1] if negative else [0] * K
        if name in ('shl', 'shlmod'):
            return self.shift_left(X, s)
        if name in ('shr', 'shrmod', 'sar', 'sarmod'):
            if not negative:
                return self.shift_right(X, s, 0)
            X = X[:K - 1] + [ram.op('add', X[K - 1], B - self.Bt)]      # ones above bit w-1 inside the top chunk
            out = self.shift_right(X, s, B - 1)
            return out[:K - 1] + [self.look(self.Ttop, out[K - 1])]
        if name == 'ror':
            s = self.look(self.Tneg, s)                                  # ror by s = rol by (w-s) mod w
        if ram.br('eq', s, 0):
            return list(X)
        left = self.shift_left(X, s)
        right = self.shift_right(X, self.look(self.Tneg, s), 0)         # disjoint bit ranges: add = or
        return [ram.op('add', left[j], right[j]) for j in range(K)]

    def shift_left(self, X, s):
        self.spread(X, 0)
        out = self.shifted(s, True)
        return out[:self.K - 1] + [self.look(self.Ttop, out[self.K - 1])]

    def shift_right(self, X, s, fill):
        self.spread(X, fill)
        return self.shifted(s, False)

    # ---- unpacking and chunk-addressed memory ------------------------------
    def unpack(self, addr, dest):
        """Raw w-bit word at literal address addr -> K chunk cells at dest: w + K + 1 steps."""
        ram = self.ram
        r = ram.load(addr)
        lo, hi = 0, 1 << self.w
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ram.br('lt', r, mid):
                hi = mid
            else:
                lo = mid
        for j in range(self.K):
            ram.store(dest + j, (lo >> (self.h * j)) & (self.B - 1))

    def unpack_loop(self, addr, dest):
        """The same conversion as one fixed loop: thresholds are loaded from a table of powers of two and all
        loop control is done by counted instructions (at most 8 per bit and 3 per chunk)."""
        ram = self.ram
        x = ram.load(addr)
        ptr, optr = self.Tpow + self.w - 1, dest + self.K - 1
        c, k = 0, self.w - (self.K - 1) * self.h          # top chunk first; register initialisations are moves
        while True:
            p = ram.load(ptr)
            if ram.br('ge', x, p):
                x = ram.op('sub', x, p)
                c = ram.op('add', ram.op('add', c, c), 1)
            else:
                c = ram.op('add', c, c)
            k = ram.op('sub', k, 1)
            if ram.br('eq', k, 0):
                ram.store(optr, c)
                if ram.br('eq', ptr, self.Tpow):
                    return
                optr = ram.op('sub', optr, 1)
                c, k = 0, self.h
            ptr = ram.op('sub', ptr, 1)

    def make_blocks(self):
        K, h, r = self.K, self.h, range(self.B)
        self.Tadr = [self.table([K * (c << (h * j)) for c in r]) for j in range(K)]
        self.block = self.next

    def real(self, A):
        """Real base address of the block of the simulated address held in chunk registers A."""
        acc = self.look(self.Tadr[0], A[0])
        for j in range(1, self.K):
            acc = self.ram.op('add', acc, self.look(self.Tadr[j], A[j]))
        return self.ram.op('add', acc, self.block)

    def mstore(self, A, X):
        base = self.real(A)
        for j in range(self.K):
            self.ram.store(self.ram.op('add', base, j), X[j])

    def mload(self, A):
        base = self.real(A)
        return [self.ram.load(self.ram.op('add', base, j)) for j in range(self.K)]


def value(X, h):
    return sum((x.v if hasattr(x, 'v') else x) << (h * j) for j, x in enumerate(X))


def audit(w, h, rng, trials):
    wide = w + (-(-w // h)).bit_length() + 3
    sim = Sim(w, h, wide)
    m = (1 << w) - 1
    edge = [0, 1, 2, h - 1, h, h + 1, w - 1, w, w + 1, 2 * w, m, m - 1, 1 << (w - 1), (1 << (w - 1)) - 1,
            (1 << (w - 1)) + 1, m >> 1, 0x5555555555555555 & m, 0xAAAAAAAAAAAAAAAA & m]
    worst = {}
    for name in ALU20:
        cases = [(a, b) for a in edge for b in edge]
        cases += [(rng.randrange(m + 1), rng.randrange(m + 1)) for _ in range(trials)]
        cases += [(rng.randrange(m + 1), rng.randrange(3 * w)) for _ in range(trials)]
        for a, b in cases:
            X, Y = sim.chunks_of(a), sim.chunks_of(b)
            before = sim.ram.steps
            Z = sim.apply(name, X, Y)
            worst[name] = max(worst.get(name, 0), sim.ram.steps - before)
            assert value(Z, h) == alu(name, a, b, w), (name, a, b, value(Z, h), alu(name, a, b, w))
            assert all(0 <= (z.v if hasattr(z, 'v') else z) < sim.B for z in Z)
            assert len(Z) == sim.K and (Z[-1].v if hasattr(Z[-1], 'v') else Z[-1]) < sim.Bt
        sim.next = sim.scr + 3 * sim.K            # recycle harness cells
    print(f'w={w} h={h} K={sim.K} (simulating width {wide}): tables {sim.table_words} words, '
          f'{len(ALU20)} operations checked on {len(edge) ** 2 + 2 * trials} operand pairs each')
    print('   worst steps per operation:', ', '.join(f'{k}={v}' for k, v in worst.items()))
    # unpacking
    raw = [rng.randrange(m + 1) for _ in range(40)] + [0, m]
    sim2 = Sim(w, h, wide, raw)
    dest = sim2.alloc(sim2.K * len(raw))
    before = sim2.ram.steps
    for i in range(len(raw)):
        sim2.unpack(i, dest + sim2.K * i)
    per = (sim2.ram.steps - before) / len(raw)
    for i, v in enumerate(raw):
        assert sum(sim2.ram.mem[dest + sim2.K * i + j].v << (h * j) for j in range(sim2.K)) == v
    assert per == w + sim2.K + 1
    dest2 = sim2.alloc(sim2.K * len(raw))
    worst_loop = 0
    for i in range(len(raw)):
        before = sim2.ram.steps
        sim2.unpack_loop(i, dest2 + sim2.K * i)
        worst_loop = max(worst_loop, sim2.ram.steps - before)
    for i, v in enumerate(raw):
        assert sum(sim2.ram.mem[dest2 + sim2.K * i + j].v << (h * j) for j in range(sim2.K)) == v
    assert worst_loop <= 8 * w + 3 * sim2.K
    # chunk-addressed memory against a dictionary
    harness = sim2.alloc(2 * sim2.K)                             # two chunk registers below the blocks
    sim2.make_blocks()
    shadow, worst_mem = {}, 0
    for a0 in [0, 1, m] + [None] * 300:
        if a0 is None:
            a0 = rng.choice(list(shadow)) if rng.random() < 0.5 else rng.randrange(m + 1)
        A = sim2.chunks_of(a0, harness)
        before = sim2.ram.steps
        if a0 not in shadow or rng.random() < 0.5:
            v = rng.randrange(m + 1)
            X = sim2.chunks_of(v, harness + sim2.K)
            before = sim2.ram.steps
            sim2.mstore(A, X)
            shadow[a0] = v
        else:
            assert value(sim2.mload(A), h) == shadow[a0]
        worst_mem = max(worst_mem, sim2.ram.steps - before)
    assert all(value(sim2.mload(sim2.chunks_of(a, harness)), h) == v for a, v in shadow.items())
    print(f'   unpack: {per:.0f} steps per raw word (= w+K+1); as one fixed loop: at most {worst_loop} (<= 8w+3K = '
          f'{8 * w + 3 * sim2.K}); chunk-addressed load/store: at most {worst_mem} steps '
          f'({len(shadow)} random addresses over all 2^{w} agree with a dictionary)')
    return max(worst.values()), worst_mem


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    rng = random.Random(seed)
    print('seed', seed)
    for w, h, trials in ((16, 4, 400), (24, 4, 300), (24, 6, 300), (30, 5, 300), (32, 8, 200),
                         (13, 4, 400), (23, 6, 300), (31, 5, 300), (29, 8, 200), (12, 5, 400)):
        audit(w, h, rng, trials)
    print('all assertions passed')


if __name__ == '__main__':
    main()
