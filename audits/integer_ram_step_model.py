"""Step-counted RAMs used by the integer-input knapsack audits.

Self-contained (imports nothing from the journal).  Two word models:

  w=None   classical integer RAM: registers and cells hold unbounded integers.
  w=int    native RAM: every word is reduced modulo 2**w, 2**w cells.

A program is ordinary Python control flow that touches data only through the
counted primitives below (one step each): op / cmp (numerical instruction),
br (compare-and-branch), load, store.  Python integers passed as operands are
immediates.  Data words are opaque V objects; control flow can depend on data
only through br outcomes, so a run is a path of a (possibly unfolded) program
with fixed branch targets.  Register moves are aliases and cost nothing.

With trace=True and additive instructions only, every word also carries its
affine form  value = c + a.x  (mod 2**w in the native model) in the original
input words x, and the run records the refined history used in round-14.md:
  * per comparison: wrap numbers of both operands and the sign of the
    difference of the reduced values (integer model: just the sign);
  * per load: which earlier write (initial input cells included) it hits.
It also records the 'forbidden' pairs (address form of a load, address form of
a later non-identical write) whose coincidence would change the alias pattern.
"""
import sys

sys.dont_write_bytecode = True

ALU20 = ('and', 'or', 'xor', 'add', 'sub', 'mul', 'shl', 'shr', 'sar',
         'shlmod', 'shrmod', 'sarmod', 'rol', 'ror',
         'eq', 'lt', 'slt', 'ne', 'ge', 'sge')
COMPARE = ('eq', 'ne', 'lt', 'ge', 'slt', 'sge')
ADDITIVE = frozenset(('add', 'sub') + COMPARE)


def alu(name, a, b, w):
    """The 20 numerical operations at width w (w=None: integers, add/sub/compare only)."""
    if w is None:
        if name == 'add':
            return a + b
        if name == 'sub':
            return a - b
        if name in ('eq', 'ne'):
            return int((a == b) ^ (name == 'ne'))
        if name in ('lt', 'slt', 'ge', 'sge'):
            return int((a < b) ^ (name in ('ge', 'sge')))
        raise ValueError('integer model has no ' + name)
    m = (1 << w) - 1
    top = 1 << (w - 1)
    sa, sb = (a ^ top) - top, (b ^ top) - top
    if name in COMPARE:
        if name in ('eq', 'ne'):
            f = a == b
        elif name in ('slt', 'sge'):
            f = sa < sb
        else:
            f = a < b
        return int(f ^ (name in ('ne', 'ge', 'sge')))
    if name == 'and':
        return a & b
    if name == 'or':
        return a | b
    if name == 'xor':
        return a ^ b
    if name == 'add':
        return (a + b) & m
    if name == 'sub':
        return (a - b) & m
    if name == 'mul':
        return (a * b) & m
    sh = b % w if name.endswith('mod') or name in ('rol', 'ror') else b
    if name in ('shl', 'shlmod'):
        return (a << sh) & m if sh < w else 0
    if name in ('shr', 'shrmod'):
        return a >> sh
    if name in ('sar', 'sarmod'):
        return (sa >> sh) & m
    if name == 'rol':
        return ((a << sh) | (a >> (w - sh))) & m
    if name == 'ror':
        return ((a >> sh) | (a << (w - sh))) & m
    raise ValueError(name)


class V:
    """Opaque data word: concrete value plus (optional) affine form."""
    __slots__ = ('v', 'c', 'a')

    def __init__(self, v, c=None, a=None):
        self.v, self.c, self.a = v, c, a


class RAM:
    def __init__(self, inputs, w=None, allowed=None, trace=False):
        self.w = w
        self.x = tuple(inputs)
        self.n = len(self.x)
        self.allowed = allowed
        self.trace = trace
        self.steps = 0
        self.mem = {}                 # address -> V
        self.last = {}                # address -> index of latest write
        self.writes = []              # (address form or None)
        self.hist = []
        self.forbid = []              # ((cA, aA), (cB, aB)) pairs
        self.alias_hits = 0
        self.wraps = 0
        zero = (0,) * self.n
        self.zero = zero
        for i, xi in enumerate(self.x):
            a = zero[:i] + (1,) + zero[i + 1:]
            self.mem[i] = V(self._red(xi), 0, a) if trace else V(self._red(xi))
            self.last[i] = len(self.writes)
            self.writes.append((i, zero))

    # ---- helpers -------------------------------------------------------
    def _red(self, v):
        return v if self.w is None else v & ((1 << self.w) - 1)

    def _get(self, x):
        if isinstance(x, V):
            return x
        return V(self._red(x), self._red(x), self.zero) if self.trace else V(self._red(x))

    def _need(self, name):
        if self.allowed is not None and name not in self.allowed:
            raise ValueError('instruction not allowed: ' + name)

    def _raw(self, u, shift=0):
        """Unreduced integer value c + a.x of a traced word (native: c shifted for signed)."""
        c = u.c if self.w is None else (u.c + shift) & ((1 << self.w) - 1)
        return c + sum(ai * xi for ai, xi in zip(u.a, self.x))

    def _refine(self, name, u, v):
        if u.a is None or v.a is None:
            self.hist.append(None)
            return
        if self.w is None:
            d = self._raw(u) - self._raw(v)
            self.hist.append((d > 0) - (d < 0))
            return
        shift = (1 << (self.w - 1)) if name in ('slt', 'sge') else 0
        ru, rv = self._raw(u, shift), self._raw(v, shift)
        ku, kv = ru >> self.w, rv >> self.w
        d = (ru - (ku << self.w)) - (rv - (kv << self.w))
        self.wraps += (ku != 0) + (kv != 0)
        self.hist.append((ku, kv, (d > 0) - (d < 0)))

    # ---- counted primitives --------------------------------------------
    def op(self, name, x, y):
        self._need(name)
        self.steps += 1
        u, v = self._get(x), self._get(y)
        r = alu(name, u.v, v.v, self.w)
        if not self.trace:
            return V(r)
        if name in COMPARE:
            self._refine(name, u, v)
            return V(r, r, self.zero)
        if name in ('add', 'sub') and u.a is not None and v.a is not None:
            s = 1 if name == 'add' else -1
            return V(r, self._red(u.c + s * v.c), tuple(p + s * q for p, q in zip(u.a, v.a)))
        return V(r)

    cmp = op

    def br(self, name, x, y):
        self._need(name)
        self.steps += 1
        u, v = self._get(x), self._get(y)
        if self.trace:
            self._refine(name, u, v)
        return bool(alu(name, u.v, v.v, self.w))

    def load(self, addr):
        self._need('load')
        self.steps += 1
        u = self._get(addr)
        hit = self.last.get(u.v, -1)
        if self.trace and u.a is not None:
            A = (u.c, u.a)
            self.hist.append(('L', hit))
            if hit >= 0 and self.writes[hit] != A:
                self.alias_hits += 1
            for s in range(hit + 1, len(self.writes)):
                B = self.writes[s]
                if B is not None and B != A:
                    self.forbid.append((A, B))
        got = self.mem.get(u.v)
        if got is None:
            return V(0, 0, self.zero) if self.trace else V(0)
        return V(got.v, got.c, got.a)

    def store(self, addr, val):
        self._need('store')
        self.steps += 1
        u, v = self._get(addr), self._get(val)
        self.mem[u.v] = v
        self.last[u.v] = len(self.writes)
        self.writes.append((u.c, u.a) if (self.trace and u.a is not None) else None)

    # ---- queries used by the audits --------------------------------------
    def history(self):
        return tuple(self.hist)

    def coincide(self, pair, y):
        """Does the recorded address pair coincide at input point y?"""
        (ca, aa), (cb, ab) = pair
        d = ca - cb + sum((p - q) * yi for p, q, yi in zip(aa, ab, y))
        return d == 0 if self.w is None else d % (1 << self.w) == 0
