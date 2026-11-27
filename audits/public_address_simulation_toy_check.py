#!/usr/bin/env python3
"""Toy check for notes/three-public-address-normal-forms-of-a-ram-run.md:
two address-public simulations on a logged toy word RAM.

Check 1 (the definition matters).  Source P_chase, the pointer-chasing source:
    copy x_0..x_{m-1} into cells 0..m-1; then for j = 1..T': v_j = M[a_{j-1}], a_j = v_j mod m.
  Simulator Q_weak is address-public with public windows and holds P's registers (v_j, a_j)
  at the end of every load window.  Window 0 precomputes v_1..v_T' obliviously (pointer
  doubling; every table lookup is a batched gather done with two bitonic sorts and a scan).
  Each load window then makes exactly ONE probe.  Asserted over every input at the sizes run:
  identical operation trace (memory kind+address, and ALU op names), correct registers.

Check 2 (the attaining construction under freshness).  Source P_fresh:
    copy x_0..x_{m-1}; then for j = 1..T': read input word q_j, reply = M[q_j mod m].
  Simulator Q_scan reads q_j first in window j (input-faithful) and scans the m cells.
  Asserted: identical trace, correct replies, q_j's input cell first loaded in window j,
  exactly 1 + m loads per window.

Records of O(1) words are stored as Python tuples in one cell (a toy simplification: on the
journal's RAM they pack into O(1) words of w = Theta(log n) bits).  Every data-dependent choice
goes through a logged ALU op whose logged name does not depend on the data, so identical traces
certify that the memory schedule and the control flow are input-independent.

Usage: python3 public_address_simulation_toy_check.py          (default sizes, about 20 s)
       python3 public_address_simulation_toy_check.py quick    (smaller sizes, about 4 s)
"""
import itertools
import random
import sys

sys.dont_write_bytecode = True


class Machine:
    """Toy word RAM: memory dict, input list, operation log."""

    def __init__(self, inp):
        self.inp = list(inp)
        self.mem = {}
        self.log = []

    # memory operations (addresses must be public: the check compares logs across inputs)
    def load_input(self, i):
        self.log.append(('I', i))
        return self.inp[i]

    def load(self, a):
        self.log.append(('L', a))
        return self.mem.get(a, 0)

    def store(self, a, v):
        self.log.append(('S', a))
        self.mem[a] = v

    # ALU operations: logged by name only
    def alu(self, name, *args):
        self.log.append(('A', name))
        if name == 'and':
            return args[0] & args[1]
        if name == 'eq':
            return 1 if args[0] == args[1] else 0
        if name == 'sel':           # sel(c, x, y) = x if c else y (branch-free on a real RAM)
            return args[1] if args[0] else args[2]
        if name == 'min':
            return min(args[0], args[1])
        if name == 'max':
            return max(args[0], args[1])
        if name == 'mk':            # pack a record
            return tuple(args)
        if name == 'fld':           # extract field args[1] of record args[0]
            return args[0][args[1]]
        raise ValueError(name)


def bitonic_sort(M, base, N):
    """Ascending bitonic sorting network on cells base..base+N-1 (N a power of two)."""
    k = 2
    while k <= N:
        j = k // 2
        while j > 0:
            for i in range(N):
                l = i ^ j
                if l > i:                       # public index condition
                    A = M.load(base + i)
                    B = M.load(base + l)
                    lo = M.alu('min', A, B)
                    hi = M.alu('max', A, B)
                    if (i & k) == 0:            # public index condition
                        M.store(base + i, lo)
                        M.store(base + l, hi)
                    else:
                        M.store(base + i, hi)
                        M.store(base + l, lo)
            j //= 2
        k *= 2


def oblivious_gather(M, tab_base, m, qry_base, q, out_base, scratch, sentinel):
    """out[i] = tab[qry[i]] for i < q, with qry[i] in [0, m).  Address-public."""
    N = 1
    while N < m + q:
        N *= 2
    # records (key, tag, idx, val): table tag 0, query tag 1, padding key = sentinel
    for i in range(m):
        v = M.load(tab_base + i)
        M.store(scratch + i, M.alu('mk', i, 0, 0, v))
    for i in range(q):
        a = M.load(qry_base + i)
        M.store(scratch + m + i, M.alu('mk', a, 1, i, 0))
    for i in range(m + q, N):
        M.store(scratch + i, M.alu('mk', sentinel, 1, i, 0))
    bitonic_sort(M, scratch, N)
    carry = 0
    for i in range(N):
        r = M.load(scratch + i)
        tag = M.alu('fld', r, 1)
        val = M.alu('fld', r, 3)
        is_tab = M.alu('eq', tag, 0)
        carry = M.alu('sel', is_tab, val, carry)
        idx = M.alu('fld', r, 2)
        # second sort key: queries first by idx; table records after them
        M.store(scratch + i, M.alu('mk', M.alu('sel', is_tab, N + i, idx), carry))
    bitonic_sort(M, scratch, N)
    for i in range(q):
        r = M.load(scratch + i)
        M.store(out_base + i, M.alu('fld', r, 1))


def source_chase(x, a0, m, Tp):
    """The pointer-chasing source P_chase: returns P's registers (v_j, a_j) after each load."""
    mem = {i: x[i] for i in range(m)}
    a = a0
    regs = []
    for _ in range(Tp):
        v = mem[a]
        a = v % m
        regs.append((v, a))
    return regs


def q_weak(x, a0, m, Tp):
    """Address-public, public windows; returns (log, registers per load window, probes per window)."""
    inp = list(x) + [a0]
    M = Machine(inp)
    # memory map (all public)
    X, F, A, TMP, V, SCR = 1000, 2000, 6000, 7000, 8000, 20000
    K = max(1, (Tp - 1).bit_length())          # powers 2^0..2^(K-1) cover j <= Tp-1
    sentinel = m + 1
    # ---- window 0: precompute v_1..v_T' ----
    for i in range(m):
        xi = M.load_input(i)
        M.store(X + i, xi)
        M.store(F + i, M.alu('and', xi, m - 1))           # F_0[i] = x_i mod m (m power of 2)
    a0r = M.load_input(m)
    for k in range(1, K):                                 # F_k = F_{k-1} o F_{k-1}
        oblivious_gather(M, F + (k - 1) * m, m, F + (k - 1) * m, m, F + k * m, SCR, sentinel)
    for j in range(Tp):                                   # A[j] = f^j(a0), j = 0..T'-1
        M.store(A + j, a0r)
    for k in range(K):
        js = [j for j in range(Tp) if (j >> k) & 1]       # public set
        if not js:
            continue
        for t, j in enumerate(js):
            M.store(TMP + t, M.load(A + j))
        oblivious_gather(M, F + k * m, m, TMP, len(js), TMP + 4096, SCR, sentinel)
        for t, j in enumerate(js):
            M.store(A + j, M.load(TMP + 4096 + t))
    oblivious_gather(M, X, m, A, Tp, V, SCR, sentinel)    # V[j-1] = x[A[j-1]] = v_j
    # ---- windows 1..m: copy steps, mirroring P's stores ----
    for i in range(m):
        M.store(i, M.load_input(i))
    # ---- load windows: one probe each ----
    regs, probes = [], []
    for j in range(Tp):
        start = len(M.log)
        v = M.load(V + j)
        a = M.alu('and', v, m - 1)
        regs.append((v, a))
        probes.append(sum(1 for e in M.log[start:] if e[0] in ('L', 'I')))
    return M.log, regs, probes


def source_fresh(x, qs, m):
    return [x[q % m] for q in qs]


def q_scan(x, qs, m):
    inp = list(x) + list(qs)
    M = Machine(inp)
    for i in range(m):                                    # copy windows
        M.store(i, M.load_input(i))
    replies, probes, windows = [], [], []
    for j in range(len(qs)):                              # window j
        start = len(M.log)
        q = M.load_input(m + j)
        a = M.alu('and', q, m - 1)
        acc = 0
        for i in range(m):
            c = M.load(i)
            acc = M.alu('sel', M.alu('eq', a, i), c, acc)
        replies.append(acc)
        win = M.log[start:]
        probes.append(sum(1 for e in win if e[0] in ('L', 'I')))
        windows.append((start, len(M.log)))               # log indices [start, end) of window j
    # input-faithfulness: input cell m+j is first loaded inside window j (lambda_j in W_j),
    # and the reply register is set at the end of W_j (tau_j < lambda_{j+1})
    pos = {}
    for t, e in enumerate(M.log):
        if e[0] == 'I' and e[1] not in pos:
            pos[e[1]] = t
    inside = all(windows[j][0] <= pos[m + j] < windows[j][1] for j in range(len(qs)))
    online = all(windows[j][1] <= pos[m + j + 1] for j in range(len(qs) - 1))
    return M.log, replies, probes, (inside, online)


def check_weak(m, b, Tp, inputs, label):
    ref_log = None
    mism = 0
    for (x, a0) in inputs:
        log, regs, probes = q_weak(x, a0, m, Tp)
        if ref_log is None:
            ref_log = log
        elif log != ref_log:
            raise SystemExit('trace differs: m=%d T=%d input=%r' % (m, Tp, (x, a0)))
        if regs != source_chase(x, a0, m, Tp):
            mism += 1
        assert probes == [1] * Tp, probes
    pre = next(i for i, e in enumerate(ref_log) if e == ('I', 0) and i > 0)  # start of copy windows
    print('Q_weak  %-10s m=%-2d b=%d T\'=%-2d inputs=%-6d identical_trace=True register_mismatches=%d '
          'probes_per_load_window=1 trace_len=%d prologue_ops=%d scan_cost_m*T\'=%d'
          % (label, m, b, Tp, len(inputs), mism, len(ref_log), pre, m * Tp))
    return mism


def check_scan(m, b, Tp, inputs, label):
    ref_log = None
    mism = 0
    for (x, qs) in inputs:
        log, replies, probes, (inside, online) = q_scan(x, qs, m)
        if ref_log is None:
            ref_log = log
        elif log != ref_log:
            raise SystemExit('trace differs (scan)')
        if replies != source_fresh(x, qs, m):
            mism += 1
        assert probes == [1 + m] * Tp
        assert inside and online
    print('Q_scan  %-10s m=%-2d b=%d T\'=%-2d inputs=%-6d identical_trace=True reply_mismatches=%d '
          'loads_per_window=%d (=1+m) first_read_of_q_j_inside_window_j=True tau_j<lambda_j+1=True'
          % (label, m, b, Tp, len(inputs), mism, 1 + m))
    return mism


def negative_control(m=4, b=2, Tp=3):
    """A non-public simulator (direct load at the data address) must fail the trace test."""
    logs = set()
    for x in itertools.product(range(2 ** b), repeat=m):
        for a0 in range(m):
            M = Machine(list(x) + [a0])
            for i in range(m):
                M.store(i, M.load_input(i))
            a = M.load_input(m)
            for _ in range(Tp):
                v = M.load(a)              # data-dependent address
                a = M.alu('and', v, m - 1)
            logs.add(tuple(M.log))
    print('negative control (direct pointer chase, m=%d b=%d T\'=%d): distinct traces=%d (must be > 1)'
          % (m, b, Tp, len(logs)))
    return 0 if len(logs) > 1 else 1


def main():
    quick = len(sys.argv) > 1 and sys.argv[1] == 'quick'
    rng = random.Random(20261127)
    bad = negative_control()
    # Check 1: exhaustive small cases
    sizes = [(2, 2, Tp) for Tp in range(1, 7)] + [(4, 2, Tp) for Tp in range(1, 9)]
    if not quick:
        sizes += [(4, 3, 6)]
    for (m, b, Tp) in sizes:
        inputs = [(x, a0) for x in itertools.product(range(2 ** b), repeat=m) for a0 in range(m)]
        bad += check_weak(m, b, Tp, inputs, 'exhaustive')
    # Check 1: sampled larger cases
    for (m, b, Tp, n) in ([(8, 4, 12, 300), (16, 5, 20, 100)] if not quick else [(8, 4, 12, 50)]):
        inputs = [([rng.randrange(2 ** b) for _ in range(m)], rng.randrange(m)) for _ in range(n)]
        bad += check_weak(m, b, Tp, inputs, 'sampled')
    # Check 2: exhaustive small cases
    for (m, b, Tp) in [(2, 2, 3), (4, 2, 3)] + ([(4, 3, 2)] if not quick else []):
        inputs = [(x, qs) for x in itertools.product(range(2 ** b), repeat=m)
                  for qs in itertools.product(range(2 ** b), repeat=Tp)]
        bad += check_scan(m, b, Tp, inputs, 'exhaustive')
    print('TOTAL mismatches:', bad)
    return 0 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
