#!/usr/bin/env python3
"""Independent check that the register programs P_main / P_first of landmark_chart_check.py
compute the seed note's P / first-family scatter program on ALL maps f (not only
permutations): halt kind vs the journal audit's scatter_solver / surjection_solver
(copied below, logic unchanged, from seed_chart_forced_memory_audit.py)."""
from itertools import product
from collections import Counter
import sys
sys.dont_write_bytecode = True      # importing the checker leaves no __pycache__ in audits/
import landmark_shared_bank_chart_check as L

# ---- copied from the journal audit (unchanged logic) ----
def parse(data):
    header, *body = data.decode("ascii").split("\n")[:-1]
    p, cnf, v, count = header.split()
    assert (p, cnf) == ("p", "cnf") and int(count) == len(body)
    clauses = []
    for line in body:
        *lits, end = map(int, line.split())
        assert end == 0 and len(lits) == 3 == len({abs(x) for x in lits})
        assert all(1 <= abs(x) <= int(v) for x in lits)
        clauses.append(tuple(lits))
    return int(v), clauses

def units_of(data):
    v, clauses = parse(data)
    m = v - 3
    assert len(clauses) == 2 * m + 7
    assert clauses[7:7 + m] == [(-1, 4 + j, 2) for j in range(m)]
    units = []
    for i, (lit, one, two) in enumerate(clauses[7 + m:]):
        assert (one, two) == (1, 2) and (lit > 0) == (i < m // 2)
        units.append((lit > 0, abs(lit) - 4))
    return m, units

def endpoint_tail(f, bank, start):
    m = len(f)
    return all(1 <= bank[y] <= m and f[bank[y] - 1] == y for y in range(start, m))

def scatter_solver_core(f):
    """scatter_solver with the fallback reported instead of run: (verdict or None, used_fallback)."""
    m = len(f)
    bank = [0] * m
    for i in range(0, m):
        last = bank[f[i]] - 1
        if last >= 0 and (last < m // 2) == (i < m // 2):
            return None, True
        bank[f[i]] = i + 1
    return endpoint_tail(f, bank, 0), False

def surjection_solver(f):
    m = len(f)
    bank = [0] * m
    for i in range(m):
        bank[f[i]] = i + 1
    return all(1 <= bank[y] <= m and f[bank[y] - 1] == y for y in range(m))
# ---------------------------------------------------------

def run_machine(f, family):
    prog, lab = L.PROGS[family]
    m = len(f)
    W = L.width(m, prog); mask = (1 << W) - 1
    st = L.TrueState()
    for _ in range(40 * m + 40):
        L.step(prog, st.read, st.write, list(f), m, mask)
    pc = st.read(L.PC)
    return {lab['ACCEPT']: 'accept', lab['REJECT']: 'reject', lab['FALLBACK']: 'fallback'}[pc]

tally = Counter()
for m in (2, 4):
    for f in product(range(m), repeat=m):
        data = L.pinned_file(list(f))
        mm, units = units_of(data)
        assert [name for _, name in units] == list(f)
        verdict, fb = scatter_solver_core(list(f))
        kind = run_machine(f, 'main')
        exp = 'fallback' if fb else ('accept' if verdict else 'reject')
        assert kind == exp, (f, kind, exp)
        tally[('main', m, kind)] += 1
for m in (2, 3, 4):
    for f in product(range(m), repeat=m):
        kind = run_machine(f, 'first')
        exp = 'accept' if surjection_solver(list(f)) else 'reject'
        assert kind == exp, (f, kind, exp)
        tally[('first', m, kind)] += 1
print("register programs agree with the audit's solvers on all maps:", dict(sorted(tally.items())))
