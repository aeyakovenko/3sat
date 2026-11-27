#!/usr/bin/env python3
"""Finite correctness check of the Proposition D algorithm (SAT in k + O(log N) bits) of
the-space-route-caps-below-n-to-the-five-fourths.md.

The decider below touches the DIMACS bytes only through read-only indexing, and its
mutable state is one k-bit assignment counter plus a fixed number of integer
positions/counters (each O(log N) bits).  Variables are indexed by FIRST-OCCURRENCE
RANK, computed by digit-by-digit numeral comparison, so the header's n and the size
of variable names never enter the work space.  This script checks correctness against
CaDiCaL on random formulas with sparse, large variable names.  It does not measure
space; the space bound is by inspection of the state listed above.
CaDiCaL is found via $CADICAL, PATH or a Lean toolchain; formulas are piped to it on stdin.
Usage: python3 first_occurrence_rank_enumeration_check.py [TRIALS]   (default 300)
"""
import random, subprocess, sys, os
from pathlib import Path

def find_cadical():
    from shutil import which
    found = os.environ.get("CADICAL") or which("cadical")
    if found:
        return found
    candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/cadical"))
    if candidates:
        return str(candidates[0])
    raise SystemExit("cadical not found: set CADICAL, put it on PATH or install a Lean toolchain")


CADICAL = find_cadical()

def next_token(inp, i):
    """Return (start, end) of the next whitespace-separated token at or after i, or None."""
    n = len(inp)
    while i < n and inp[i] in b" \t\r\n":
        i += 1
    if i >= n:
        return None
    j = i
    while j < n and inp[j] not in b" \t\r\n":
        j += 1
    return (i, j)

def body_start(inp):
    # skip comment lines and the header line "p cnf n m"
    i = 0
    while True:
        t = next_token(inp, i)
        if t is None:
            return len(inp)
        if inp[t[0]:t[0]+1] in (b"c", b"p"):
            j = t[0]
            while j < len(inp) and inp[j:j+1] != b"\n":
                j += 1
            i = j + 1
            continue
        return t[0]

def same_var(inp, p, q):
    """Compare |numeral| at token starts p and q digit by digit (O(log N) state)."""
    if inp[p:p+1] == b"-": p += 1
    if inp[q:q+1] == b"-": q += 1
    while p < len(inp) and inp[p:p+1] == b"0" and p + 1 < len(inp) and inp[p+1:p+2].isdigit(): p += 1
    while q < len(inp) and inp[q:q+1] == b"0" and q + 1 < len(inp) and inp[q+1:q+2].isdigit(): q += 1
    while True:
        a = inp[p:p+1] if p < len(inp) and inp[p:p+1].isdigit() else b""
        b = inp[q:q+1] if q < len(inp) and inp[q:q+1].isdigit() else b""
        if a != b:
            return False
        if a == b"":
            return True
        p += 1; q += 1

def is_zero(inp, p):
    return inp[p:p+1] == b"0" and not inp[p+1:p+2].isdigit()

def literal_tokens(inp, s):
    """Generator over literal token starts (skips clause terminators). State: one position."""
    i = s
    while True:
        t = next_token(inp, i)
        if t is None:
            return
        if not is_zero(inp, t[0]):
            yield t[0]
        i = t[1]

def is_first(inp, s, p):
    for q in literal_tokens(inp, s):
        if q >= p:
            return True
        if same_var(inp, q, p):
            return False
    return True

def rank(inp, s, p):
    f = None
    for q in literal_tokens(inp, s):
        if same_var(inp, q, p):
            f = q; break
    r = 0
    for q in literal_tokens(inp, s):
        if q > f:
            break
        if is_first(inp, s, q):
            r += 1
    return r - 1

def decide(inp):
    s = body_start(inp)
    k = sum(1 for p in literal_tokens(inp, s) if is_first(inp, s, p))
    for A in range(1 << k):                      # the k-bit counter
        ok = True
        i = s
        clause_sat = False
        while True:                              # scan clauses with one position
            t = next_token(inp, i)
            if t is None:
                break
            p = t[0]
            if is_zero(inp, p):
                if not clause_sat:
                    ok = False; break
                clause_sat = False
            elif not clause_sat:
                bit = (A >> rank(inp, s, p)) & 1
                neg = inp[p:p+1] == b"-"
                if bit ^ neg:
                    clause_sat = True
            i = t[1]
        if ok:
            return True
    return False

def random_formula(rng):
    k = rng.randint(1, 9)
    names = rng.sample(range(1, 10**6), k)
    m = rng.randint(1, 4 * k + 2)
    clauses = []
    for _ in range(m):
        w = rng.randint(1, 3)
        clauses.append([rng.choice(names) * rng.choice((1, -1)) for _ in range(w)])
    nmax = max(abs(l) for c in clauses for l in c)
    txt = "c random sparse-name test\np cnf %d %d\n" % (nmax, m)
    txt += "".join(" ".join(str(l) for l in c) + " 0\n" for c in clauses)
    return txt.encode()

def cadical(inp):
    r = subprocess.run([CADICAL, "-q"], input=inp, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return {10: True, 20: False}[r.returncode]

if __name__ == "__main__":
    rng = random.Random(20261127)
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    agree = sat = 0
    for _ in range(trials):
        inp = random_formula(rng)
        a, b = decide(inp), cadical(inp)
        if a != b:
            print("MISMATCH", inp.decode()); sys.exit(1)
        agree += 1; sat += a
    print("trials=%d agree=%d sat=%d unsat=%d" % (trials, agree, sat, trials - sat))
