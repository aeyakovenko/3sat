"""Finite check of the DIMACS bridge (Lemma B of the journal note
alternation-dichotomy-for-dimacs-sat.md).

(1) Fixed-field rendering of a signed literal by O(1) chunk divisions and
    table lookups (tables of size 10^d), as a word RAM would do it, equals the
    right-justified canonical decimal field built with str().
(2) CaDiCaL parses files whose literals sit in such fixed-width fields (runs
    of spaces) and returns the same verdict as on the single-space rendering.

Usage: python3 -I -B dimacs_fixed_width_literal_check.py [trials, default 200] [cadical_path]
CaDiCaL is taken from the second argument, $CADICAL, the PATH or a Lean toolchain, as in the journal's
other audits; without it the second check is skipped.
Writes temporary CNF files only inside a private temporary directory.
"""
import os
import random
import subprocess
import sys
import tempfile
from pathlib import Path


def find_cadical():
    """CaDiCaL on PATH or in a Lean toolchain (the journal's usual lookup); None if absent."""
    from shutil import which
    found = which("cadical")
    if found:
        return found
    candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/cadical"))
    return str(candidates[0]) if candidates else None


def make_tables(d):
    """T0[v]: d digits zero-padded; TS[v]: d chars, leading spaces (v>0)."""
    t0 = [str(v).rjust(d, "0") for v in range(10 ** d)]
    ts = [str(v).rjust(d, " ") for v in range(10 ** d)]
    return t0, ts


def field_by_chunks(lit, width, d, t0, ts, nchunks):
    """Render a nonzero literal right-justified in `width` chars using only
    divisions by 10^d, table lookups and a count of significant digits."""
    sign = lit < 0
    x = -lit if sign else lit
    base = 10 ** d
    chunks = []
    for _ in range(nchunks):          # O(1) divisions: nchunks is fixed
        x, r = divmod(x, base)
        chunks.append(r)
    assert x == 0, "index exceeds the chunk capacity"
    top = max(i for i, c in enumerate(chunks) if c != 0)
    lead = ts[chunks[top]]
    ndig = d * top + len(lead.lstrip(" "))
    body = lead + "".join(t0[chunks[i]] for i in range(top - 1, -1, -1))
    body = body.lstrip(" ")
    assert len(body) == ndig
    s = ("-" if sign else "") + body
    return " " * (width - len(s)) + s


def check_fields(trials, rng):
    bad = 0
    for v_max in (9, 10, 99, 1000, 65535, 10 ** 6 + 3, 2 ** 31 - 1):
        dmax = len(str(v_max))
        width = dmax + 1
        d = max(1, dmax // 3)
        nchunks = -(-dmax // d)
        t0, ts = make_tables(d)
        for _ in range(trials):
            v = rng.randint(1, v_max)
            lit = v if rng.random() < 0.5 else -v
            want = str(lit).rjust(width, " ")
            got = field_by_chunks(lit, width, d, t0, ts, nchunks)
            bad += (got != want)
        for v in (1, v_max):                     # boundary indices
            for lit in (v, -v):
                bad += (field_by_chunks(lit, width, d, t0, ts, nchunks)
                        != str(lit).rjust(width, " "))
    return bad


def run_cadical(path, cad):
    r = subprocess.run([cad, "-q", path], capture_output=True, text=True,
                       timeout=60)
    for line in r.stdout.splitlines():
        if line.startswith("s "):
            return line.split()[1]
    return "ERR(rc=%d)" % r.returncode


def check_cadical(trials, rng, cad):
    agree = sat = unsat = 0
    with tempfile.TemporaryDirectory() as tmp:
        for t in range(trials):
            nv = rng.randint(3, 40)
            nc = rng.randint(1, int(4.6 * nv))
            clauses = [[rng.choice((1, -1)) * rng.randint(1, nv)
                        for _ in range(3)] for _ in range(nc)]
            width = len(str(nv)) + 2
            d = 1
            t0, ts = make_tables(d)
            nchunks = len(str(nv))
            plain = "p cnf %d %d\n" % (nv, nc) + "".join(
                " ".join(map(str, c)) + " 0\n" for c in clauses)
            padded = "p cnf %d %d\n" % (nv, nc) + "".join(
                " ".join(field_by_chunks(l, width, d, t0, ts, nchunks)
                         for l in c) + " " + "0".rjust(width) + "\n"
                for c in clauses)
            p1 = os.path.join(tmp, "plain.cnf")
            p2 = os.path.join(tmp, "padded.cnf")
            with open(p1, "w") as f:
                f.write(plain)
            with open(p2, "w") as f:
                f.write(padded)
            a, b = run_cadical(p1, cad), run_cadical(p2, cad)
            agree += (a == b and a in ("SATISFIABLE", "UNSATISFIABLE"))
            sat += (a == "SATISFIABLE")
            unsat += (a == "UNSATISFIABLE")
    return agree, sat, unsat


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    cad = sys.argv[2] if len(sys.argv) > 2 else (os.environ.get("CADICAL") or find_cadical())
    rng = random.Random(20261128)
    bad = check_fields(trials, rng)
    print("field rendering: %d value ranges x %d random literals, mismatches=%d"
          % (7, trials, bad))
    if cad and os.path.exists(cad):
        agree, sat, unsat = check_cadical(trials, rng, cad)
        print("cadical: trials=%d agree=%d sat=%d unsat=%d"
              % (trials, agree, sat, unsat))
    else:
        print("cadical not found; skipped")


if __name__ == "__main__":
    main()
