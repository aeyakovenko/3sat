"""Audit the Andreev -> proper ASCII 3-SAT copy projection used in
depth-two-threshold-circuit-bounds-for-3-sat.md.

encode() and bank_name() are copied verbatim from
  andreev_dimacs_projection_audit.py   (encode)
  dense_ascii_chunk_circuit_audit.py   (bank_name, properness checks of sat_from_bytes)
because both of those modules import pycosat at load time.  Here the SAT verdict comes from
CaDiCaL (exit 10 = SAT, 20 = UNSAT), found on PATH or in a Lean toolchain as in
seed_chart_forced_memory_audit.py, and each file is piped to it on stdin; the properness
assertions of sat_from_bytes are kept unchanged.

Semantics are checked against an Andreev function written from Kane-Williams' definition
(arXiv:1511.07860v1, p. 1): x in {0,1}^{2^k}, blocks a_{i,1..b}, i = 1..k,
A = x_{bin(p_1..p_k)} with p_i = parity of block i, bin MSB-first onto {1..2^k}.

Usage: python3 andreev_projection_copy_audit.py
"""

import subprocess
from itertools import product
from pathlib import Path
from random import Random


def find_cadical():
    from shutil import which
    found = which("cadical")
    if found:
        return found
    candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/cadical"))
    if candidates:
        return str(candidates[0])
    raise SystemExit("cadical not found: put it on PATH or install a Lean toolchain")


CADICAL = find_cadical()


# ---------------- verbatim copies from the journal ----------------
def bank_name(bank, suffix, digits):
    return int(str(bank) + format(suffix, f"0{digits}b"))


def encode(r, m, h, source):
    """First 2**r bits form the table; the rest are r successive parity rows."""
    n = 1 << r
    assert 1 <= h <= n and h & (h - 1) == 0 and m > 0 and len(source) == n + r * m
    limit = 3 * 10**h - 1
    maximum = limit
    core = []

    def fresh():
        nonlocal maximum
        maximum += 1
        return maximum

    def xor(a, b):
        c = fresh()
        core.extend([(a, b, -c), (a, -b, c), (-a, b, c), (-a, -b, -c)])
        return c

    def scalar(bank, bits):
        mask = sum(bit << i for i, bit in enumerate(bits))
        lib = bank_name(bank, mask, h)
        c = fresh()
        core.extend([(-c, lib), (c, -lib)])
        return c

    anchors = [fresh() for _ in range(3)]
    mask_names = {bank_name(b, mask, h) for b in (1, 2) for mask in range(1 << h)}
    for mask in range(1 << h):
        name = bank_name(1, mask, h)
        core.append((name if mask.bit_count() % 2 else -name,))
    for name in range(1, limit + 1):
        if name not in mask_names:
            core.append((-anchors[0], name, anchors[1]))

    address = []
    for j in range(r):
        row = source[n + j * m:n + (j + 1) * m]
        chunks = [scalar(1, row[i:i + h]) for i in range(0, m, h)]
        parity = chunks[0]
        for chunk in chunks[1:]:
            parity = xor(parity, chunk)
        address.append(parity)

    # The two children of a low-address prefix represent parent AND the relevant literal.
    levels = [fresh()]
    core.append((levels[0],))
    low_bits = h.bit_length() - 1
    for selector in reversed(address[:low_bits]):
        children = []
        for parent in levels:
            for literal in (-selector, selector):
                c = fresh()
                core.extend([(-c, parent), (-c, literal), (c, -parent, -literal)])
                children.append(c)
        levels = children
    for mask in range(1 << h):
        lookup = bank_name(2, mask, h)
        for offset, chosen in enumerate(levels):
            core.append((-chosen, lookup if mask & (1 << offset) else -lookup))

    table = [scalar(2, source[i:i + h]) for i in range(0, n, h)]
    for selector in address[low_bits:]:
        reduced = []
        for lo, hi in zip(table[::2], table[1::2]):
            c = fresh()
            core.extend([(selector, -lo, c), (selector, lo, -c),
                         (-selector, -hi, c), (-selector, hi, -c)])
            reduced.append(c)
        table = reduced
    core.append((table[0],))

    proper = [tuple(-a if bit else a for a, bit in zip(anchors, bits))
              for bits in product(range(2), repeat=3) if any(bits)]
    proper.extend((*clause, *anchors[:3 - len(clause)]) for clause in core)
    lines = [f'p cnf {maximum} {len(proper)}\n']
    lines.extend(f'{a} {b} {c} 0\n' for a, b, c in proper)
    return ''.join(lines).encode('ascii')
# ---------------- end of verbatim copies ----------------


def proper_clauses(file):
    """The journal's properness assertions (from sat_from_bytes), solver removed."""
    header, *lines = file.decode("ascii").splitlines()
    p, cnf, variables, count = header.split()
    assert (p, cnf) == ("p", "cnf") and int(count) == len(lines)
    names = set()
    for line in lines:
        a, b, c, end = map(int, line.split())
        terms = [a, b, c]
        assert end == 0 and len({abs(t) for t in terms}) == 3
        names.update(map(abs, terms))
    assert names == set(range(1, int(variables) + 1))
    return int(variables), int(count)


def sat_cadical(file):
    proper_clauses(file)
    rc = subprocess.run([CADICAL, '-q'], input=file, stdout=subprocess.DEVNULL).returncode
    assert rc in (10, 20), rc
    return rc == 10


def kw_andreev(x, a):
    """Kane-Williams' definition. x: list of 2^k bits (x_1..x_{2^k} as x[0..]);
    a: list of k blocks (block i = a[i-1]). bin is MSB-first: a_1 most significant."""
    k = len(a)
    p = [sum(block) % 2 for block in a]
    index1 = 1 + sum(p[i] << (k - 1 - i) for i in range(k))   # in {1..2^k}
    return x[index1 - 1]


def journal_to_kw(source, r, m):
    """Explicit copy map: x_t = T[t-1]; block i = row r-i (i = 1..r)."""
    n = 1 << r
    table = source[:n]
    rows = [source[n + j * m:n + (j + 1) * m] for j in range(r)]
    return table, [rows[r - i] for i in range(1, r + 1)]


def column_check(r, m, h):
    """Each source bit flips exactly two disjoint bytes '0'->'1' (bit 0 only)."""
    n = 1 << r
    k = n + r * m
    zero = [0] * k
    base = encode(r, m, h, zero)
    occupied, copies = set(), []
    for pos in range(k):
        single = zero.copy()
        single[pos] = 1
        var = encode(r, m, h, single)
        assert len(var) == len(base)
        changed = {i for i, (u, v) in enumerate(zip(base, var)) if u != v}
        assert len(changed) == 2 and changed.isdisjoint(occupied)
        assert all((base[i], var[i]) == (48, 49) and base[i] ^ var[i] == 1 for i in changed)
        occupied.update(changed)
        copies.append(sorted(changed))
    return base, copies


def signature_check(r, m, h, rng, randoms):
    """Large-r copy check without k single-bit flips: binary-coded probes identify
    the source index behind every varying byte; random inputs then confirm
    byte = '0' + x_i at every varying byte and constancy elsewhere."""
    n = 1 << r
    k = n + r * m
    bits = k.bit_length()
    probes = [[(i >> t) & 1 for i in range(k)] for t in range(bits)]
    probes += [[1] * k, [0] * k]
    files = [encode(r, m, h, s) for s in probes]
    L = len(files[-1])
    assert all(len(f) == L for f in files)
    base = files[-1]
    varying = [i for i in range(L) if any(f[i] != base[i] for f in files)]
    owner = {}
    for pos in varying:
        assert base[pos] == 48 and files[-2][pos] == 49
        idx = sum(((files[t][pos] - 48) & 1) << t for t in range(bits))
        assert all(files[t][pos] in (48, 49) for t in range(bits))
        owner.setdefault(idx, []).append(pos)
    assert sorted(owner) == list(range(k)) and all(len(v) == 2 for v in owner.values())
    for _ in range(randoms):
        s = [rng.randrange(2) for _ in range(k)]
        f = encode(r, m, h, s)
        expect = bytearray(base)
        for idx, poss in owner.items():
            for pos in poss:
                expect[pos] = 48 + s[idx]
        assert f == bytes(expect)
    return k, len(varying), L


def check_semantics(r, m, h, sources):
    count = 0
    for s in sources:
        f = encode(r, m, h, s)
        x, a = journal_to_kw(s, r, m)
        assert sat_cadical(f) == bool(kw_andreev(x, a)), (r, m, h, s)
        count += 1
    return count


def main():
    rng = Random(20261127)
    total = 0
    # 1. Exhaustive at KW's shape k=2 (b = 2^2/2 = 2), h = 2: all 256 inputs.
    c = check_semantics(2, 2, 2, product(range(2), repeat=8))
    print(f'exhaustive (r,m,h)=(2,2,2): {c} inputs, SAT verdict == KW Andreev on all')
    total += c
    # 2. Exhaustive truth table at k=3, b=floor(8/3)=2, h=2 (8+6 = 14 bits, 16384 inputs).
    c = check_semantics(3, 2, 2, product(range(2), repeat=14))
    print(f'exhaustive (r,m,h)=(3,2,2): {c} inputs, SAT verdict == KW Andreev on all')
    total += c
    # 3. Random samples: KW shapes b = floor(2^k/k), incl. canonical h for r >= 8.
    layouts = [(4, 4, 2, 60), (4, 4, 4, 60), (5, 6, 2, 60), (5, 6, 4, 40), (6, 10, 4, 40),
               (8, 32, 1, 60), (9, 56, 1, 30), (12, 341, 1, 10), (16, 4096, 2, 4)]
    for r, m, h, cnt in layouts:
        k = (1 << r) + r * m
        samples = [[rng.randrange(2) for _ in range(k)] for _ in range(cnt)]
        # include constant-address extremes: all-zero rows and all-one rows
        samples.append([rng.randrange(2) for _ in range(1 << r)] + [0] * (r * m))
        samples.append([rng.randrange(2) for _ in range(1 << r)] + [1] * (r * m))
        c = check_semantics(r, m, h, samples)
        print(f'random (r,m,h)=({r},{m},{h}): {c} inputs agree')
        total += c
    print(f'TOTAL CaDiCaL verdicts matching KW Andreev: {total}')
    # 4. Single-bit column checks.
    cols = 0
    for r, m, h in [(2, 2, 2), (3, 2, 2), (4, 4, 2), (4, 4, 4), (5, 6, 2), (8, 32, 1)]:
        base, copies = column_check(r, m, h)
        cols += len(copies)
        print(f'column check (r,m,h)=({r},{m},{h}): {len(copies)} source bits, '
              f'each -> exactly 2 bytes 48->49, file {len(base)} bytes')
    print(f'TOTAL single-bit columns checked: {cols}')
    # 5. Binary-probe copy checks at canonical larger r.
    for r, m, h, randoms in [(12, 341, 1, 6), (16, 4096, 2, 4)]:
        k, nv, L = signature_check(r, m, h, rng, randoms)
        print(f'probe copy check (r,m,h)=({r},{m},{h}): {k} source bits, {nv} varying bytes '
              f'(= 2 per bit), file {L} bytes = {8 * L} bits')


if __name__ == '__main__':
    main()
