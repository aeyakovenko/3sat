"""Independent finite audit for seed rows and the pinned files.

Run from the directory that holds this script:
    python3 -B seed_chart_forced_memory_audit.py

It shares no code with seed_interval_check_audit.py, except that section C
compares its serialized files byte for byte with that script's generator.
Nothing is written to disk. CaDiCaL is taken from PATH or from an elan toolchain.
"""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb, factorial, lgamma, log, log2
from pathlib import Path
from random import Random
from subprocess import run
import sys

import numpy as np

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


# --------------------------------------------------------------------------
# Polynomials over F_2 in n seed variables: a set of monomial masks (ANF).
# --------------------------------------------------------------------------

def mobius(vec, n):
    """Subset-sum transform mod 2. It is its own inverse (ANF <-> truth table)."""
    v = vec.copy().reshape([2] * n) if n else vec.copy()
    for axis in range(n):
        hi = [slice(None)] * n
        lo = [slice(None)] * n
        hi[axis], lo[axis] = 1, 0
        v[tuple(hi)] ^= v[tuple(lo)]
    return v.reshape(-1)


def table_of(poly, n):
    coeff = np.zeros(1 << n, dtype=np.uint8)
    for mask in poly:
        coeff[mask] ^= 1
    return mobius(coeff, n)


def degree(poly):
    return max((m.bit_count() for m in poly), default=0)


def random_poly(rng, n, d, constant_rate=0.35):
    if rng.random() < constant_rate or d == 0:
        return {0} if rng.random() < 0.5 else set()
    poly = set()
    for _ in range(rng.randrange(1, 4)):
        size = rng.randrange(1, d + 1)
        poly ^= {sum(1 << j for j in rng.sample(range(n), size))}
    if rng.random() < 0.3:
        poly ^= {0}
    return poly


# --------------------------------------------------------------------------
# A. Word-RAM blocks with indirect loads and stores and a seed routine.
#    Two 2-bit registers, four 2-bit cells; the register value is an address.
# --------------------------------------------------------------------------
W, NREG, NCELL = 2, 2, 4
NSTATE = W * (NREG + NCELL)


def reg_base(i):
    return W * i


def cell_base(a):
    return W * (NREG + a)


def random_program(rng, n):
    program = []
    for _ in range(rng.randrange(1, 5)):
        kind = rng.choice(["load", "load", "store", "store", "add", "and", "const",
                           "skipz", "sread", "swrite"])
        i, j = rng.randrange(NREG), rng.randrange(NREG)
        if kind == "const":
            program.append((kind, i, rng.randrange(1 << W)))
        elif kind == "skipz":
            program.append((kind, i))
        elif kind in ("sread", "swrite"):
            program.append((kind, i, j, rng.randrange(n)))
        else:
            program.append((kind, i, j))
    return program


def run_block(program, entry, seed, n):
    """Execute one block from the packed entry state and the seed.

    Returns the ordered query path, the state assignments and the seed
    assignments.  A coordinate is queried only if it is read before the
    block has assigned it; a later read returns the assigned constant.
    """
    known, assigned, sknown, sassigned, path = {}, {}, {}, {}, []

    def read_word(base):
        value = 0
        for k in range(W):
            c = base + k
            if c not in known:
                known[c] = entry >> c & 1
                path.append((0, c, known[c]))
            value |= known[c] << k
        return value

    def write_word(base, value):
        for k in range(W):
            known[base + k] = assigned[base + k] = value >> k & 1

    pc = 0
    while pc < len(program):
        ins = program[pc]
        kind = ins[0]
        pc += 1
        if kind == "load":
            write_word(reg_base(ins[1]), read_word(cell_base(read_word(reg_base(ins[2])))))
        elif kind == "store":
            address = read_word(reg_base(ins[2]))
            write_word(cell_base(address), read_word(reg_base(ins[1])))
        elif kind == "add":
            write_word(reg_base(ins[1]),
                       (read_word(reg_base(ins[1])) + read_word(reg_base(ins[2]))) % (1 << W))
        elif kind == "and":
            write_word(reg_base(ins[1]),
                       read_word(reg_base(ins[1])) & read_word(reg_base(ins[2])))
        elif kind == "const":
            write_word(reg_base(ins[1]), ins[2])
        elif kind == "skipz":
            if read_word(reg_base(ins[1])) == 0:
                pc += 1
        elif kind == "sread":
            j = (ins[3] + read_word(reg_base(ins[2]))) % n
            if j not in sknown:
                sknown[j] = seed >> j & 1
                path.append((1, j, sknown[j]))
            write_word(reg_base(ins[1]), sknown[j])
        elif kind == "swrite":
            j = (ins[3] + read_word(reg_base(ins[2]))) % n
            sknown[j] = sassigned[j] = read_word(reg_base(ins[1])) & 1
    return tuple(path), assigned, sassigned


def check_blocks():
    rng = Random(20261127)
    n = 12
    size = 1 << n
    seeds = np.arange(size, dtype=np.int64)
    pop = np.array([s.bit_count() for s in range(size)])
    counts = Counter()
    largest_tight = 0
    for trial in range(260):
        d = (0, 1, 1, 2, 2, 3)[trial % 6]
        old = [random_poly(rng, n, d) for _ in range(NSTATE)]
        new = ([set(p) for p in old] if trial % 2 == 0
               else [random_poly(rng, n, d) for _ in range(NSTATE)])
        incoming = [random_poly(rng, n, 2, 0.0) for _ in range(trial % 3)]
        outgoing = [random_poly(rng, n, 2, 0.0) for _ in range(trial % 2)]
        program = random_program(rng, n)
        old_t = [table_of(p, n) for p in old]
        new_t = [table_of(p, n) for p in new]
        in_t = [table_of(p, n) for p in incoming]
        out_t = [table_of(p, n) for p in outgoing]
        entry = np.zeros(size, dtype=np.int64)
        for c, t in enumerate(old_t):
            entry |= t.astype(np.int64) << c
        entry = entry.tolist()
        allowed = np.ones(size, dtype=bool)
        for t in in_t:
            allowed &= t == 0
        leaves = {}
        groups = {}
        for s in range(size):
            path, assigned, sassigned = run_block(program, entry[s], s, n)
            if path in leaves:
                assert leaves[path] == (assigned, sassigned)   # a leaf fixes all writes
            else:
                leaves[path] = (assigned, sassigned)
            if not allowed[s]:
                continue
            updated = s
            for j, bit in sassigned.items():
                updated = updated & ~(1 << j) | bit << j
            for c in range(NSTATE):
                actual = assigned[c] if c in assigned else entry[s] >> c & 1
                if actual != new_t[c][updated]:
                    groups.setdefault((path, 0, c), []).append(s)
            for k, t in enumerate(out_t):
                if t[updated]:
                    groups.setdefault((path, 1, k), []).append(s)
        counts["leaves"] += len(leaves)
        for (path, kind, index), members in groups.items():
            assigned, sassigned = leaves[path]
            queried = {c for tag, c, _ in path if tag == 0}
            aux = {j for tag, j, _ in path if tag == 1}
            base = (sum(degree(old[c]) for c in queried) + len(aux)
                    + sum(degree(p) for p in incoming))
            if kind == 1:
                residual = degree(outgoing[index])
            elif index in assigned or index in queried:
                residual = degree(new[index])      # the exit bit is a constant on this leaf
            else:
                residual = max(degree(old[index]), degree(new[index]))
            bound = base + residual
            indicator = np.zeros(size, dtype=np.uint8)
            indicator[members] = 1
            # The closed formula used in the proof, evaluated independently.
            formula = allowed.copy()
            for tag, c, bit in path:
                column = old_t[c] if tag == 0 else (seeds >> c & 1)
                formula &= column == bit
            moved = seeds.copy()
            for j, bit in sassigned.items():
                moved = moved & ~(1 << j) | bit << j
            if kind == 1:
                formula &= out_t[index][moved] == 1
            else:
                actual = (np.full(size, assigned[index]) if index in assigned
                          else old_t[index])
                formula &= actual != new_t[index][moved]
            assert np.array_equal(formula.astype(np.uint8), indicator)
            anf = mobius(indicator, n)
            anf_degree = int(pop[anf.nonzero()[0]].max())
            least = int(pop[members].min())
            assert anf_degree <= bound
            assert least == int(pop[anf.nonzero()[0]].min()) <= bound
            # Every failing seed lies above a failing seed of weight <= bound.
            small = [s for s in members if pop[s] <= bound]
            if bound < n:
                small_arr = np.array(small, dtype=np.int64)
                for s in members[:: max(1, len(members) // 40)]:
                    assert np.any(small_arr & ~s == 0)
            counts["failing leaf-coordinate groups"] += 1
            counts["groups with bound below the seed length"] += bound < n
            counts["groups whose normal form has degree equal to the bound"] += anf_degree == bound
            counts["groups whose least failing weight equals the bound"] += least == bound
            counts["of those, groups with bound 0"] += least == bound == 0
            counts["groups from an outgoing equation"] += kind == 1
            if anf_degree == bound:
                largest_tight = max(largest_tight, bound)
        counts["blocks"] += 1
        counts["block executions"] += size
    print("A. word blocks:", dict(counts), "largest tight bound", largest_tight)


# --------------------------------------------------------------------------
# B. Sharpness: a unique failing seed of weight exactly d(q+1)+a.
# --------------------------------------------------------------------------

def check_sharp():
    cases = total_seeds = largest = 0
    for d, q, a, variant in product(range(4), range(5), range(4), ("state", "seed")):
        total = d * (q + 1) + a
        if total > 18 or (variant == "seed" and d == 0):
            continue
        n = max(total, 1)
        blocks = [((1 << d) - 1) << (d * j) for j in range(q + 1)]
        side = [d * (q + 1) + k for k in range(a)]
        failing = []
        for s in range(1 << n):
            cell = [int(s & mask == mask) for mask in blocks]     # degree-d monomials
            fired = all(cell[:q]) and all(s >> j & 1 for j in side)
            if variant == "state":            # the block stores 0 in the last cell
                actual = 0 if fired else cell[q]
                claimed = cell[q]             # same row, same seed
            else:                             # the routine clears one seed bit
                actual = cell[q]
                moved = s & ~(1 << (d * q)) if fired else s
                claimed = int(moved & blocks[q] == blocks[q])
            if actual != claimed:
                failing.append(s)
        if total:
            assert failing == [(1 << n) - 1]
        assert min(x.bit_count() for x in failing) == total
        # queried cells cost d each, aux reads one each, the residual costs d
        assert d * q + a + d == total
        cases += 1
        total_seeds += 1 << n
        largest = max(largest, total)
    print("B. sharp instances / seeds enumerated / largest forced weight:",
          cases, total_seeds, largest)


# --------------------------------------------------------------------------
# C. The pinned files, two solvers, and the forced suffix.
# --------------------------------------------------------------------------

def pinned_file(f):
    m = len(f)
    v = m + 3
    digits = len(str(v))
    rows = [tuple(-j if bits >> (j - 1) & 1 else j for j in (1, 2, 3)) for bits in range(1, 8)]
    rows += [(-1, 4 + j, 2) for j in range(m)]
    rows += [((4 + y) if i < m // 2 else -(4 + y), 1, 2) for i, y in enumerate(f)]
    text = f"p cnf {v} {len(rows)}\n" + "".join(
        " ".join(f"{lit:>{digits + 1}}" for lit in row) + " 0\n" for row in rows)
    data = text.encode("ascii")
    assert len(data) == 8 + digits + len(str(2 * m + 7)) + (2 * m + 7) * (3 * digits + 8)
    return data


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


def brute_force(v, clauses):
    grid = np.arange(1 << v, dtype=np.int64)
    alive = np.ones(1 << v, dtype=bool)
    for clause in clauses:
        hit = np.zeros(1 << v, dtype=bool)
        for lit in clause:
            bit = (grid >> (abs(lit) - 1) & 1) == 1
            hit |= bit if lit > 0 else ~bit
        alive &= hit
    return bool(alive.any())


def cadical(data):
    result = run([CADICAL, "-q"], input=data, capture_output=True)
    assert result.returncode in (10, 20), result.stderr
    return result.returncode == 10


def units_of(data):
    """The m signed names in file order, read from the last m physical rows."""
    v, clauses = parse(data)
    m = v - 3
    assert len(clauses) == 2 * m + 7
    assert clauses[7:7 + m] == [(-1, 4 + j, 2) for j in range(m)]
    units = []
    for i, (lit, one, two) in enumerate(clauses[7 + m:]):
        assert (one, two) == (1, 2) and (lit > 0) == (i < m // 2)
        units.append((lit > 0, abs(lit) - 4))
    return m, units


def mark_solver(data):
    m, units = units_of(data)
    mark = [0] * m                       # 0 unseen, 1 positive, 2 negative
    for steps, (positive, name) in enumerate(units, 1):
        want = 1 if positive else 2
        if mark[name] and mark[name] != want:
            return False, steps
        mark[name] = want
    return True, m


def endpoint_tail(f, bank, start):
    """Phase 2 of the scatter solver from loop index `start`; it trusts the bank."""
    m = len(f)
    return all(1 <= bank[y] <= m and f[bank[y] - 1] == y for y in range(start, m))


def scatter_solver(data, bank=None, start=0):
    """Returns (verdict, loop iterations, used_fallback)."""
    m, units = units_of(data)
    f = [name for _, name in units]
    bank = [0] * m if bank is None else list(bank)
    for i in range(start, m):
        last = bank[f[i]] - 1
        if last >= 0 and (last < m // 2) == (i < m // 2):
            return mark_solver(data)[0], i - start + 1 + m, True    # complete fallback
        bank[f[i]] = i + 1
    return endpoint_tail(f, bank, 0), 2 * m - start, False


def check_files():
    counts = Counter()
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import seed_interval_check_audit as worker          # byte comparison only
    rng = Random(9)
    for m in (2, 4, 6):
        for f in product(range(m), repeat=m):
            data = pinned_file(f)
            if m <= 4 or rng.random() < 0.01:
                assert data == worker.pinned_file(f)
                counts["byte-identical to the worker's generator"] += 1
            halves = set(f[:m // 2]), set(f[m // 2:])
            disjoint = halves[0].isdisjoint(halves[1])
            v, clauses = parse(data)
            assert brute_force(v, clauses) == disjoint
            counts["files decided by enumerating all assignments"] += 1
            if m <= 4 or rng.random() < 0.01:
                assert cadical(data) == disjoint
                counts["files decided by cadical"] += 1
            verdict, steps, fallback = scatter_solver(data)
            assert verdict == disjoint and steps <= 2 * m
            answer, marks = mark_solver(data)
            assert answer == disjoint and marks <= m
            injective = all(len(h) == m // 2 for h in halves)
            assert fallback == (not injective)
            counts["scatter runs without fallback"] += not fallback
            counts["largest loop count / m, scatter"] = max(
                counts["largest loop count / m, scatter"], -(-steps // m))
            counts["SAT" if disjoint else "UNSAT"] += 1
    for m in (8, 16, 64):
        for _ in range(60):
            f = [rng.randrange(m) for _ in range(m)]
            if rng.random() < 0.5:
                f = rng.sample(range(m), m)
            data = pinned_file(f)
            disjoint = set(f[:m // 2]).isdisjoint(f[m // 2:])
            assert cadical(data) == disjoint == scatter_solver(data)[0] == mark_solver(data)[0]
            counts["larger random files decided by cadical"] += 1
    print("C1. files:", dict(counts))
    for m in (4, 256, 4096, 65536):
        bits = 8 * len(pinned_file(list(range(m))))
        print(f"    m={m}: N={bits} bits, N/(m log2 m)={bits / (m * log2(m)):.4f}, "
              f"log2(m!)/N={log2(factorial(m)) / bits:.4f}")
    print(f"    limit of N/(m log2 m): 48/log2(10) = {48 / log2(10):.6f}")

    # Forced suffix in phase 2, and the fallback escape in phase 1.
    forced = Counter()
    m = 4
    for f in permutations(range(m)):
        data = pinned_file(f)
        true = [0] * m
        for i, y in enumerate(f):
            true[y] = i + 1
        for start in range(m + 1):
            for bank in product(range(m + 2), repeat=m):
                accept = endpoint_tail(f, bank, start)
                assert accept == (list(bank[start:]) == true[start:])
                forced["phase-2 banks"] += 1
                forced["phase-2 accepting banks"] += accept
        for i in range(m + 1):
            written = set(f[:i])
            for bank in product(range(m + 2), repeat=m):
                verdict, _, fallback = scatter_solver(data, bank, i)
                right = all(bank[y] == true[y] for y in written)
                assert verdict == (right or fallback)
                forced["phase-1 banks"] += 1
                forced["phase-1 banks accepted with a wrong written cell"] += verdict and not right
    m = 6
    rng = Random(6)
    for f in permutations(range(m)):
        true = [0] * m
        for i, y in enumerate(f):
            true[y] = i + 1
        for start in range(m + 1):
            for y, value in product(range(m), range(m + 2)):
                bank = true.copy()
                bank[y] = value
                assert endpoint_tail(f, bank, start) == (y < start or value == true[y])
                forced["m=6 one-cell edits"] += 1
            for _ in range(4):
                bank = [rng.randrange(m + 2) for _ in range(m)]
                assert endpoint_tail(f, bank, start) == (bank[start:] == true[start:])
                forced["m=6 random banks"] += 1
    print("C2. forced suffix:", dict(forced))

    # Theorem 3 on the last loop iteration: every row for the one live cell,
    # three bits, each an arbitrary function of two seed bits.
    m = 4
    passing = rows = 0
    for f in permutations(range(m)):
        target = f.index(m - 1) + 1
        for functions in product(range(16), repeat=3):
            values = [sum((functions[k] >> s & 1) << k for k in range(3)) for s in range(4)]
            ok = all(1 <= value <= m and f[value - 1] == m - 1 for value in values)
            assert ok == all(value == target for value in values)
            passing += ok
            rows += 1
    print("C3. rows for the last live cell / rows sound on every seed:", rows, passing)


# --------------------------------------------------------------------------
# C4. The worker's first family (recovered from its log): SAT iff some name is
#     missing from the image.  Here the table is forced on REJECTING runs.
# --------------------------------------------------------------------------

def missing_file(f):
    m = len(f)
    x = lambda j: 4 + j
    prefix = lambda j: 4 + m + j
    v = 2 * m + 3
    digits = len(str(v))
    rows = [tuple(-j if bits >> (j - 1) & 1 else j for j in (1, 2, 3)) for bits in range(1, 8)]
    rows += [(-prefix(0), x(0), 1), (prefix(0), -x(0), 1)]
    for j in range(1, m):
        rows += [(-prefix(j - 1), prefix(j), 1), (-x(j), prefix(j), 1),
                 (prefix(j - 1), x(j), -prefix(j))]
    rows.append((prefix(m - 1), 1, 2))
    rows += [(-x(y), 1, 2) for y in f]
    text = f"p cnf {v} {len(rows)}\n" + "".join(
        " ".join(f"{lit:>{digits + 1}}" for lit in row) + " 0\n" for row in rows)
    data = text.encode("ascii")
    assert len(rows) == 4 * m + 7
    assert len(data) == 8 + digits + len(str(4 * m + 7)) + (4 * m + 7) * (3 * digits + 8)
    return data


def surjection_tail(f, bank, start):
    """Phase 2 of the second scatter program: True means the UNSAT signal."""
    m = len(f)
    return all(1 <= bank[y] <= m and f[bank[y] - 1] == y for y in range(start, m))


def surjection_solver(f, bank=None, start=0):
    """Scatter i+1 to B[f(i)], then verify every name. No fallback is needed."""
    m = len(f)
    bank = [0] * m if bank is None else list(bank)
    for i in range(start, m):
        bank[f[i]] = i + 1
    return surjection_tail(f, bank, 0)


def check_first_family():
    counts = Counter()
    for m in (2, 3, 4):
        for f in product(range(m), repeat=m):
            data = missing_file(f)
            names = [-int(line.split()[0]) - 4 for line in data.decode().splitlines()[-m:]]
            assert tuple(names) == f
            onto = len(set(f)) == m
            v, clauses = parse(data)
            assert brute_force(v, clauses) == (not onto) == cadical(data)
            assert surjection_solver(f) == onto          # UNSAT signal iff permutation
            counts["UNSAT (permutations)" if onto else "SAT"] += 1
    for m in (4, 256, 4096):
        print(f"    first family m={m}: N={8 * len(missing_file(list(range(m))))} bits")
    for m in (3, 4):
        for f in permutations(range(m)):
            true = [0] * m
            for i, y in enumerate(f):
                true[y] = i + 1
            for bank in product(range(m + 2), repeat=m):
                for y in range(m + 1):       # phase-2 loop heads
                    assert surjection_tail(f, bank, y) == (list(bank[y:]) == true[y:])
                    counts["phase-2 memories"] += 1
                for i in range(m + 1):       # phase-1 loop heads: written cells forced
                    written = set(f[:i])
                    assert surjection_solver(f, bank, i) == all(
                        bank[y] == true[y] for y in written)
                    counts["phase-1 memories"] += 1
    print("C4. first family:", dict(counts))


# --------------------------------------------------------------------------
# D. Adaptive exposure and the advice count.
# --------------------------------------------------------------------------

def check_exposure():
    rng = Random(77)
    cases = 0
    for m in (5, 6, 7):
        perms = list(permutations(range(m)))
        for _ in range(6 if m < 7 else 2):
            salt = rng.randrange(1 << 30)

            def next_position(history, remaining):
                return remaining[hash((salt, history)) % len(remaining)]

            for length in range(1, m + 1):
                tuples = Counter()
                for pi in perms:
                    remaining = list(range(m))
                    history = ()
                    for _ in range(length):
                        position = next_position(history, tuple(remaining))
                        remaining.remove(position)
                        history += (pi[position],)
                    tuples[history] += 1
                # the reply sequence is uniform over injective tuples
                assert len(tuples) == factorial(m) // factorial(m - length)
                assert set(tuples.values()) == {factorial(m - length)}
                for targets in range(1, min(length, 3) + 1):
                    hits = sum(count for history, count in tuples.items()
                               if set(range(targets)) <= set(history))
                    assert hits * comb(m, targets) == factorial(m) * comb(length, targets)
                    cases += 1
    print("D1. adaptive strategies x lengths x target counts with the exact law:", cases)

    print("D2. advice count: s >= log2 C(m,t) - log2 C(t(Q+1),t) - 1, maximised over t <= m/2")
    for m in (256, 4096, 65536):
        for probes in (1, 15, 255):
            width = probes + 1

            def estimate(t):
                def lc(a, b):
                    return (lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)) / log(2)
                return lc(m, t) - lc(t * width, t) - 1

            candidates = range(1, min(m // 2, m // width) + 1)
            simple = m // (2 * width) - 1
            if simple < 1:
                continue                     # the count says nothing at this budget
            t = max(candidates, key=estimate)
            exact = log2(comb(m, t)) - log2(comb(t * width, t)) - 1
            assert abs(exact - estimate(t)) < 1e-6 * max(1.0, exact)
            assert exact >= simple
            print(f"    m={m} Q={probes}: s >= {exact:.1f} bits at t={t};"
                  f" closed form floor(m/(2(Q+1)))-1 = {simple}")


# --------------------------------------------------------------------------
# E. A degree-one seed chart for the mark solver: advice = one model.
# --------------------------------------------------------------------------

def check_mark_chart():
    counts = Counter()
    for m in (2, 4):
        for f in product(range(m), repeat=m):
            data = pinned_file(f)
            _, units = units_of(data)
            satisfiable = set(f[:m // 2]).isdisjoint(f[m // 2:])
            passing = 0
            for sigma in product((True, False), repeat=m):     # claimed sign of each name
                def row(s):                                    # (P_a, Q_a) = sigma-bit * s_a
                    return [(int(sigma[a]) * (s >> a & 1), int(not sigma[a]) * (s >> a & 1))
                            for a in range(m)]
                good = True
                least = None
                for i, (positive, name) in enumerate(units):
                    for s in range(1 << m):
                        state = row(s)
                        p, q = state[name]
                        conflict = q if positive else p
                        if not conflict:
                            state[name] = (1, q) if positive else (p, 1)
                        claimed = row(s | 1 << name)           # seed routine: s_name := 1
                        if conflict or state != claimed:
                            good = False
                            weight = s.bit_count()
                            least = weight if least is None else min(least, weight)
                    if least is not None:
                        assert least <= 3      # d(q+1)+a with d=1, q=2 entry bits, a=0
                        counts["failing one-step blocks"] += 1
                        break
                assert good == all(sigma[name] == positive for positive, name in units)
                passing += good
                counts["charts checked on every seed"] += 1
            assert (passing > 0) == satisfiable
            assert passing == (2 ** (m - len(set(f))) if satisfiable else 0)
            counts["SAT files with a passing chart" if satisfiable
                   else "UNSAT files with no passing chart"] += 1
    # Forced bits of the two-bit mark pass on permutation files.
    m = 4
    for f in permutations(range(m)):
        for head in range(m + 1):
            for memory in product(range(4), repeat=m):       # bit 0 = P_a, bit 1 = Q_a
                marks = list(memory)
                accept = True
                for i in range(head, m):
                    positive = i < m // 2
                    if marks[f[i]] >> (1 if positive else 0) & 1:
                        accept = False
                        break
                    marks[f[i]] |= 1 if positive else 2
                opposite_clear = all(
                    not memory[f[i]] >> (1 if i < m // 2 else 0) & 1 for i in range(head, m))
                assert accept == opposite_clear
                counts["two-bit mark memories"] += 1
    print("E. mark-solver charts:", dict(counts))


if __name__ == "__main__":
    check_blocks()
    check_sharp()
    check_files()
    check_first_family()
    check_exposure()
    check_mark_chart()
