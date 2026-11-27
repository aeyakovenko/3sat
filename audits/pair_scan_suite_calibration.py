"""Suite-correct programs on the 5/2 suite, for five-halves-per-word-is-tight-on-the-single-edit-suite.md.

Suite (generating-fresh-addresses-on-one-native-sat-file.md): the positive
file F = prefix + A*m + trailer and its 2m single-word edits (one-bit B and the
whitespace alternative B' with B' = A mod w).  The layout code (positions, raw,
layout, sat, alternative) is copied from the journal audits
fresh_native_address_audit.py and dimacs_whitespace_residue_audit.py
(kept as copies so that this module is self-contained).

Machine: separate-operation RAM (five-instruction-loops-on-dimacs-sat.md):
registers start at zero, LOAD/STORE take a register or an immediate as the full
address, numerical ops are binary with register/immediate operands, a branch
compares two operands and jumps to a fixed target, verdicts are terminal.
Every executed instruction (including branches and the verdict) costs one step.
"""
import sys
from itertools import product


# ---------------- layout (copied from the journal audits) ----------------
def positions(width):
    k = 0
    while 256**(k+1) <= width//128:
        k += 1
    assert width/32768 < 256**k <= width/128 and k > 0
    return k


def raw(width, k, d, tag, inside_fmt="{d} 1 0\n"):
    word = bytearray(b" "*(width//8))
    inside = inside_fmt.format(d=d).encode()
    word[k:k+len(inside)] = inside
    word[-1] = ord(str(tag))
    return bytes(word)


def circular(a, b, mod):
    delta = (a-b) % mod
    return min(delta, mod-delta)


def layout(width, m):
    W = width//8
    head = f"p cnf 9 {m+17}\n".encode()

    def prefix(d):
        rows = [f"{l} {u} {v} 0\n".encode() for l in (-1, -d, 4, -5)
                for u, v in product((2, -2), (3, -3))]
        data = head+b"".join(rows)
        return data+b" "*((-len(data)-1) % W)+b"4"
    first = len(prefix(6))//W
    ell = (first+m-1).bit_length()
    k = positions(width)
    for d in (6, 7, 8, 9):
        a = raw(width, k, d, 4)
        r = int.from_bytes(a, "little") % width
        if all(circular(r, z, width) >= width/100000 for z in (0, width/2, width-ell)):
            assert len(prefix(d)) == first*W
            return prefix(d), a, raw(width, k, d, 5), f" {d} 1 0\n".encode(), ell, d
    raise AssertionError("no residue")


def alternative(a):
    w = 8 * len(a)
    q = w // (w & -w)
    b = bytearray(a)
    b[-1] = ord('5')
    delta = (int.from_bytes(a, 'little') - int.from_bytes(b, 'little')) % q
    previous = {0: None}
    for i in range(a.index(b'\n') + 1, len(a) - 1):
        if delta in previous:
            break
        if 1 << (8*i) < w:
            continue
        assert b[i] == 32
        weights = [(c, ((c-32) * pow(256, i, q)) % q) for c in (9, 10)]
        for residue in tuple(previous):
            for c, weight in weights:
                new = (residue + weight) % q
                if new not in previous:
                    previous[new] = residue, i, c
    assert delta in previous
    while delta:
        delta, i, byte = previous[delta]
        b[i] = byte
    assert int.from_bytes(a, 'little') % w == int.from_bytes(b, 'little') % w
    return bytes(b)


def sat(file):
    """Exact SAT by enumeration over the occurring variables (<= 9)."""
    header, rest = file.split(b"\n", 1)
    p, cnf, n, c = header.split()
    assert (p, cnf) == (b"p", b"cnf")
    ints = list(map(int, rest.split()))
    rows, cur = [], []
    for t in ints:
        if t == 0:
            rows.append(tuple(cur)); cur = []
        else:
            cur.append(t)
    assert not cur and len(rows) == int(c)
    rows = sorted(set(rows))
    names = sorted({abs(i) for row in rows for i in row})
    assert len(names) <= 9
    for assign in product((0, 1), repeat=len(names)):
        vals = dict(zip(names, assign))
        if all(any(vals[abs(t)] == (t > 0) for t in row) for row in rows):
            return True
    return False


# ---------------- RAM ----------------
def run(prog, words, width, limit):
    """prog: list of instructions; words: dict addr -> int.  Returns (verdict, steps)."""
    mask = (1 << width) - 1
    reg = {}
    mem = dict(words)
    pc = steps = 0

    def val(o):
        return o[1] if o[0] == 'i' else reg.get(o[1], 0)
    while steps < limit:
        ins = prog[pc]
        steps += 1
        op = ins[0]
        if op == 'load':
            reg[ins[1]] = mem.get(val(ins[2]) & mask, 0); pc += 1
        elif op == 'store':
            mem[val(ins[1]) & mask] = val(ins[2]) & mask; pc += 1
        elif op == 'add':
            reg[ins[1]] = (val(ins[2]) + val(ins[3])) & mask; pc += 1
        elif op == 'sub':
            reg[ins[1]] = (val(ins[2]) - val(ins[3])) & mask; pc += 1
        elif op == 'mov':
            reg[ins[1]] = val(ins[2]) & mask; pc += 1
        elif op == 'beq':
            pc = ins[3] if val(ins[1]) == val(ins[2]) else pc + 1
        elif op == 'bne':
            pc = ins[3] if val(ins[1]) != val(ins[2]) else pc + 1
        elif op == 'acc':
            return True, steps
        elif op == 'rej':
            return False, steps
        else:
            raise ValueError(ins)
    return None, steps


def assemble(lines):
    """lines: list of (label or None, instruction with symbolic targets)."""
    labels = {}
    for i, (lab, _) in enumerate(lines):
        if lab:
            labels[lab] = i
    out = []
    for _, ins in lines:
        if ins[0] in ('beq', 'bne'):
            ins = ins[:3] + (labels[ins[3]],)
        out.append(ins)
    return out


R = lambda x: ('r', x)
I = lambda x: ('i', x)


def pair_program(first, hard_pairs=0):
    """Constant-size pair loop, optionally preceded by hard_pairs hardwired pairs.

    Correct on {F} + single-word edits for ANY layout with m equal marked words at
    first..first+m-1, a trailer word T (T != A, T != 0) and a zero word after T.
    No use of n, w or the end address.
    """
    L = []
    # x1 := first marked word (needed only for the odd-m exit test)
    L.append((None, ('load', 'x1', I(first))))
    for j in range(hard_pairs):
        a1, a2 = first + 2*j, first + 2*j + 1
        L.append((None, ('load', 'u', I(a1))))
        L.append((None, ('load', 'v', I(a2))))
        L.append((None, ('bne', R('u'), R('v'), 'REJ')))
    start = first - 1 + 2*hard_pairs
    if start != 0:
        L.append((None, ('mov', 'p', I(start))))
    L += [
        ('loop', ('add', 'p', R('p'), I(1))),
        (None, ('load', 'u', R('p'))),
        (None, ('add', 'p', R('p'), I(1))),
        (None, ('load', 'v', R('p'))),
        (None, ('beq', R('u'), R('v'), 'loop')),
        (None, ('beq', R('v'), I(0), 'ACC')),      # m even: exit at (T, 0)
        (None, ('add', 'q', R('p'), I(1))),
        (None, ('load', 'z', R('q'))),
        (None, ('bne', R('z'), I(0), 'REJ')),       # exit inside the marked block
        (None, ('beq', R('u'), R('x1'), 'ACC')),    # m odd: exit at (A, T)
        ('REJ', ('rej',)),
        ('ACC', ('acc',)),
    ]
    return assemble(L)


def checksum_program(first, m, S, k):
    """Sum test for an ARBITRARY base with single-word edits, unrolled k times.

    Per-length immediates: S (sum of the base marked words mod 2^w) and the end
    address.  Steps 3m + ceil(m/k) + O(k)."""
    L = []
    full = m // k
    if first - 1 != 0:
        L.append((None, ('mov', 'p', I(first - 1))))
    endp = first - 1 + k*full
    if full:
        body = []
        for t in range(k):
            body.append(('loop' if t == 0 else None, ('add', 'p', R('p'), I(1))))
            body.append((None, ('load', 'x', R('p'))))
            body.append((None, ('add', 's', R('s'), R('x'))))
        L += body
        L.append((None, ('bne', R('p'), I(endp), 'loop')))
    for t in range(m - k*full):              # straight-line tail
        L.append((None, ('add', 'p', R('p'), I(1))))
        L.append((None, ('load', 'x', R('p'))))
        L.append((None, ('add', 's', R('s'), R('x'))))
    L.append((None, ('beq', R('s'), I(S), 'ACC')))
    L.append(('REJ', ('rej',)))
    L.append(('ACC', ('acc',)))
    return assemble(L)


def words_of(file, W):
    return {i: int.from_bytes(file[i*W:(i+1)*W].ljust(W, b"\0"), "little")
            for i in range((len(file)+W-1)//W)}


def suite(width, m, check_sat):
    prefix, a, b1, trailer, ell, d = layout(width, m)
    b2 = alternative(a)
    W = len(a)
    first = len(prefix)//W
    base = prefix + a*m + trailer
    files = [(base, True)]
    for i in range(m):
        for b in (b1, b2):
            files.append((prefix + a*i + b + a*(m-1-i) + trailer, False))
    if check_sat:
        for f, ans in files:
            assert sat(f) == ans
    return first, a, files


def main():
    widths = [32768, 33024, 49152]
    ms = [int(x) for x in sys.argv[1:]] or [6, 7, 40, 41, 120, 121, 300, 301]
    print("width m first | PAIR steps(base) 5m/2 diff | HYB j instr steps saved/instr"
          " | CHK k steps 3m+m/k")
    for width in widths:
        for m in ms:
            first, a, files = suite(width, m, check_sat=(m <= 41))
            W = len(a)
            mask = (1 << width) - 1
            # PAIR: constant size, correct on every suite file
            prog = pair_program(first)
            base_steps = None
            for f, ans in files:
                v, s = run(prog, words_of(f, W), width, 10*m + 100)
                assert v == ans, (width, m, ans, v)
                assert s <= 5*m//2 + 20
                if ans:
                    base_steps = s
            # HYBRID: j hardwired pairs
            hyb = []
            for j in (0, m//8, m//4, m//2 - 1):
                if j < 0:
                    continue
                hp = pair_program(first, j)
                for f, ans in files:
                    v, s = run(hp, words_of(f, W), width, 10*m + 100)
                    assert v == ans
                    if ans:
                        hyb.append((j, len(hp), s))
            j0, c0, s0 = hyb[0]
            rates = [(j, c, s, (s0 - s)/(c - c0) if c > c0 else 0.0) for j, c, s in hyb]
            # CHECKSUM: arbitrary-base method, k = 4
            S = (int.from_bytes(a, "little") * m) & mask
            k = 4
            cp = checksum_program(first, m, S, k)
            chk = None
            for f, ans in files:
                v, s = run(cp, words_of(f, W), width, 10*m + 100)
                assert v == ans
                if ans:
                    chk = s
            print(f"{width} {m} {first} | PAIR {base_steps} {5*m/2} {base_steps-5*m/2:+.1f} "
                  f"(size {len(prog)}) | "
                  + " ".join(f"j={j}:C={c},T={s},r={r:.3f}" for j, c, s, r in rates)
                  + f" | CHK k={k} T={chk} 3m+m/k={3*m+m/k:.1f} (size {len(cp)})")
    print("all suite files classified correctly by PAIR, HYBRID and CHECKSUM")


if __name__ == "__main__":
    main()
