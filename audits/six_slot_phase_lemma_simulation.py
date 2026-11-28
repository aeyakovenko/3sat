#!/usr/bin/env python3
"""Finite check of the phase lemma of
notes/one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md on synthetic memory,
for the two hardest of the 18 two-loop shapes, each with the numerical loop first:
L1S1A1B3 `C:AS C:L |seq` and `C:A C:LS |seq`.

Memory: w = 16, 400 input words of an even three-word palette H, zero elsewhere. Each run
draws an opcode, operands among four registers (starting at 0, N, w, 0) and three literals,
the order of the numerical instruction and the STORE in `C:AS`, an exit test, and a cap of
1 to 3,000 steps for the numerical loop. It then runs the LOAD loop (the LOAD, then the
STORE in `C:LS`) until its exit test holds, for at most 10 to 2,000 turns.

Claim checked: every address read by the LOAD lies in V = Z u LIT u H u E u {0}, where
Z = the registers at entry to the LOAD loop, LIT = the literals, H = the palette and
E = the values of written cells that do not hold their own address; and
|E| <= |F| + |LIT| + 1 for `C:AS`, where F = the registers that loop does not write.
Also reports the largest number of distinct addresses read and the largest |V|.

Run from audits/:
  python3 six_slot_phase_lemma_simulation.py [SEED]
      20,000 runs per shape (seed 1 by default, about 15 s);
  python3 six_slot_phase_lemma_simulation.py --control
      a numerical loop with two numerical sites, outside the 18 classes, which writes a
      linked list; there the check must fail.
Nothing is written.
"""
import random, sys

W = 16
Q = 1 << W
MASK = Q - 1
L = 400                       # input words
N = 8 * 2 * L                 # an even public length
H = [0x2A20, 0x3A14, 0x2C1E]  # even words, as on the periodic base
LITS_POOL = [1, 3, 5, 7, 2, 4, 0x8001, Q - 1, Q - 3, 9, 17, 255, 256]

OPS = {
    "add": lambda a, b: (a + b) & MASK, "sub": lambda a, b: (a - b) & MASK,
    "mul": lambda a, b: (a * b) & MASK, "xor": lambda a, b: a ^ b,
    "and": lambda a, b: a & b, "or": lambda a, b: a | b,
    "shl": lambda a, b: (a << (b % W)) & MASK, "shr": lambda a, b: a >> (b % W),
    "rotl": lambda a, b: ((a << (b % W)) | (a >> ((W - b % W) % W))) & MASK,
    "mov": lambda a, b: b,
}
CMPS = {"eq": lambda a, b: a == b, "ne": lambda a, b: a != b,
        "ult": lambda a, b: a < b, "uge": lambda a, b: a >= b}


def mem_init():
    m = {}
    for i in range(L):
        m[i] = H[i % len(H)]
    return m


def operand(regs, o):
    return regs[o[1]] if o[0] == "r" else o[1]


def rand_operand(rng, nregs, lits):
    return ("r", rng.randrange(nregs)) if rng.random() < 0.6 else ("l", rng.choice(lits))


def run(rng, shape):
    nregs = 4
    lits = rng.sample(LITS_POOL, 3)
    regs = [0, N, W, 0]
    mem = mem_init()
    written = set()
    # numerical loop: A (and S for C:AS); branch exit test
    d = rng.randrange(nregs)
    op = rng.choice(list(OPS))
    a_src = (rand_operand(rng, nregs, lits), rand_operand(rng, nregs, lits))
    if rng.random() < 0.7:
        a_src = (("r", d), a_src[1])
    s_addr = rand_operand(rng, nregs, lits)
    s_val = rand_operand(rng, nregs, lits)
    order_as = rng.random() < 0.5
    exit_cmp = (rng.choice(list(CMPS)), ("r", d), rand_operand(rng, nregs, lits))
    max_num = rng.choice([1, 10, 100, 1000, 3000])
    steps = 0
    while True:  # numerical loop phase
        if shape == "AS-L":
            if order_as:
                regs[d] = OPS[op](operand(regs, a_src[0]), operand(regs, a_src[1]))
                a = operand(regs, s_addr); mem[a] = operand(regs, s_val); written.add(a)
            else:
                a = operand(regs, s_addr); mem[a] = operand(regs, s_val); written.add(a)
                regs[d] = OPS[op](operand(regs, a_src[0]), operand(regs, a_src[1]))
        else:
            regs[d] = OPS[op](operand(regs, a_src[0]), operand(regs, a_src[1]))
        steps += 1
        c, x, y = exit_cmp
        if CMPS[c](operand(regs, x), operand(regs, y)) or steps >= max_num:
            break
    F = set(regs[i] for i in range(nregs) if i != d)
    Z = set(regs)
    E = set(mem[a] for a in written if mem[a] != a)
    # LOAD loop phase (C:L or C:LS): LOAD x <- M[addr]; optional STORE; two exit tests
    lx = rng.randrange(nregs)
    laddr = rand_operand(rng, nregs, lits)
    st = (rand_operand(rng, nregs, lits), rand_operand(rng, nregs, lits)) if shape == "A-LS" else None
    t1 = (rng.choice(list(CMPS)), ("r", rng.randrange(nregs)), rand_operand(rng, nregs, lits))
    reads = set()
    for _ in range(rng.choice([10, 100, 2000])):
        a = operand(regs, laddr)
        reads.add(a)
        regs[lx] = mem.get(a, 0)
        if st is not None:
            sa = operand(regs, st[0]); mem[sa] = operand(regs, st[1])
        c, x, y = t1
        if CMPS[c](operand(regs, x), operand(regs, y)):
            break
    V = Z | set(lits) | set(H) | E | {0}
    ok = reads <= V
    eok = (shape != "AS-L") or len(E) <= len(F) + len(lits) + 1
    return ok, eok, len(reads), len(V)


def control_two_numerical_sites():
    """Control outside the 18 classes: a numerical loop with TWO numerical sites
    (e <- d+2; M[d] <- e; d <- e) writes a linked list, and the LOAD loop x <- M[x]
    then reads unboundedly many addresses. Hypothesis (iii) of the phase lemma fails
    here, and the check must report reads outside V."""
    mem = mem_init()
    written = set()
    d, e = 1, 0
    for _ in range(300):
        e = (d + 2) & MASK
        mem[d] = e; written.add(d)
        d = e
    Z = {1, d, e, N, W}
    E = set(mem[a] for a in written if mem[a] != a)
    x = 1
    reads = set()
    for _ in range(1000):
        reads.add(x)
        x = mem.get(x, 0)
        if x == 0:
            break
    V = Z | set(H) | {0}
    print(f"control (two numerical sites, not one of the 18): distinct addresses read={len(reads)}, "
          f"reads outside V={len(reads - V)}, |E|={len(E)}")


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--control":
        control_two_numerical_sites()
        return
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    for shape in ("AS-L", "A-LS"):
        bad = bade = 0
        mx = mxv = 0
        runs = 20000
        for _ in range(runs):
            ok, eok, nr, nv = run(rng, shape)
            bad += not ok
            bade += not eok
            mx = max(mx, nr)
            mxv = max(mxv, nv)
        print(f"{shape}: runs={runs} reads outside V: {bad}  |E| bound violated: {bade}  "
              f"max distinct addresses read={mx}  max |V|={mxv}  (input words L={L})")


if __name__ == "__main__":
    main()
