#!/usr/bin/env python3
"""Finite check of the factored round rule for RAM visits with single-cell blocks.

Toy RAM: M memory cells holding values mod V, registers r0, r1 (mod V), a random
program over {LOAD r0<-mem[r1%M], STORE mem[r1%M]<-r0, ADDI k, MOV r1<-r0,
SWAP, JNZ target, HALT}. Cap T steps.

Raw controller z = (pc, r0, r1, tau, flag), flag 0 running / 1 halted / 2 timeout.
sel(z): block (= cell) of the next memory access from z, found by running the
register-only instructions first; the designated cell 0 if the run halts or times
out before any memory access, or if z is terminal.
Visit(z, v): from z, with cell sel(z) holding v, run until the next memory access
to a different cell (that instruction starts the next visit), halt or cap.
Register-only stretches are folded into the visit, so every controller selects
exactly one block.

For epochs of L = k^2 visits in k rounds of k, and the semantic prefix H of round
j, enumerate EVERY raw k-controller suffix Y and evaluate the product over all
cells i of the replay flag P_{Y,i}(H, A_i), each computed from cell i's
epoch-start value alone (Lemma "local replay" of the two-fifths preprint).
Claim checked: exactly one Y passes, and it is the true continuation.
"""
import itertools
import random
import sys

M, V, T, K = 2, 2, 12, 2          # cells, value range, cap, round length k
L = K * K                         # visits per epoch
OPS = ["LOAD", "STORE", "ADDI", "MOV", "SWAP", "JNZ", "HALT"]


def rand_program(rng, P):
    prog = []
    for _ in range(P - 1):
        op = rng.choice(OPS[:-1])
        arg = rng.randrange(V) if op == "ADDI" else (rng.randrange(P) if op == "JNZ" else 0)
        prog.append((op, arg))
    prog.append(("HALT", 0))
    return prog


def step_regs(prog, pc, r0, r1):
    """Execute a register-only instruction; return new (pc, r0, r1)."""
    op, arg = prog[pc]
    if op == "ADDI":
        return pc + 1, (r0 + arg) % V, r1
    if op == "MOV":
        return pc + 1, r0, r0
    if op == "SWAP":
        return pc + 1, r1, r0
    if op == "JNZ":
        return (arg if r0 != 0 else pc + 1), r0, r1
    raise ValueError(op)


def make_tables(prog):
    P = len(prog)
    raw = [(pc, r0, r1, tau, fl) for pc in range(P) for r0 in range(V) for r1 in range(V)
           for tau in range(T + 1) for fl in range(3)]

    def sel(z):
        pc, r0, r1, tau, fl = z
        if fl != 0:
            return 0
        while tau < T:
            op, _ = prog[pc]
            if op == "HALT":
                return 0
            if op in ("LOAD", "STORE"):
                return r1 % M
            pc, r0, r1 = step_regs(prog, pc, r0, r1)
            tau += 1
        return 0

    def visit(z, v):
        pc, r0, r1, tau, fl = z
        if fl != 0:
            return z, v
        i = sel(z)
        while True:
            if tau >= T:
                return (pc, r0, r1, T, 2), v
            op, _ = prog[pc]
            if op == "HALT":
                return (pc, r0, r1, tau, 1), v
            if op in ("LOAD", "STORE"):
                a = r1 % M
                if a != i:
                    return (pc, r0, r1, tau, 0), v
                if op == "LOAD":
                    r0 = v
                else:
                    v = r0
                pc += 1
            else:
                pc, r0, r1 = step_regs(prog, pc, r0, r1)
            tau += 1

    sel_t = {z: sel(z) for z in raw}
    vis_t = {(z, v): visit(z, v) for z in raw for v in range(V)}
    return raw, sel_t, vis_t


def reference(sel_t, vis_t, mem0, nvis):
    z = (0, 0, 0, 0, 0)
    mem = list(mem0)
    ctrls, mems = [z], [tuple(mem)]
    for _ in range(nvis):
        i = sel_t[z]
        z, mem[i] = vis_t[(z, mem[i])]
        ctrls.append(z)
        mems.append(tuple(mem))
    return ctrls, mems


def replay_flag(sel_t, vis_t, Z, i, v):
    ok = True
    for t in range(1, len(Z)):
        if sel_t[Z[t - 1]] == i:
            out, v = vis_t[(Z[t - 1], v)]
            ok = ok and (out == Z[t])     # continue the scan after a failed check
    return ok


def main():
    nprog = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    rng = random.Random(20261127)
    total_checks = 0
    p, tried, seen = 0, 0, set()
    while p < nprog:
        tried += 1
        prog = rand_program(rng, 6)
        raw, sel_t, vis_t = make_tables(prog)
        mem0 = [rng.randrange(V) for _ in range(M)]
        ctrls, mems = reference(sel_t, vis_t, mem0, 2 * L)
        # keep only distinct programs whose runs have >= 4 genuine (running) visits touching both cells
        live = [t for t in range(2 * L) if ctrls[t][4] == 0]
        cells = {sel_t[ctrls[t]] for t in live}
        if len(live) < 4 or len(cells) < 2 or tuple(prog) in seen:
            continue
        seen.add(tuple(prog))
        for e in range(2):
            A = mems[e * L]
            for j in range(K):
                H = ctrls[e * L: e * L + j * K + 1]
                truth = tuple(ctrls[e * L + j * K + 1: e * L + (j + 1) * K + 1])
                passing = []
                for Y in itertools.product(raw, repeat=K):
                    Z = H + list(Y)
                    if all(replay_flag(sel_t, vis_t, Z, i, A[i]) for i in range(M)):
                        passing.append(Y)
                total_checks += 1
                status = "OK" if (len(passing) == 1 and passing[0] == truth) else "FAIL"
                print(f"prog {p} {prog} epoch {e} round {j}: |raw|^k={len(raw)**K} passing={len(passing)} {status}")
        print(f"  prog {p}: live visits={len(live)} cells={sorted(cells)} controllers={ctrls}")
        p += 1
    print(f"programs tried={tried} kept={nprog} checks={total_checks}")


if __name__ == "__main__":
    main()
