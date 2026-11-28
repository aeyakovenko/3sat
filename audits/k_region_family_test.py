#!/usr/bin/env python3
"""k-region equality family in the word-aligned layout of the journal's equality files
(notes/communication-bound-for-public-crossed-scans.md): k regions, each pinning the same m
variables x_1..x_m (four clauses (l_i, +-u, +-v) per pin), region r in its own order pi_r.
SAT iff all k regions pin every x_i the same way.  Checked against CaDiCaL on the parsed clauses.
Usage: python3 -B k_region_family_test.py [PROG.asm ORDER(chain|shuffled) [SEED] [COUNT]]
(no arguments: k_region_pin_table.asm shuffled with seed 4 and 54 files, about 1 s)"""
import sys, random, math
sys.dont_write_bytecode = True
import five_slot_ram_interpreter as I
import equality_file_generator as G

def build(N, w, k, m, orders, bits):
    W = w // 8
    K = math.ceil(math.log2(m + 3))
    def name(j):
        return '1' + ''.join('0' * (W - 1) + b for b in format(j, '0%db' % K))
    u, v = m + 1, m + 2
    V = name(2 ** K - 1)
    header = 'p cnf %s %d\n' % (V, 4 * m * k)
    header += ' ' * ((-len(header)) % W)
    lit = lambda j, neg: ' ' * (W - 2) + ('-' if neg else ' ') + name(j)
    endc = ' 0\n' + ' ' * (W - 3)
    body = header
    for r in range(k):
        for i in orders[r]:
            for su in (False, True):
                for sv in (False, True):
                    body += lit(i, bits[r][i - 1] == 0) + lit(u, su) + lit(v, sv) + endc
    total = N // 8
    if len(body) + 2 * W + 1 > total:
        return None
    body += ' ' * (total - len(body) - 1) + '\n'
    return dict(data=body.encode('ascii'), w=w, N=N)

def main():
    args = sys.argv[1:] or ['k_region_pin_table.asm', 'shuffled', '4', '54']
    prog_name = args[0]
    prog = I.parse(open(prog_name).read())
    order = args[1]
    seed = int(args[2]) if len(args) > 2 else 1
    count = int(args[3]) if len(args) > 3 else 60
    rng = random.Random(seed)
    ok = bad = 0
    worst = {}
    for t in range(count):
        k = 2 + t % 9                      # 2..10 regions
        m = rng.choice([3, 5, 8, 13, 21])
        w = rng.choice([32, 32, 48, 64])
        orders = [list(range(1, m + 1)) for _ in range(k)]
        if order == 'shuffled':
            for o in orders:
                rng.shuffle(o)
        base = [rng.randrange(2) for _ in range(m)]
        bits = [list(base) for _ in range(k)]
        mode = t % 3
        if mode == 1:
            bits[rng.randrange(k)][rng.randrange(m)] ^= 1
        elif mode == 2:
            bits = [[rng.randrange(2) for _ in range(m)] for _ in range(k)]
        N = 8 * 64
        f = None
        while f is None:
            N *= 2
            f = build(N, w, k, m, orders, bits)
        N = 2 * N                           # leave real padding (half the file)
        f = build(N, w, k, m, orders, bits)
        truth_expected = all(b == bits[0] for b in bits)
        cl = G.validate(dict(data=f['data']))
        truth = G.cadical_sat(cl)
        assert truth == truth_expected
        verdict, steps = I.run(prog, f['data'], w=w, max_steps=100 * N)
        good = verdict == ('YES' if truth else 'NO')
        ok += good; bad += not good
        if not good:
            print('MISMATCH k=%d m=%d w=%d truth=%s verdict=%s' % (k, m, w, truth, verdict))
        worst[k] = max(worst.get(k, 0), steps / N)
    print('prog=%s order=%s files=%d correct=%d wrong=%d' % (prog_name, order, ok + bad, ok, bad))
    print('max steps/N by number of regions k:', {kk: round(r, 4) for kk, r in sorted(worst.items())})

if __name__ == '__main__':
    main()
