"""Finite-size illustration of the shrink step in compact-compilers-and-linear-sat-time.md
at SAT exponent a = -1 (packed-scan SAT time N/log N), versus a = 0.

Cap from the note (dominant term only; payload term u*L^b is lower order while t >> n polylog n):
    h ~ K * (M / log2(2+M)) * L**a,   L = ceil(log2(s+2)),  s ~ t.
Compiler output modelled as M = c * s * log2(s)**beta.
Prints the ratio h/t; the shrink step needs h/t <= 1/2 for every round.
This is arithmetic only: it does not check that the verifier can emit the failure test in
O(W/log W) word steps, which a = -1 additionally requires (see
moving-the-milestone-to-nlin-versus-dlin-removes-no-barrier.md, Section 4).
"""
import math

def ratio(s, beta, a, c=1.0, K=1.0):
    L = math.ceil(math.log2(s + 2))
    M = c * s * math.log2(s) ** beta
    h = K * (M / math.log2(2 + M)) * L ** a
    return h / s

def eventual_threshold(beta, a, c=1.0, K=1.0):
    """Asymptotically h/t ~ K*c*log2(s)**(beta-1+a); it stays <= 1/2 once
    log2(s) >= (2*K*c)**(1/(1-a-beta)) (requires beta < 1-a). Returns that log2(s)."""
    gap = 1 - a - beta
    return (2 * K * c) ** (1.0 / gap)

if __name__ == '__main__':
    print('ratio h/t at s = 2^e (c = K = 1)')
    for a in (0, -1):
        for beta in ((0.5, 0.9, 1.0) if a == 0 else (1.5, 1.9, 2.0)):
            row = ['%.3f' % ratio(2.0 ** e, beta, a) for e in (20, 40, 64, 128, 512)]
            print('a=%2d beta=%.1f  e=20,40,64,128,512 :' % (a, beta), ' '.join(row))
    print('eventual threshold log2(s) beyond which h/t <= 1/2 (leading-order asymptotics; c = 1)')
    for a, beta in ((0, 0.9), (-1, 1.9), (-1, 1.5)):
        print('a=%2d beta=%.1f :' % (a, beta), ' '.join('K=%d: %.3g' % (K, eventual_threshold(beta, a, 1.0, K)) for K in (1, 4, 16)))
    print('beta = 2 at a = -1 (c = 1): ratio tends to K*c, so halving needs K*c < 1/2:')
    for e in (64, 1000, 10**6):
        L = e; Mlog = e + 2 * math.log2(e)
        print('  e=%d  ratio/K = %.4f' % (e, e ** 2 / Mlog / L))
