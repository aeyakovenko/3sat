#!/usr/bin/env python3
"""Numbers for the oracle with existential-only wrappers of
notes/a-relativization-barrier-for-the-square-root-floor.md.
Run: python3 existential_wrapper_oracle_parity_bounds.py   (about 8 s)

Part A  lower-bound inequality (scale induction, Section 2 of the note).
        For a deterministic oracle RAM whose memory never holds more than B0
        one-bits and which makes q <= B0 queries, Section 2 shows: if it
        computes parity of the 2^n raw bits R^{=n} for every setting of them,
        then n < Phi(B0), where
          lambda_i = (pi+1) * rho^i,  rho = pi^2/(pi+1)     (length scales)
          m        = least i with lambda_i >= (pi+1)/pi * B0 (top scale)
          D_0 = 1, D_i = floor(lambda_i) + i + 2             (tree depths)
          W_i = (lambda_i/pi) * D_{i-1}                      (DNF widths)
          Phi(B0) = sum_{i=1..m} log2(10 W_i) + log2(max(8, 2(q D_m + 1))).
        We print x*(n) = the largest log2(B0) with Phi(B0) <= n.  Every
        machine with log2(B0) <= x*(n) therefore FAILS to compute parity
        (x* is the failure threshold, found by bisection to ~1e-10), and we
        compare x*(n) with sqrt(n log2 rho).
Part B  relative upper bound: the XOR-splitting recursion of Section 4 run
        with one nondeterministic wrapper per quantifier block, per-wrapper
        cost factor pi*c (c = words written per step), minimised over the
        block size s; compared with 2 sqrt(n log2 K), K = (pi c)^2.
Part C  brute-force exactness of the XOR-splitting game for small n.
"""
import math, itertools, random, sys


def phi(log2B0, pi=4.0):
    """Upper end of the necessary condition n < Phi(B0); q = B0."""
    # All quantities in log2 to avoid overflow.  D_i = floor(lambda_i)+i+2 is
    # bounded above by lambda_i + i + 2, which is what we use (upper bound on
    # Phi, hence a valid, slightly weaker threshold).
    rho = pi * pi / (pi + 1.0)
    lam0 = pi + 1.0
    top = math.log2((pi + 1.0) / pi) + log2B0          # log2 of (pi+1)/pi * B0
    total = 0.0
    log2D_prev = 0.0                                    # D_0 = 1
    i = 0
    while True:
        i += 1
        log2lam = math.log2(lam0) + i * math.log2(rho)
        log2W = log2lam - math.log2(pi) + log2D_prev
        total += math.log2(10.0) + log2W
        # log2(lambda_i + i + 2) = log2lam + log2(1 + (i+2)/lambda_i)
        log2D_prev = log2lam + math.log2(1.0 + (i + 2) * 2.0 ** (-log2lam))
        if log2lam >= top:
            break
    m = i
    log2q = log2B0
    e = log2q + log2D_prev                              # log2(q * D_m)
    tail = max(3.0, 1.0 + e + math.log2(1.0 + 2.0 ** (-e)))
    return total + tail, m


def xstar(n, pi=4.0):
    """Largest log2(B0) with Phi(B0) <= n (Phi is increasing in B0): every
    machine with one-bit budget B0 <= 2^xstar fails to compute parity."""
    lo, hi = 1.0, 4.0 * math.sqrt(n) + 50
    for _ in range(200):
        mid = (lo + hi) / 2
        if phi(mid, pi)[0] > n:
            hi = mid
        else:
            lo = mid
    return lo


def upper_log2_time(n, pi=4.0, c=1.0):
    """log2 of the deterministic time of the nested-wrapper parity algorithm,
    minimised over block size s.  Cost of writing a wrapper for a program with
    input X bits and budget t at width w:  ~ pi*c*(t+2) + (2*pi+1)*X/w + 8."""
    # The per-level recursion is affine: with
    #   tau_2 = s + tau_D(i) + n/w + 4                 (guess y, run D(i))
    #   tau_1 = 2*2^s/w + cost(X2, tau_2) + 1          (guess v, write W')
    #   tau_D(i-1) = cost(X1, tau_1) + 1               (write W, query)
    #   cost(X, t) = pi*c*(t+2) + (2*pi+1)*X/w + 8,  X2 = n+2^s+4w, X1 = n+4w
    # one gets tau_D(i-1) = a*tau_D(i) + b with a = (pi c)^2 and
    #   b = a(s+n/w+6) + pi c (2*2^s/w + (2pi+1) X2/w + 11) + (2pi+1) X1/w + 9,
    # so tau_D(0) = a^k tau_D(k) + b (a^k-1)/(a-1), tau_D(k) = n/w + 2.
    # Everything is evaluated in log2 (2^s overflows floats).
    def lse(*xs):
        mx = max(xs)
        return mx + math.log2(sum(2.0 ** (x - mx) for x in xs))
    a = (pi * c) ** 2
    la = math.log2(a)
    best = None
    smax = int(4 * math.sqrt(n * la)) + 10
    for s in range(1, min(n, smax) + 1):
        k = -(-n // s)
        w = max(8.0, 2.0 * (s + k * la))      # word width Theta(log T)
        small = a * (s + n / w + 6) + pi * c * ((2 * pi + 1) * (n + 4 * w) / w + 11) \
            + (2 * pi + 1) * (n + 4 * w) / w + 9
        l_big = math.log2(pi * c * (2 + (2 * pi + 1))) + s - math.log2(w)
        lb = lse(math.log2(small), l_big)
        ltk = math.log2(n / w + 2)
        val = k * la + lse(ltk, lb - math.log2(a - 1))
        if best is None or val < best[0]:
            best = (val, s, k)
    return best


def game_check(n, s_list, trials, seed=1):
    """XOR-splitting game: P_{i-1}(rho,b) <=> exists v in {0,1}^{2^s}
    (xor v = b and forall y P_i(rho y, v_y)); P_k(rho,b) <=> R(rho) = b.
    Check by brute force that exactly one root claim b is accepted and that it
    equals the parity of R."""
    rng = random.Random(seed)
    bad = 0
    checked = 0
    for s in s_list:
        blocks = []
        rem = n
        while rem > 0:
            blocks.append(min(s, rem))
            rem -= blocks[-1]
        for _ in range(trials):
            R = [rng.randrange(2) for _ in range(2 ** n)]

            def P(level, prefix, plen, b):
                if level == len(blocks):
                    return R[prefix] == b
                sz = blocks[level]
                for v in itertools.product((0, 1), repeat=2 ** sz):
                    if sum(v) % 2 != b:
                        continue
                    if all(P(level + 1, (prefix << sz) | y, plen + sz, v[y])
                           for y in range(2 ** sz)):
                        return True
                return False

            acc = [b for b in (0, 1) if P(0, 0, 0, b)]
            checked += 1
            if acc != [sum(R) % 2]:
                bad += 1
    return checked, bad


def main():
    print("Part A: failure threshold x*(n) = max log2(B0) with Phi(B0) <= n; every machine with log2(B0) <= x*(n) fails (pi = padding factor)")
    print("A   pi      n        x*(n)   sqrt(n log2 rho)   x*/sqrt(n)   sqrt(log2 rho)")
    for pi in (4.0, 16.0):
        rho = pi * pi / (pi + 1)
        for n in (10**3, 10**4, 10**5, 10**6, 10**7, 10**8):
            x = xstar(n, pi)
            print("A %4.0f %9d %10.1f %14.1f %14.4f %14.4f" % (
                pi, n, x, math.sqrt(n * math.log2(rho)), x / math.sqrt(n),
                math.sqrt(math.log2(rho))))
    print()
    print("Part B: relative upper bound, nested existential wrappers, two per XOR level")
    print("B   pi  c      n     log2 T   s*    k*   log2T/sqrt(n)   2sqrt(log2 K)   log2T(upper)/x*(n)")
    for (pi, c) in ((4.0, 1.0), (4.0, 2.0), (16.0, 1.0)):
        for n in (10**3, 10**4, 10**5, 10**6, 10**7, 10**8):
            val, s, k = upper_log2_time(n, pi, c)
            K = (pi * c) ** 2
            x = xstar(n, pi)
            print("B %4.0f %2.0f %9d %9.1f %5d %5d %12.4f %14.4f %12.3f" % (
                pi, c, n, val, s, k, val / math.sqrt(n), 2 * math.sqrt(math.log2(K)), val / x))
    print()
    print("Part C: XOR-splitting game exactness (brute force over all messages)")
    for n, s_list, trials in ((4, (1, 2, 3, 4), 20), (6, (1, 2, 3), 10), (8, (2, 3), 3)):
        checked, bad = game_check(n, s_list, trials, seed=n)
        print("C n=%d s in %s: instances=%d mismatches=%d" % (n, s_list, checked, bad))


if __name__ == "__main__":
    main()
