"""Exact integer schedule checks and a complete small adaptive relay audit."""
from itertools import product


def ceil_log(value):
    return (value - 1).bit_length()


def schedule(b, count_factor, extra, leaf_guess_factor):
    # Actual lengths are 2**v; only their exponents v need to be stored.
    B = 1 << b
    depth = B // (32 * count_factor * b)
    v = b
    track = log_paths = gate_ratio_failures = 0
    for _ in range(depth):
        ell = max(1, ceil_log(v + 1))
        step = extra + ceil_log(ell)
        new = v + step
        bound = count_factor * ceil_log(new + 1)
        track += bound
        log_paths += ceil_log(bound)
        gate_ratio_failures += bound * 4 > 1 << step
        v = new
    leaf_guess = leaf_guess_factor * (B // b + 1)
    assert track + b <= B
    assert v > leaf_guess + log_paths + 4 * b
    assert not gate_ratio_failures
    return depth, track, v - log_paths - leaf_guess


def small_games():
    policies = ({1,2,3}, {1,2}, {1,3}, {1})
    checked = 0
    for P in policies:
        # A different postprocessing bit per reachable leaf, so the last
        # oracle answer need not equal the verdict.
        leaves = {2*i+j for i in P for j in (0,1)} - P
        for output_bits in product((0,1), repeat=len(leaves)):
            post = dict(zip(sorted(leaves), output_bits))
            def gate(get):
                q=1
                while q in P:
                    q=2*q+get(q)
                return post[q]
            for table in product((0,1),repeat=len(P)**2):
                grid=dict(zip(product(sorted(P),repeat=2),table))
                explicit = {i:gate(lambda j:grid[i,j]) for i in P}
                visited = []
                def asked(i):
                    def get(j):
                        visited.append((i,j))
                        return grid[i,j]
                    return gate(get)
                root = gate(asked)
                assert root == gate(explicit.get)
                assert len(visited) <= 4
                checked += 1
    return checked


def main():
    cases=[]
    # Use different bases and independent time/guess constants. c is fixed
    # within each family; it is intentionally large compared with G/L.
    for C in (1,2,3):
        for g in (1,2):
            c=96*C*(g+1)+ceil_log(C)+4
            for b in (14,17,20):
                cases.append(schedule(b,C,c,g))
    print('integer schedules:',len(cases),
          'minimum endpoint exponent slack after leaf guesses:',min(x[2] for x in cases))
    print('adaptive trees and small leaf tables:',small_games())


if __name__ == '__main__':
    main()
