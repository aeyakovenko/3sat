#!/usr/bin/env python3
"""Finite checks for the RAM -> exact network simulation threshold of
simulating-a-ram-step-by-exact-networks.md.

Check A (memory histories).  For every history of T events (op in {R,W}, addr in
[A], val in [V]) with zero initial memory, enumerate ALL hidden index sequences
I in [T]^T (the gather witness of batched-last-writers-...md, line 69).  A
witness is accepted iff the gathered (addr, time) pairs increase strictly and,
along each same-address run, every read equals the carried value (reset to the
initial value at each run start, overwritten by writes).  Claim checked:
#accepting witnesses == [history is legal]  (so the summed network is exact).

Check B (toy RAM with indirect loads/stores, input in memory).  Program:
    x = M[0]; repeat K times: { y = M[x]; M[(x+1) % A] = y; x = (y + 1) % A }
    output x.
The full witness is (claimed values of all reads) x (hidden order I in [T]^T).
Local transitions are checked by re-running the program on the claimed reads;
memory consistency by the gather check with initial values = input.  Claim
checked: exactly one accepting witness per input, and its output equals the
direct run.

Check C (gate-count line).  Batcher odd-even mergesort comparator count on
n = 2^k records versus n*k: the ratio grows like k/4, so Batcher costs
T*w^3 gates on w-bit records; the exponent 2 needs AKS (O(n log n) comparators,
astronomically large constant).
"""
import itertools
import sys


def accepts(hist, I, init):
    """hist: list of (op, addr, val); I: tuple of indices; init: dict addr->val."""
    prev = None
    carried = None
    for idx in I:
        op, a, v = hist[idx]
        key = (a, idx)
        if prev is not None and not (key > prev):
            return False
        if prev is None or a != prev[0]:
            carried = init.get(a, 0)
        if op == 'R':
            if v != carried:
                return False
        else:
            carried = v
        prev = key
    return True


def legal(hist, init):
    mem = dict(init)
    for op, a, v in hist:
        if op == 'R':
            if mem.get(a, 0) != v:
                return False
        else:
            mem[a] = v
    return True


def check_A(T, A, V):
    events = [(op, a, v) for op in 'RW' for a in range(A) for v in range(V)]
    n_hist = n_legal = bad = 0
    total_witness_checks = 0
    for hist in itertools.product(events, repeat=T):
        cnt = 0
        for I in itertools.product(range(T), repeat=T):
            total_witness_checks += 1
            if accepts(hist, I, {}):
                cnt += 1
        lg = legal(hist, {})
        n_hist += 1
        n_legal += lg
        if cnt != (1 if lg else 0):
            bad += 1
    return n_hist, n_legal, total_witness_checks, bad


def run_program(inp, A, K, reads=None):
    """Run the toy RAM.  If reads is given, use those claimed read values
    instead of memory (this is the local-transition check of a claimed trace).
    Returns (history, output)."""
    mem = {i: inp[i] for i in range(A)}
    hist = []
    r = iter(reads) if reads is not None else None

    def load(addr):
        v = next(r) if r is not None else mem[addr]
        hist.append(('R', addr, v))
        return v

    def store(addr, v):
        if r is None:
            mem[addr] = v
        hist.append(('W', addr, v))

    x = load(0) % A
    for _ in range(K):
        y = load(x)
        store((x + 1) % A, y)
        x = (y + 1) % A
    return hist, x


def check_B(A, V, K):
    n_reads = 1 + K
    T = 1 + 2 * K
    inputs = list(itertools.product(range(V), repeat=A))
    bad = 0
    checks = 0
    for inp in inputs:
        init = {i: inp[i] for i in range(A)}
        _, true_out = run_program(inp, A, K)
        acc = []
        for reads in itertools.product(range(V), repeat=n_reads):
            hist, out = run_program(inp, A, K, reads=reads)
            assert len(hist) == T
            for I in itertools.product(range(T), repeat=T):
                checks += 1
                if accepts(hist, I, init):
                    acc.append((reads, I, out))
        if len(acc) != 1 or acc[0][2] != true_out:
            bad += 1
    return len(inputs), T, checks, bad


def batcher_comparators(k):
    # odd-even mergesort on n = 2^k inputs: (k^2 - k + 4) * 2^(k-2) - 1
    return (k * k - k + 4) * 2 ** (k - 2) - 1


def main():
    print("Check A: memory histories, all hidden index sequences I in [T]^T")
    for (T, A, V) in [(1, 2, 2), (2, 2, 2), (3, 2, 2), (4, 2, 2), (3, 3, 2)]:
        n_hist, n_legal, checks, bad = check_A(T, A, V)
        print(f"  T={T} A={A} V={V}: histories={n_hist} legal={n_legal} "
              f"witness_checks={checks} mismatches={bad}")
    print("Check B: toy RAM with indirect load/store, full witness enumeration")
    for (A, V, K) in [(3, 3, 1), (3, 3, 2), (4, 4, 1), (4, 2, 2)]:
        n_in, T, checks, bad = check_B(A, V, K)
        print(f"  A={A} V={V} K={K} (T={T} events): inputs={n_in} "
              f"witness_checks={checks} inputs_without_exactly_one_correct_witness={bad}")
    print("Check C: Batcher odd-even mergesort comparators / (n*log2 n)")
    for k in (10, 20, 30, 40):
        n = 2 ** k
        c = batcher_comparators(k)
        print(f"  k={k}: comparators={c} ratio_to_nlogn={c / (n * k):.3f} (k/4={k / 4:.2f})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
