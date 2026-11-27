"""Variants for five-halves-per-word-is-tight-on-the-single-edit-suite.md.

(1) 2-CNF analogue of the 5/2 suite (test (b)): marked word "  ...  d 0\n ... 4",
    clauses (x4 v x_d) repeated, forcing by 2-clauses; edit 4 -> 5 (one bit).
    Run PAIR on it.
(2) Non-homogeneous base: marked word i carries digit d_i in {6,7,8,9}; all of
    x1,x5..x9 forced false, x4 true; edit 4 -> 5 in word i.  PAIR must fail on the
    base (unequal pairs); the checksum program (immediate S) is correct.
"""
import random
from itertools import product
from pair_scan_suite_calibration import (positions, raw, sat, run, pair_program, checksum_program,
                          words_of)


def two_cnf_suite(width, m, check):
    W = width // 8
    k = positions(width)
    d = 6
    rows = [f"{l} {u} 0\n".encode() for l in (-d, 4, -5) for u in (2, -2)]
    head = f"p cnf 9 {m+1+len(rows)}\n".encode() + b"".join(rows)
    prefix = head + b" " * ((-len(head) - 1) % W) + b"4"
    a = raw(width, k, d, 4, "{d} 0\n")
    b = raw(width, k, d, 5, "{d} 0\n")
    trailer = f" {d} 0\n".encode()
    first = len(prefix) // W
    files = [(prefix + a*m + trailer, True)]
    for i in range(m):
        files.append((prefix + a*i + b + a*(m-1-i) + trailer, False))
    if check:
        for f, ans in files:
            assert sat(f) == ans
            # every clause has exactly two literals
            body = f.split(b"\n", 1)[1].split()
            assert len(body) % 3 == 0 and all(body[j+2] == b"0" for j in range(0, len(body), 3))
    return first, a, files


def mixed_suite(width, m, check, seed=1):
    W = width // 8
    k = positions(width)
    rng = random.Random(seed + m + width)
    digits = [rng.choice((6, 7, 8, 9)) for _ in range(m)]
    rows = [f"{l} {u} {v} 0\n".encode() for l in (-1, -6, -7, -8, -9, 4, -5)
            for u, v in product((2, -2), (3, -3))]
    head = f"p cnf 9 {m+1+len(rows)}\n".encode() + b"".join(rows)
    prefix = head + b" " * ((-len(head) - 1) % W) + b"4"
    A = [raw(width, k, d, 4) for d in digits]
    B = [raw(width, k, d, 5) for d in digits]
    trailer = b" 6 1 0\n"
    first = len(prefix) // W
    files = [(prefix + b"".join(A) + trailer, True)]
    for i in range(m):
        files.append((prefix + b"".join(A[:i]) + B[i] + b"".join(A[i+1:]) + trailer, False))
    if check:
        for f, ans in files:
            assert sat(f) == ans
    S = sum(int.from_bytes(x, "little") for x in A) % (1 << width)
    return first, files, S, len(set(digits))


def main():
    width = 32768
    W = width // 8
    for m in (6, 7, 40, 41, 300, 301):
        first, a, files = two_cnf_suite(width, m, check=(m <= 41))
        prog = pair_program(first)
        for f, ans in files:
            v, s = run(prog, words_of(f, W), width, 10*m + 100)
            assert v == ans
            if ans:
                print(f"2-CNF suite w={width} m={m}: PAIR correct on {len(files)} files, "
                      f"base steps {s} (5m/2={5*m/2})")
    for m in (6, 7, 40, 41, 300, 301):
        first, files, S, nd = mixed_suite(width, m, check=(m <= 41))
        prog = pair_program(first)
        wrong = sum(run(prog, words_of(f, W), width, 10*m + 100)[0] != ans for f, ans in files)
        cp = checksum_program(first, m, S, 4)
        for f, ans in files:
            v, s = run(cp, words_of(f, W), width, 10*m + 100)
            assert v == ans
            if ans:
                base = s
        print(f"mixed base w={width} m={m} ({nd} distinct marked words): PAIR wrong on "
              f"{wrong}/{len(files)} files; CHECKSUM(k=4) correct on all, base steps {base} "
              f"(3m+m/4={3*m+m/4:.1f})")


if __name__ == "__main__":
    main()


def pair_not_globally_correct():
    """PAIR is suite-correct only: replace BOTH words of one pair by B."""
    from pair_scan_suite_calibration import layout
    width = 32768
    W = width // 8
    for m in (6, 7, 40):
        prefix, a, b, trailer, ell, d = layout(width, m)
        first = len(prefix) // W
        f = prefix + b + b + a*(m-2) + trailer          # words 1 and 2 = a pair
        ans = sat(f)
        v, s = run(pair_program(first), words_of(f, W), width, 10*m + 100)
        print(f"two-edit file (pair 1,2 both B) w={width} m={m}: sat={ans}, PAIR verdict={v}"
              f" -> {'PAIR WRONG (expected: suite-correct only)' if v != ans else 'ok'}")
    # m = 1 boundary: PAIR needs m >= 2
    m = 1
    prefix, a, b, trailer, ell, d = layout(width, m)
    first = len(prefix) // W
    for f, name in ((prefix + a + trailer, "base"), (prefix + b + trailer, "edit")):
        v, s = run(pair_program(first), words_of(f, W), width, 100)
        print(f"m=1 {name}: sat={sat(f)}, PAIR verdict={v}")


if __name__ == "__main__":
    pair_not_globally_correct()
