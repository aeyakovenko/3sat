"""Constructive test for five-halves-per-word-is-tight-on-the-single-edit-suite.md:
program families with o(m) stored instructions on the
5/2 suite (base + m single-word B' edits + m one-bit B edits), looking for a
deadline K*m with K < 5/2.  Mechanisms tried: loop unrolling
and shared address updates.  Reuses the suite, RAM and PAIR from pair_scan_suite_calibration.py.

UNROLL(k):  PAIR loop body repeated k times per iteration (k-1 exit branches,
            last compare is the back-edge).
SHARED(k):  k pointer registers p_t = first+t, one load each, k/2 pair compares,
            then all k pointers advanced by k (shared stride).
Both use PAIR's exit test (accept iff the first unequal pair is the end pair).
"""
import sys
from pair_scan_suite_calibration import suite, run, assemble, pair_program, words_of, R, I

EXIT = [
    ('EXIT', ('beq', R('v'), I(0), 'ACC')),
    (None, ('add', 'q', R('p'), I(1))),
    (None, ('load', 'z', R('q'))),
    (None, ('bne', R('z'), I(0), 'REJ')),
    (None, ('beq', R('u'), R('x1'), 'ACC')),
    ('REJ', ('rej',)),
    ('ACC', ('acc',)),
]


def unroll_program(first, k):
    L = [(None, ('load', 'x1', I(first)))]
    if first - 1:
        L.append((None, ('mov', 'p', I(first - 1))))
    for t in range(k):
        L.append(('loop' if t == 0 else None, ('add', 'p', R('p'), I(1))))
        L.append((None, ('load', 'u', R('p'))))
        L.append((None, ('add', 'p', R('p'), I(1))))
        L.append((None, ('load', 'v', R('p'))))
        if t < k - 1:
            L.append((None, ('bne', R('u'), R('v'), 'EXIT')))
        else:
            L.append((None, ('beq', R('u'), R('v'), 'loop')))
    L.append((None, ('beq', R('u'), R('u'), 'EXIT')))
    return assemble(L + EXIT)


def shared_program(first, k):
    assert k % 2 == 0
    L = [(None, ('load', 'x1', I(first)))]
    for t in range(k):
        L.append((None, ('mov', f'p{t}', I(first + t))))
    L.append(('loop', ('load', 'u0', R('p0'))))
    for t in range(1, k):
        L.append((None, ('load', f'u{t}', R(f'p{t}'))))
    for t in range(0, k - 2, 2):                  # early pairs exit before updates
        L.append((None, ('bne', R(f'u{t}'), R(f'u{t+1}'), f'X{t}')))
    for t in range(k):
        L.append((None, ('add', f'p{t}', R(f'p{t}'), I(k))))
    L.append((None, ('beq', R(f'u{k-2}'), R(f'u{k-1}'), 'loop')))
    # last pair failed after the shared update: undo the stride for its pointer
    L.append((None, ('mov', 'u', R(f'u{k-2}'))))
    L.append((None, ('mov', 'v', R(f'u{k-1}'))))
    L.append((None, ('sub', 'p', R(f'p{k-1}'), I(k))))
    L.append((None, ('beq', R('u'), R('u'), 'EXIT')))
    for t in range(0, k - 2, 2):
        L.append((f'X{t}', ('mov', 'u', R(f'u{t}'))))
        L.append((None, ('mov', 'v', R(f'u{t+1}'))))
        L.append((None, ('mov', 'p', R(f'p{t+1}'))))
        L.append((None, ('beq', R('u'), R('u'), 'EXIT')))
    return assemble(L + EXIT)


def main():
    ms = [int(x) for x in sys.argv[1:]] or [6, 7, 40, 41, 120, 121, 300, 301]
    for width in (32768, 49152):
        for m in ms:
            first, a, files = suite(width, m, check_sat=(m <= 41))
            W = len(a)
            mem = [(words_of(f, W), ans) for f, ans in files]
            row = [f"w={width} m={m} files={len(files)}"]
            progs = [("PAIR", pair_program(first))]
            progs += [(f"UNROLL{k}", unroll_program(first, k)) for k in (2, 4, 8)]
            progs += [(f"SHARED{k}", shared_program(first, k)) for k in (2, 4, 8)]
            for name, prog in progs:
                base = None
                for words, ans in mem:
                    v, s = run(prog, words, width, 10*m + 200)
                    assert v == ans, (name, width, m, ans, v)
                    if ans:
                        base = s
                row.append(f"{name}(C={len(prog)}) T={base} T-5m/2={base-2.5*m:+.1f}")
            print(" | ".join(row))
    print("every program correct on every suite file; no family below 5m/2")


if __name__ == "__main__":
    main()
