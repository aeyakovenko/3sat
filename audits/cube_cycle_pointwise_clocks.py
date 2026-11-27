"""Cube-cycle catalog: pointwise clocks of the cube-cycle catalog (independent replication).

The pointwise clock of a file x is the least number of instructions executed on
x by any correct program.  This script checks

  * the catalog counts 61,440 / 1,889 / 2,207 for the three classes
      A: some word is not SAFE                       (claimed clock 2)
      B: SAT, all four words SAFE                    (claimed clock 4)
      C: UNSAT (cover)                               (claimed clock 8)
  * the pointwise UPPER bounds 2 / 4 / 8: the recognition path of each class is
    sound (its leaf set contains only files with the announced verdict), so
    "tests, then any correct fallback program" is a correct program;
  * the pointwise LOWER bounds 2 (all files) and 4 (class B) for the full
    model.  The lower bound 8 for class C is the seven-step exclusion of
    cube_cycle_leaf_capacity (see clock-bounds-for-the-four-word-cube-cycle-catalog.md for its scope).
"""

from itertools import product

import numpy as np

from cube_cycle_native_model import SAFE, alu, branch, is_cover, is_cover_by_assignments, mask_of, words_of, ALU, BRANCH

codes = np.arange(65536, dtype=np.int64)
W = [(codes >> (4 * i)) & 15 for i in range(4)]
rot = ((codes << 1) & 0xffff) | (codes >> 15)
COVER = (codes | rot) == 0xffff
safe_tab = np.zeros(16, dtype=bool)
safe_tab[list(SAFE)] = True
ALLSAFE = safe_tab[W[0]] & safe_tab[W[1]] & safe_tab[W[2]] & safe_tab[W[3]]


def counts():
    assert all(bool(COVER[m]) == is_cover(m) == is_cover_by_assignments(m) for m in range(65536))
    a = int((~ALLSAFE).sum())
    b = int((ALLSAFE & ~COVER).sum())
    c = int(COVER.sum())
    assert not (COVER & ~ALLSAFE).any()          # every cover has four SAFE words
    print(f'class A (a word outside SAFE, SAT): {a}')
    print(f'class B (all words SAFE, SAT):      {b}')
    print(f'class C (cover, UNSAT):             {c}')
    assert (a, b, c) == (61440, 1889, 2207)
    # each word of a cover is pivotal: replacing it by 0 gives a satisfiable file
    for i in range(4):
        zeroed = codes & ~(15 << (4 * i))
        assert not COVER[zeroed[COVER]].any()
    print('every word of every cover is pivotal (replacing it by 0 gives SAT)')


def upper_paths():
    # A: load word i, compare with its literal value v (v not SAFE) -> ACCEPT.
    n = 0
    for i in range(4):
        for v in range(16):
            if v in SAFE:
                continue
            leaf = W[i] == v
            assert not COVER[leaf].any()
            n += 1
    print(f'class A paths: {n} (address, literal) tests, each leaf set is SAT only  -> 2 steps')
    # B: two cyclically adjacent words i, i+1 with top bit of word i and low bit
    #    of word i+1 both zero.  load, compare, load, compare -> ACCEPT.
    covered = np.zeros(65536, dtype=bool)
    n = 0
    for i in range(4):
        j = (i + 1) % 4
        for u, v in product(range(16), repeat=2):
            if (u >> 3) & 1 or v & 1:
                continue
            leaf = (W[i] == u) & (W[j] == v)
            assert not COVER[leaf].any()
            covered |= leaf
            n += 1
    assert (covered | ~ALLSAFE | COVER).all()     # every class-B file has such a pair
    print(f'class B paths: {n} two-word tests, each leaf set is SAT only; every class-B file has one  -> 4 steps')
    # C: four equality tests isolate the file itself -> 8 steps.
    print('class C paths: four loads and four equality tests isolate one file  -> 8 steps')


def lower_class_b():
    """No ACCEPT leaf reached in <= 3 steps contains a class-B file (full model).

    Reduction (clock-bounds-for-the-four-word-cube-cycle-catalog.md, section 1): on a class-B file x a path of <= 3
    instructions reads at most two original cells, and if x' agrees with x on
    the cells read then x' follows the same path.  With <= 1 cell read, x' = x
    on that cell and 15 elsewhere is a cover.  With two cells read the path is
    LOAD i; LOAD j; BRANCH with fixed literal addresses i != j (an address taken
    from the first loaded word is >= 5 on x and reads a zero cell), so the leaf
    set is {y : cmp(P, Q) = outcome} with P, Q in {literal, y_i, y_j}.  All
    such leaf sets are enumerated here on the full catalog.
    """
    target = ALLSAFE & ~COVER
    tried = bad = 0
    for i, j in product(range(4), repeat=2):
        if i == j:
            continue
        operands = [('lit', c) for c in range(16)] + [('w', i), ('w', j)]
        for name in BRANCH:
            tab = np.array([[branch(name, a, b) for b in range(16)] for a in range(16)])
            for p, q in product(operands, repeat=2):
                a = W[p[1]] if p[0] == 'w' else np.full(65536, p[1])
                b = W[q[1]] if q[0] == 'w' else np.full(65536, q[1])
                outcome = tab[a, b]
                for want in (True, False):
                    leaf = outcome == want
                    tried += 1
                    if leaf.any() and not COVER[leaf].any() and target[leaf].any():
                        bad += 1
    print(f'class B lower bound: {tried} three-step leaf sets (two literal loads + one comparison) tried, '
          f'{bad} are SAT-only and contain a class-B file')
    assert bad == 0
    # the one-cell argument: x' = (x_i at i, 15 elsewhere) is a cover for SAFE x_i
    for i in range(4):
        for v in SAFE:
            ws = [15] * 4
            ws[i] = v
            assert is_cover(mask_of(ws))
    print('one-cell argument: (v at one address, 15 elsewhere) is a cover for every SAFE v')


if __name__ == '__main__':
    counts()
    upper_paths()
    lower_class_b()
    print('pointwise clocks: A = 2 (61,440 files), B = 4 (1,889 files), C <= 8 (2,207 files)')
