"""Five-bit two-word clock and forced-false lifts at 18 and 20 selector bits."""

import subprocess
import tempfile
from itertools import combinations, product
from pathlib import Path

import numpy as np

from four_raw_comparisons_on_complementary_pairs import minimal_masks


def operation(name, a, b):
    signed_a = (a ^ 16) - 16
    signed_b = (b ^ 16) - 16
    if name < 6:
        value = (a & b, a | b, a ^ b, a + b, a - b, a * b)[name]
    elif name < 12:
        shift = b if name < 9 else b % 5
        value = (a << shift, a >> shift, signed_a >> shift)[(name - 6) % 3]
    elif name < 14:
        shift = b % 5 if name == 12 else (-b) % 5
        value = (a << shift) | (a >> (5 - shift))
    else:
        value = (
            a == b,
            a < b,
            signed_a < signed_b,
            a != b,
            a >= b,
            signed_a >= signed_b,
        )[name - 14]
    return np.asarray(value, dtype=np.int64) & 31


def rowmask(values):
    return int.from_bytes(np.packbits(values, bitorder="little").tobytes(), "little")


def comparisons(a, b):
    return (a == b, a < b, b < a, (a ^ 16) < (b ^ 16), (b ^ 16) < (a ^ 16))


def native_bit_planes():
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp)
        (dst / "probe.cpp").write_text(r"""
#include "five_bit_native_planes.hpp"
#include <cstdio>
int main() {
  for (int block=0; block<16; ++block) {
    Word a{},b{};
    for (int k=0;k<64;++k) {
      int v=block*64+k;
      for(int j=0;j<5;++j) {
        a[j]|=Mask((v>>(j+5))&1)<<k; b[j]|=Mask((v>>j)&1)<<k;
      }
    }
    for(int f=0;f<20;++f) {
      auto r=operation(f,a,b,~Mask(0));
      for(int k=0;k<64;++k) {
        int v=0;
        for(int j=0;j<5;++j) v|=((r[j]>>k)&1)<<j;
        std::putchar(v);
      }
    }
    for(auto g:tests(a,b,~Mask(0)))
      for(int k=0;k<64;++k) std::putchar((g>>k)&1);
  }
}
""")
        subprocess.run(
            [
                "c++",
                "-O2",
                "-std=c++20",
                "-I",
                str(Path(__file__).resolve().parent),
                str(dst / "probe.cpp"),
                "-o",
                str(dst / "probe"),
            ],
            check=True,
        )
        actual = subprocess.check_output([dst / "probe"])
    expected = []
    for block in range(16):
        codes = np.arange(64 * block, 64 * block + 64, dtype=np.int64)
        a, b = codes // 32, codes % 32
        expected.extend(operation(f, a, b) for f in range(20))
        expected.extend(comparisons(a, b))
    assert np.concatenate(expected).astype("uint8").tobytes() == actual
    print(
        "All 20,480 five-bit ALU and 5,120 comparison entries agree with the scalar tables."
    )


def pair_test(bits, offset):
    # A fixed high negative-unit bit represents the forced-false new variable.
    maximum = (1 << bits) - 1
    p, m = np.indices((maximum + 1, maximum + 1), dtype=np.int64).reshape(2, -1)
    raw = (p, m + offset)
    overlap = (p & m) != 0
    exceptional = (p == 0) & (m == maximum)
    labels = np.where(overlap, 0, np.where(exceptional, 1, 2))
    target = labels == 2
    original = [np.full_like(p, c) for c in range(32)] + list(raw)
    tables = set()
    for a in original:
        for b in original:
            for k in range(20):
                tables.add(operation(k, a, b).astype("uint8").tobytes())
    hits = []
    for encoded in tables:
        stage = np.frombuffer(encoded, dtype="uint8")
        for i, other in enumerate(original):
            for k, mask in enumerate(comparisons(stage, other)):
                if np.array_equal(mask, target) or np.array_equal(~mask, target):
                    hits.append((i, k))
    assert not hits, (bits, offset, hits)
    # Even arbitrary postprocessing of a single pair result cannot distinguish
    # all three residual Boolean functions of the other pair.
    for a, b in (raw, raw[::-1]):
        for k in range(20):
            r = operation(k, a, b)
            classes = [set(r[labels == i]) for i in range(3)]
            assert any(x & y for x, y in combinations(classes, 2))
    band = np.arange(4, 12)
    rows, cols = np.indices((8, 8))
    u, v = band[rows].ravel(), band[cols].ravel() + offset
    strict = (u & (v - offset)) == 0
    # Equality/disequality or a signed/unsigned order against any univariate
    # table cannot implement the noninterval 5th row/column on the high band.
    for first, second in ((u, v), (v, u)):
        fixed = first == 5 + (offset if first is v else 0)
        second_col = second[fixed]
        wanted = strict[fixed]
        assert wanted.sum() == 2 and not any(
            np.array_equal(g, wanted) or np.array_equal(~g, wanted)
            for c in range(32)
            for g in comparisons(c, second_col)
        )
    yes = np.flatnonzero((u + (v - offset)) == 15)
    neg = np.flatnonzero(~strict)
    cols_raw = [np.full_like(u, c) for c in range(32)] + [u, v]
    allmask = (1 << 64) - 1
    gs = set()
    for a, b in combinations(cols_raw, 2):
        for test in comparisons(a, b):
            msk = rowmask(test)
            gs.update((msk, msk ^ allmask))
    best = 0
    posmask = sum(1 << int(z) for z in yes)
    negmask = sum(1 << int(z) for z in neg)
    for a, b in product(gs, repeat=2):
        accepted = a & b
        if not accepted & negmask:
            best = max(best, (accepted & posmask).bit_count())
    assert best <= 2
    print(
        f"physical pair bits={bits} negative-base={offset}: {len(tables)} first ALU tables, "
        f"zero exact one-guard decisions, raw two-guard support {best}/8."
    )


def upper_and_lift(k):
    pmax = 31
    qmax = (1 << (k - 5)) - 1
    # Four native words with the input's two sign planes aligned separately.
    p, q, m, n = np.indices((32, qmax + 1, 32, qmax + 1), dtype=np.int64).reshape(4, -1)
    sat = ((p & m) == 0) & ((q & n) == 0) & ((m != pmax) | (n != qmax))
    program = np.where(
        m != pmax,
        ((p & m) == 0) & ((q & n) == 0),
        (n != qmax) & (p == 0) & ((q & n) == 0),
    )
    steps = np.where(
        m != pmax,
        np.where((p & m) != 0, 5, 9),
        np.where(n == qmax, 4, np.where(p != 0, 6, 9)),
    )
    assert np.array_equal(program, sat) and sat.sum() == 3**k - 1 and steps.max() == 9
    # At nine variables insert x5, and at ten insert x5 and x10, always false.
    # Padding words encode units of these new variables only.
    a, b, c, d = np.indices((16,) * 4, dtype=np.int64).reshape(4, -1)
    source = ((a & c) == 0) & ((b & d) == 0) & ((c != 15) | (d != 15))
    phys = (a, b, c | 16, d if k == 9 else d | 16)
    origin = np.ravel_multi_index(phys, (32, qmax + 1, 32, qmax + 1))
    assert np.array_equal(sat[origin], source)
    positive = p | (q << 5)
    negative = m | (n << 5)
    tight = positive | (negative << k)
    words = tuple((tight >> (5 * i)) & 31 for i in range(4))
    if k == 9:
        assert all(
            np.array_equal(x, y)
            for x, y in zip(
                words, (p, q | ((m & 1) << 4), (m >> 1) | ((n & 1) << 4), n >> 1)
            )
        )
        assert np.array_equal(((words[2] << 1) & 31) | (words[1] >> 4), m)
        assert np.array_equal((words[3] << 1) | (words[2] >> 4), n)
    else:
        assert all(np.array_equal(x, y) for x, y in zip(words, (p, q, m, n)))
    hist = {int(i): int(j) for i, j in zip(*np.unique(steps, return_counts=True))}
    print(
        f"{2 * k} selector bits, w=5, {sat.size} files: {int(sat.sum())} SAT, "
        f"nine-step program counts {hist}, all 65,536 forced-false embeddings agree."
    )


def tight_unaligned_program(variables):
    # For variables=8, an appended constant zero is the designated seventeenth bit.
    # The program loads the four physical words before converting the two negative masks.
    pos, neg = np.indices((1 << variables, 1 << variables), dtype=np.int64).reshape(
        2, -1
    )
    code = pos | (neg << variables)
    a, b, c, d = ((code >> (5 * i)) & 31 for i in range(4))
    shift = 10 - variables
    top = variables - 5
    m = ((c << shift) & 31) | (b >> top)
    n = ((d << shift) & 31) | (c >> top)
    short_max = (1 << top) - 1
    assert np.array_equal(m, neg & 31) and np.array_equal(n, neg >> 5)
    program = np.where(
        m == 31,
        (n != short_max) & (a == 0) & ((b & n) == 0),
        ((a & m) == 0) & ((b & n) == 0),
    )
    truth = ((pos & neg) == 0) & (neg != (1 << variables) - 1)
    assert np.array_equal(program, truth)
    print(
        f"Tight physical encoding at {17 if variables == 8 else 18} bits: "
        f"all {truth.size} verdicts agree with the 15-step upper program."
    )


def one_new_negative_selector(old_variables):
    # The new variable enters the fixed disjunction with no positive unit slot.
    # Its single negative unit z can be chosen by the input.
    pos, neg = np.indices(
        (1 << old_variables, 1 << old_variables), dtype=np.int64
    ).reshape(2, -1)
    if old_variables == 8:
        p, q = pos & 15, pos >> 4
        m, n = neg & 15, neg >> 4
        mask_word = 0
    else:
        p, q = pos & 31, pos >> 5
        m, n = neg & 31, neg >> 5
        mask_word = 1
    disjoint = (pos & neg) == 0
    old = disjoint & (neg != (1 << old_variables) - 1)
    counts = []
    for z in (0, 1):
        first = m + (16 * z if mask_word == 0 else 0)
        second = n + (16 * z if mask_word == 1 else 0)
        short_max = 15 if mask_word == 0 else 31
        physical = (
            ((p & first) == 0)
            & ((q & second) == 0)
            & ((first != 31) | (second != short_max))
        )
        assert np.array_equal(physical, old if z else disjoint)
        counts.append(int(physical.sum()))
    assert counts[0] == counts[1] + 1 == 3**old_variables
    print(
        f"{2 * old_variables + 1} independent aligned selectors, "
        f"{2 * len(old)} input files and {sum(counts)} SAT. "
        f"The added negative unit changes one old fiber."
    )


def raw_four_guard_support(k):
    offset = 0 if k == 9 else 16
    targets = [
        (p, q, 31 - p, 15 - q + offset) for p, q in product(range(4, 12), repeat=2)
    ]
    negatives = [
        (p, q, 16 + m, n + offset)
        for p, q, m, n in product(range(4, 12), repeat=4)
        if p & m or q & n
    ]
    columns = list(np.array(targets + negatives).T)
    cols = columns + [np.full_like(columns[0], c) for c in range(32)]
    yes = (1 << 64) - 1
    universe = (1 << (64 + len(negatives))) - 1
    guards = set()
    for a, b in combinations(cols, 2):
        for test in comparisons(a, b):
            bits = rowmask(test)
            for mask in (bits, bits ^ universe):
                if (mask & yes).bit_count() >= 2:
                    guards.add((mask & yes, mask >> 64))
    easy = 0
    for i, j in combinations(range(64), 2):
        pair = (1 << i) | (1 << j)
        permitted = [n for p, n in guards if p & pair == pair]
        shared = (1 << len(negatives)) - 1
        for neg in permitted:
            shared &= neg
        if shared:
            easy += 1
        else:
            single = minimal_masks(permitted)
            double = minimal_masks(a & b for a, b in product(single, repeat=2))
            assert all(a & b for a, b in product(double, repeat=2))
    print(
        f"{2 * k} selectors: {len(guards)} raw guard masks and {len(negatives)} negatives eliminate all 2,016 "
        f"target pairs from four-guard paths ({easy} pairs have one common negative)."
    )


if __name__ == "__main__":
    native_bit_planes()
    for shape in ((4, 0), (4, 16), (5, 0)):
        pair_test(*shape)
    for variables in (9, 10):
        upper_and_lift(variables)
        raw_four_guard_support(variables)
    for variables in (8, 9):
        tight_unaligned_program(variables)
        one_new_negative_selector(variables)
