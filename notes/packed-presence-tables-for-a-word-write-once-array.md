# Packed presence tables give a word-write-once array at amortized O(log m / log w) on the random workload

On the random alternating workload of the [write-once note](mutable-arrays-on-word-write-once-memory.md), model W has a deterministic array scheme that keeps one register between operations and whose expected amortized cost, in loads plus writes, is at most 12·⌊log₂ m / log₂ B⌋ + O(1) per operation, with B = 2^⌊½·log₂ w⌋. At w = Θ(log m) this is O(log m / log log m), so with the note's Lemma A′ the amortized cost on this workload is Θ(log m / log log m), and the log log gap of Lemma A′ is closed from above. Lemma A's worst-case form is not matched, because a merge writes Θ(min(n, m)) cells in one update. The scheme keeps tiered levels of sorted runs with, per level, a presence table packed B buckets to a word and rebuilt in the same pass as each merge, so every key is read O(1) times per level. Correctness and W-legality are proved for every operation sequence, but the cost bound only for the random workload; an instrumented simulator checks the scheme from m = 2^12 to 2^23, and an independent simulator written during review gives the same per-level counts. At w = 64 the scheme costs 2.1 to 2.4 times path copying at every size tested, so the gain is asymptotic only. Nothing here bounds SAT or any language; the linear, quadratic and cubic questions remain open.

## The model and the statement

Model W is that of the write-once note: every cell is written at most once, no cell is loaded before it is written, registers are kept between operations, and computation is free in the probe count. The workload is that of its Lemma A′: n operations alternate update(i, v) and read(q), with all indices and values independent and uniform.

**Lemma (packed presence tables).**
- *Parameters.* For all integers μ, β ≥ 1, put m = 2^μ and B = 2^β, and take any word width w ≥ max(B², 2μ + 2) that also addresses the scheme's memory.
- *The scheme.* There is a deterministic model-W scheme for an m-word array, initially all zero. It keeps one register between operations, the update count U. During an operation it uses a fixed number of registers: fewer than 50 scalar words and two w-bit words.
- *(i) For every operation sequence:* every read returns the current value, no cell is written twice, and no cell is loaded before it is written.
- *(ii) On the random workload:* for every n, the expected number of loads plus writes, amortized over the n operations, is at most 12·⌊μ/β⌋ + C₀, where C₀ is an absolute constant.
- *(iii) Word-RAM time* is within a constant factor of that count, plus a one-time write of a 2^B-entry bit-scan table (2^B ≤ 2^{√w}, that is m^{o(1)} words at w = Θ(log m)). In (ii) bit scans are free computation: the table loads counted in Sections 3 and 4 are an overcount, and no initialization is charged.

The simulator stores 2^{min(B,16)} table entries and handles B = 32 by first testing which 16-bit half is nonzero, so each scan is still one lookup; it refuses B > 32, where such a table would need ⌈B/16⌉ lookups per scan, a hidden factor in word-RAM time.

**Corollary.** Take w = Θ(log m) and B = 2^⌊½·log₂ w⌋ ≥ √w/2. Then the cost is O(log m / log log m), and Lemma A′ (C ≥ c·log m / log(wC + 2) for every model-W scheme with O(1) registers) makes this optimal up to a constant factor on this workload. More generally, the two bounds together give Θ(log m / log w) wherever Lemma A′'s hypotheses hold (m ≥ 2^20, n ≥ 3√m, w ≥ log₂ m, 16(r+2)w ≤ m^{1/4}) and w ≥ 2·log₂ m + 2. Below 2·log₂ m + 2, splitting each directory cell into two costs one more probe per directory access and keeps the order. This follows by combining the two statements; no further check was made. The scheme improves the order only when w = (log m)^{1+o(1)}, in particular at w = Θ(log m): packed path copying puts w/(address bits) pointers in a one-cell node and costs O(log m / log(w / log m)), which is already O(log m / log w) once w ≥ (log m)^{1+ε}.

**Sources and overlap.** The write-once note's next-step item 3 sketched frontier filters with Θ(B·log_B m) loads per update ("Each rebuild must *read* the keys"); the construction here avoids that cost because each key is read O(1) times per level. The journal's bit-write-once radix in [normalizing stores in a SAT solver](normalizing-stores-in-a-sat-solver.md) reads missing paths as zero and lies outside W. Nothing else in the journal states an o(log m) upper bound inside W. The construction descends from the Bentley–Saxe logarithmic method and log-structured merge trees, known from memory and not checked at source. Searches during review, at snippet and abstract level, found no statement of this bound; the closest idea found is Dayan and Twitto's "Chucky" (SIGMOD 2021), a global filter that maps key fingerprints to run identifiers across the levels of an LSM tree, in mutable external memory. No search was made in the write-once, persistent or purely functional array literature, so **novelty is not established**.

## 1. The scheme

Notation: e_c(ℓ) = min(ℓβ, μ) and e_f(ℓ) = min((ℓ+1)β, μ). Key x lies in bucket ⌊x / 2^{μ−e}⌋ at exponent e. Keys are uniform, so key order is hash order. P = w/B ≥ B presence vectors are packed in a word.
- **Runs.** Run (ℓ, g) covers the update window W(ℓ, g) = [g·B^ℓ, (g+1)·B^ℓ). It holds the distinct keys updated in that window, in ascending order (one cell per key, one cell per value), each with its last value in the window. For ℓ ≥ 1 it has a directory of 2^{e_c(ℓ)} cells, each holding (start, end) of one coarse bucket, packed in one word. Level-0 runs hold one key and have no directory.
- **Presence versions.** Version (ℓ, g) of level ℓ's table holds a B-bit vector for each fine bucket f < 2^{e_f(ℓ)}. Bit r is set iff run (ℓ, ⌊g/B⌋·B + r) has a key in f. A new version is written each time a run joins level ℓ.
- **Clock addressing.** With U = Σ d_ℓ·B^ℓ in base B, level ℓ holds d_ℓ runs, with ids ⌊U/B^{ℓ+1}⌋·B + r for r < d_ℓ, and its current version is ⌊U/B^ℓ⌋ − 1. Every structure of kind k at level ℓ sits at (4ℓ + k + 1)·2^RS plus id times slot size, so all addresses are O(1) shifts and multiplies of (U, ℓ, offset). There are no per-level pointers and no allocator. RS is a program constant fixed from w (for instance w − ⌈log₂(4L + 2)⌉, where L bounds the number of levels), so (i) holds for every sequence whose regions fit in 2^RS cells. The simulator takes RS from the number of updates.
- **Update** (index u = U). Write run (0, u) in 2 cells. Write version (0, u): 1 load of version (0, u−1) if u mod B ≠ 0, then 1 write. While the new id is ≡ B−1 mod B, merge that level into the next one.
- **Merge (ℓ−1 → run (ℓ, g)).** One pass over the coarse output buckets b < 2^{e_c(ℓ)}, in increasing order. Since e_f(ℓ−1) = e_c(ℓ), level ℓ−1's last version names the input runs with a key in b. The pass works by selection rounds:
  - For each named run, through the bit-scan table: load its directory cell for the bucket containing b, then scan from that bucket's start to the first key in b above the last key output.
  - Output the minimum such key with its value. Ties go to the larger r, the newer run.
  - OR its bit into a w-bit accumulator. The accumulator is level ℓ's new presence word; it was loaded from version (ℓ, g−1) if that exists.
  - Write the directory cell for b, and write the accumulator whenever its word index changes.

  There are no per-run cursors: a flagged run is re-entered through its directory on every round.
- **Read(q).** For ℓ = 0, 1, …, skip the level if d_ℓ = 0; this needs no probe. Otherwise load one presence word. Scan the flagged runs newest first: one directory cell, then keys until one is ≥ q, and the value if found. If no level has q, return 0.

Three design choices matter. There is no separate per-run occupancy bitmap: level ℓ's presence table is rebuilt in the same pass as the merge, because one coarse output bucket covers exactly the B fine buckets of one presence word when w = B². Directory cells pack (start, end), so a run's unwritten tail after deduplication is never probed; the negative control of Section 5 probes it and aborts. Empty levels are recognised from the clock digit, so no table is reset and no blank cell is read.

## 2. W-legality and correctness (any operation sequence)

**Writes.** Run (ℓ, g) and version (ℓ, g) are created exactly once, because g fixes the window and the update count passes each window once. Each cell of a structure is written once while that structure is built: key and value cells in order, one directory cell per coarse bucket, one write per presence word. So no cell is written twice.

**Loads.** Every load addresses one of four kinds of cell:
- a presence word of a version that exists (its digit is nonzero, or it is the input of the running merge), and all its words were written;
- a directory cell of an existing run (all 2^{e_c} cells are written);
- a key or value cell at a position below the end bound read from a directory cell;
- the bit-scan table, written at initialization.

So no unwritten cell is loaded.

**Correctness.**
- The windows of the runs present partition [0, U).
- Lower levels hold later windows, and within a level a larger r is later.
- A run keeps the last value per key in its window.
- Flags have no false negatives.
- The read visits runs in decreasing window order and stops at the first run that contains q. If no run contains q, q was never updated and 0 is correct.

## 3. Expected cost of a read (uncapped level ℓ, that is (ℓ+1)β ≤ μ)

Let N = B^ℓ be the window length. For run r, let n_{r,c} be its number of keys in coarse bucket c, and let Y_c ~ Bin(N, 2^{−e_c}) be the number of window updates landing in c. Then n_{r,c} ≤ Y_c, and since 2^{e_c} = N,

  E Σ_c n_{r,c}² ≤ Σ_c E Y_c² ≤ N + N²/2^{e_c} = 2N.

The point q is independent of the updates, so:
- Pr[r is flagged] ≤ (number of occupied fine buckets)/2^{e_f} ≤ N/B^{ℓ+1} = 1/B;
- E[n_{r,c(q)}·1(r flagged)] ≤ 2^{−e_f}·E Σ_c n_{r,c}·#{occupied fine buckets in c} ≤ 2^{−e_f}·2N = 2/B.

A flagged run costs one table load, one directory load and at most n_{r,c(q)} key loads. Summing over at most B − 1 runs:

  **E[loads at level ℓ] ≤ 1 + (B−1)·(2/B + 2/B) < 5**, plus one value load per read.

Capped levels have exact flags: a flag means q is in the run, so the read stops there.
- At the first fine-capped level ℓ₀ only one run is scanned, the newest that contains q. Given that it contains q, its count in q's coarse bucket is size-biased, with mean at most 1 + N·2^{−e_c(ℓ₀)} = 2. So the level costs O(1) in expectation; this step was added during review.
- Above ℓ₀ a run's window has more than m updates and contains q with probability at least 1 − 1/e, so a read probes O(1) capped levels in expectation.

## 4. Expected cost of a merge (uncapped ℓ ≥ 1)

Take coarse output bucket b. Let X_b ~ Bin(N, 1/N) be the number of window updates in b, and X_{r,b} the number from sub-window r.
- The output keys in b number k_b ≤ X_b, and the flagged runs |F_b| ≤ #{r : X_{r,b} ≥ 1} ≤ X_b.
- A flagged run's scan per round is at most X_{r,b} + Z_{r,b}, where Z_{r,b} counts sub-window r's updates in the input coarse bucket of b, outside b. Given all counts in b, Z_{r,b} is binomial with mean at most B^{ℓ−1}·(B−1)B^{−ℓ}/(1 − B^{−ℓ}) ≤ 1.
- There are k_b + 1 rounds. So

  E[selection cost of b] ≤ E[(X_b+1)·(3X_b + Σ_r 1(X_{r,b} ≥ 1)·Z_{r,b})] ≤ 3(E X_b² + E X_b) + E[(X_b+1)·X_b] < 9 + 3 = 12.

The other terms per merge are:
- output: value load plus key and value writes, ≤ 3N;
- directory writes: N;
- level ℓ's presence words, old version loaded and new one written: 2·B^{ℓ+1}/P ≤ 2N;
- the input presence words: N/P.

Total: **E[merge] ≤ 19N, that is ≤ 19 loads plus writes per update per level**, independent of B and ℓ. There is no hidden factor log B: deduplication costs nothing extra, the choice of run is a linear selection costing O(X_b²) per bucket, false flags are at most (B−1)/B per level, and field extraction is shifts and masks; this was checked during review step by step.

Capped levels cost O(1) per update in total (a short argument, not written out in full).
- At the first capped level ℓ₀ the coarse buckets are still uncapped, and the count above applies.
- At ℓ₀ + 1 the window lies between m and B·m. The input keys number at most the window and the buckets at most m, so the cost is O(1) per update.
- From ℓ₀ + 2 on, a merge handles at most B·m input keys and m buckets per window of more than B·m updates, so the cost per update falls by a factor B per level.

Averaging an update and a read gives (19 + 5)/2 = 12 per uncapped level, which is (ii).

## 5. The simulator and its runs

`write_once_array_presence_table_simulator.cpp` is an instrumented simulator of the scheme and of path copying. Its memory layer aborts on a load of an unwritten cell (exit 3) or a second write (exit 4), and counts every probe by operation, level and category. The scheme's state between operations is one register, the update count; the written-cell bitmap and the reference array are used only by the harness, which checks every read. Path copying is the baseline: F-ary, two 32-bit pointers per cell (the same packing the scheme uses for directories), top-down allocation, and a null pointer for empty subtrees, so it too is legal in W. `write_once_array_presence_table_runs.py all` runs every configuration below, two processes at a time under the 8 GB cap, in about 80 seconds; the largest run, at m = 2^23, reaches 4.3 GB, so m = 2^24 would exceed the cap. Each run has n = 2m updates, each followed by a read, and is measured over the second half, which for m = 8^k is exactly one full cycle of every level below k, after warm-up.

**Main configuration, w = 64 and B = 8:**

```
mu | Z1 per-op (s1, s2) | Z1 per-upd, per-read | PC per-op F=2,4,8,16 (pp=2) | best PC | ratio Z1/bestPC | levels used
12 |  33.80  33.88 |  56.83  10.77 |  18.81  15.87  18.88  26.38 |  15.87 |  2.13 | 5  ok=True
15 |  43.06  42.99 |  72.88  13.25 |  23.32  20.79  23.38  34.88 |  20.79 |  2.07 | 6  ok=True
18 |  52.27  52.28 |  88.95  15.60 |  27.82  23.38  27.88  43.36 |  23.38 |  2.24 | 7  ok=True
21 |  61.51  61.51 | 105.04  17.97 |  32.32  28.30  32.38  51.62 |  28.30 |  2.17 | 8  ok=True
mu=22: Z1 per-op 63.25  PC(F=4) per-op 28.38  ratio 2.23  levels 2-5 upd 15.95-16.08 rd 2.36-2.37  ok=True
mu=23: Z1 per-op 72.61  PC(F=4) per-op 30.80  ratio 2.36  levels 2-5 upd 15.95-16.09 rd 2.37-2.37  ok=True
```

At m = 2^22 and 2^23 only seed 1 and F = 4 were run; F = 4 is the best path copying at every μ from 12 to 21. The scheme grows by 9.21 to 9.26 per operation for each added level (3 bits of μ), and path copying with F = 4 by about 1.37 per bit.

**Per level, m = 2^21, seed 1** (upd = loads plus writes per update charged to the level; rd = loads per read at the level; flag = flagged runs per read that probes the level; k/dir = keys loaded per directory probe; mdir, mkey, msel = merge directory probes, key loads and selection rounds per output key):

```
 lev    upd     rd   flag  k/dir   mdir   mkey   msel    out
   0   3.88   1.75  0.500  0.000  0.000  0.000  0.000  1.000
   1  11.75   2.36  0.473  1.574  0.000  2.875  1.656  1.000
   2  15.95   2.37  0.470  1.633  2.776  4.398  1.635  1.000
   3  16.08   2.37  0.470  1.639  2.765  4.548  1.632  1.000
   4  16.08   2.37  0.467  1.637  2.763  4.567  1.633  0.999
   5  15.99   2.35  0.456  1.607  2.764  4.567  1.637  0.992
   6  15.32   2.18  0.374  1.413  2.776  4.559  1.672  0.940
   7   9.99   2.23  0.632  1.000  2.975  4.686  2.000  0.632
```

Over all six sizes the interior levels (from level 2 up to two below the top) stay below the proved 19 and 5:

```
mu = 12, 15, 18, 21, 22, 23: upd 15.88-16.09  rd 2.32-2.38  over 19 level rows
```

**B-sweep.** Presence words have B² bits and cost one probe each. Key, value and directory cells stay 64-bit, so at B = 2 and 4 this is a mixed-width model. The sweep tests dependence on B only and is outside w = Θ(log m). Columns are means over the interior levels:

```
mu beta  B | interior levels | upd/level  rd/level  flag/level  k/dir  mdir  mkey  msel | total per op | levels used
18    1   2 | 2..17 |    13.50     1.17     0.395  1.461  2.21  3.38  1.66 |  137.74 | 20 ok=True
18    2   4 | 2..8  |    14.94     1.91     0.430  1.540  2.56  4.08  1.65 |   74.31 | 10 ok=True
18    3   8 | 2..5  |    15.83     2.32     0.442  1.574  2.77  4.52  1.64 |   52.27 | 7 ok=True
18    4  16 | 2..3  |    16.45     2.57     0.466  1.634  2.88  4.75  1.64 |   37.81 | 5 ok=True
18    5  32 | 2..2  |    16.72     2.69     0.473  1.647  2.94  4.87  1.63 |   29.27 | 4 ok=True
20    5  32 | 2..3  |    16.66     2.63     0.429  1.572  2.94  4.90  1.64 |   35.77 | 5 ok=True
```

Each doubling of B adds +1.44, +0.89, +0.62 and +0.27 to upd/level, and +0.74, +0.41, +0.25 and +0.12 to rd/level. The increments roughly halve, as an approach to the B-free bounds of Sections 3 and 4 would do (flag → ½ as B → ∞), while a hidden log B would add a constant per doubling. The product (total per op) × β is 138, 149, 157, 151 and 146 at μ = 18, consistent with total ≈ c·μ/β. These totals are not comparable with path copying, which uses two pointers per 64-bit cell: with cells of B² bits it could pack B²/32 pointers per cell, and at B = 32 (1,024 bits) that is a one-cell 32-ary node, about 7 per operation at μ = 18 by count, not run, far below the scheme's 29.27.

**Large B, during review.** A one-level Monte Carlo written during review (`write_once_array_presence_table_large_b_monte_carlo.py`, an interior level in the limit N ≪ m, seed 1 and 200,000 trials) extends this to B = 2048:

```
    B  merge/upd   out/upd  rounds/out | read/level  flag/read
    8     16.088     1.000       1.631 |      2.706      0.469
   32     16.789     1.000       1.633 |      2.798      0.490
  128     16.960     0.999       1.633 |      2.842      0.500
  512     17.058     1.002       1.632 |      2.839      0.500
 2048     17.069     1.000       1.631 |      2.842      0.500
```

The merge cost levels off at about 17 per update and the read cost at about 2.84 per level, below the proved 19 and 5. Selection rounds per output key are 1.63, close to 1 + Pr[Poisson(1) ≥ 1].

**Many more operations than cells.** The main runs have n ≤ 4m, so the capped levels from ℓ₀ + 2 on never execute there. During review both simulators were run with n up to 1024·m, and the cost per operation stays flat in n, and from ℓ₀ + 2 on each level's update cost falls by a factor of about B (the lines below start at ℓ₀, so their first two values are levels ℓ₀ and ℓ₀ + 1):

```
mu=8 B=4: per op 36.84 (Nu=1024) / 35.83 (Nu=16384) / 35.61 (Nu=262144)
   levels 4..: upd 9.74 4.96 1.77 0.45 0.11 0.06
mu=7 B=8: per op 23.84 (Nu=512) / 21.82 (Nu=16384) / 21.85 (Nu=262144)
   levels 2..: upd 11.93 6.27 1.61 0.20 0.05
```

**W status and correctness.** Every run ends with no read error and no W-violation; the negative controls abort:

```
runs checked: 56, problems: 0
neg_illegal_load: exit 3, W-VIOLATION: load of unwritten cell 1179775 (op 1)
neg_illegal_write: exit 4, W-VIOLATION: second write of cell 1441792 (op 0)
```

The illegal-load control probes the last slot of a deduplicated run's allocation; the illegal-write control rewrites one directory cell. Both abort, so the zero violation counts are meaningful.

**Structured key sequences** (B = 8, μ = 15 unless marked). "hash" means the scheme is fed π_a(x) = a·x mod m with a random odd a: a bijection, one more register, the scheme's code unchanged.

```
scope_wl0_hash_mu15          per-upd   72.83 per-read   13.26 per-op   43.05  read errors 0
scope_wl0_nohash_mu15        per-upd   72.88 per-read   13.25 per-op   43.06  read errors 0
scope_wl1_hash_mu15          per-upd   53.09 per-read   10.19 per-op   31.64  read errors 0
scope_wl1_hash_mu18          per-upd   69.91 per-read   13.03 per-op   41.47  read errors 0
scope_wl1_nohash_mu15        per-upd  295.07 per-read  140.32 per-op  217.69  read errors 0
scope_wl2_hash_mu15          per-upd   67.47 per-read   13.93 per-op   40.70  read errors 0
scope_wl2_hash_mu18          per-upd   87.06 per-read   16.58 per-op   51.82  read errors 0
scope_wl2_nohash_mu15        per-upd  192.27 per-read   13.52 per-op  102.89  read errors 0
```

Here wl0 is the random workload, wl1 has keys and reads in [0, m/64), and wl2 has sequential updates. The unhashed bucket function is attacked, as expected: the selection cost in a bucket grows with the square of the bucket's load, and wl1 costs 5.1 times the random workload at m = 2^15. On these two sequences the multiplier restores the uniform cost.

**Independent simulator, during review.** `write_once_array_presence_table_independent_simulator.py` was written during review from the description of Section 1, after reading the simulator above, so it is a second implementation rather than a blind one. It names cells by (kind, level, id, offset), or with `--intaddr` by the integer layout of Section 1, checks write-once and that no unwritten cell is loaded, and charges one probe per bit scan as the simulator does. Its per-operation cost on the random workload is 33.90 and 33.80 at m = 2^12 (two seeds; the simulator gives 33.80 and 33.88), 43.04 at 2^15 (43.06) and 52.28 at 2^18 (52.27), with per-level rows agreeing to about 0.1. It finds no violation and no read error on the random workload and on five structured ones, with B = 2, 4 and 8 and with P = 2B and 4B, and its default suite runs four negative controls, all of which abort:

```
W-VIOLATION (inplace, uniform): second write of cell ('P', 0, 0, 0) during upd
W-VIOLATION (noend1, uniform): load of unwritten cell ('K', 1, 4, 8) during read
W-VIOLATION (tailload, uniform): load of unwritten cell 589887 during read
W-VIOLATION (dirtwice, uniform): second write of cell 720896 during upd
default suite: 8 runs and 4 negative controls, problems: 0
```

The first updates a presence table in place, the second reads past a directory's end bound at levels ≥ 1, and the last two replicate the simulator's controls in the integer layout. The end-bound control lands at slot = capacity, which in the integer layout is the next run's slot 0, so it does not isolate the deduplicated-tail hazard; the replicated tail control does.

## 6. The three standard tests

- **(a) Fast solver for the hard family?** Not applicable in the sense meant: this is an upper bound, not a lower bound. The workload costs O(1) per operation on a RAM with mutable memory.
- **(b) The same bound for 2-SAT?** Not applicable. No language is bounded, and the construction applies equally to any program's memory.
- **(c) The oracle of the [relativized clock](relativized-clock.md).** The construction uses only O(1)-word loads and stores, shifts, masks and multiplies, so no oracle binds it. The oracle model reads unwritten memory as zero, which is outside W, and the scheme never needs that.

## 7. Exact obstruction and next step

1. **Arbitrary address sequences.** A RAM run's addresses, which the alternating-time route of the [round-five summary](parallel-proof-attempts-of-28-november-round-five.md) needs, form a fixed sequence of w-bit words, not uniform keys. The deterministic bucket function fails on such sequences (5.1 times the cost at m = 2^15 above, and quadratic in the bucket load in general).
   - With a hash seed of O(1) words, drawn independently of the sequence, the computation of Sections 3 and 4 goes through for every fixed sequence if the family is 3-wise independent. Examples are a degree-2 polynomial over a prime field, with runs sorted by (h(x), x), or keys taken as full w-bit addresses with log_B t levels. The read's term E[n·1(flag)] and the merge's cross term are three-point events (x, y, q).
   - Multiply-shift (a·x mod 2^μ with a random odd a, bucket = top bits) is universal only up to a factor 2: collision probability at most 2^{1−ℓ} for ℓ output bits, a bound recalled during review from Dietzfelbinger et al. and not checked at source. It is not 2- or 3-wise independent. The proof here does not cover it, although it passed the two sequences above.
   - For a fixed sequence the capped-level read argument changes, as noted during review: a never-updated q visits every nonempty capped level, which is log_B(n/m) + O(1) of them. That is inside the O(log_B n + 1) of the next lemma.
   - **Next lemma** (a sketch, unchecked): for every fixed sequence of n operations on w-bit addresses, and h from a 3-wise independent family held in O(1) registers, the expected amortized cost is O(log_B n + 1). On 28 November a round-six note proved it, with a degree-2 polynomial seed modulo a prime and levels that never cap ([seeded write-once array](ram-time-t-in-word-priced-alternating-time-t-over-log-log-t.md)).
2. **Worst case per operation.** The bounds are amortized. A merge at the top level touches Θ(m) cells in one operation. A route that counts total steps may not need more; deamortization was not tried.
3. **Constants.** At feasible sizes the scheme loses to path copying by a factor of about 2 at w = 64.
   - The measured slope is about 9.2 per operation per level of the scheme, against about 1.37 per bit for path copying (F = 4, two pointers per cell). So the scheme wins only when log₂ B ≳ 7, that is B ≳ 128 and w = B² ≳ 2^14.
   - That holds only while path copying is held to two pointers per cell, that is with w about twice the address width, so log₂ m in the thousands. At a fixed m a wider word lets path copying pack more pointers and favours it (B-sweep above).
   - A register buffer of a few keys per bucket would remove the repeated selection scans (msel ≈ 1.64 rounds and mkey ≈ 4.5 loads per key) and might halve the update cost. It was not tried, and it does not affect the asymptotic statement.

## 8. What is not proved

- Nothing about SAT or any language. The alternating-time route of the round-five summary is untouched: the append-only normal form, the round-three truth-claim lemma (itself unreviewed) and the alternating speedup.
- The bound is proved for the random workload only, in expectation and amortized. For every fixed sequence with a hashed seed it is a sketch (Section 7). Multiply-shift is checked on two sequences at m = 2^15 and 2^18 and is not proved.
- The capped top levels are handled by a short argument, not written out in full; the n ≫ m runs above agree with it. The constants 19 and 5 are upper bounds, not optimized, and C₀ is not computed.
- The simulator checks m ≤ 2^23 at B = 8 (two seeds up to 2^21, one seed at 2^22 and 2^23), and m = 2^18 and 2^20 for B = 2 to 32 with packing width B², outside w = Θ(log m).
- Word-RAM time is argued, not instrumented: O(1) ALU operations per probe and per level, and bit scans through a 2^B-entry table. The simulator counts probes including table loads, which overcount (ii), and charges no table initialization. A layout with RS fixed from w was not run; both simulators take RS from the number of updates.
- Lemma A's worst-case form (t_u per update) is not matched, and max(t_q, t_u) = o(log m) in the worst-case sense remains open, as do arbitrary sequences.
- Novelty against the literature is not established.

## Reproducing the checks

Run from `audits/`. No script writes files unless given `--out DIR`.

```
python3 write_once_array_presence_table_runs.py
python3 write_once_array_presence_table_runs.py all
python3 write_once_array_presence_table_independent_simulator.py
python3 write_once_array_presence_table_large_b_monte_carlo.py
python3 write_once_array_presence_table_large_b_monte_carlo.py 1 200000 8 32 128 512 2048
```

The runs script compiles `write_once_array_presence_table_simulator.cpp` into a temporary directory and every child process runs under an 8 GB address-space cap. With no argument it runs the small configurations (m up to 2^15, the n ≫ m runs and the negative controls) in a few seconds; `all` adds every configuration above in about 80 seconds, with one process at 4.3 GB. The independent simulator's default suite takes about 3 seconds; with arguments it runs one configuration, for example `15 3 8 65536 1` (about 4 seconds) or `18 3 8 524288 1` (about 50 seconds and 2.3 GB). The Monte Carlo's default (B = 8 and 32) takes about 7 seconds, and the full table about 6 minutes. [Runs](../audits/write_once_array_presence_table_runs.py) · [Simulator](../audits/write_once_array_presence_table_simulator.cpp) · [Independent simulator](../audits/write_once_array_presence_table_independent_simulator.py) · [Large-B Monte Carlo](../audits/write_once_array_presence_table_large_b_monte_carlo.py)
