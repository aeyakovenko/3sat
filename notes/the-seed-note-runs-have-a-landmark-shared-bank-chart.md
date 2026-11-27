# The seed note's runs have a landmark shared-bank chart: one bank serves every loop-head cut, with at most h probes per decode

On the families of the seed note, the landmark shared-bank chart that the note left as a sketch exists for the runs of its two programs P_main and P_first. One bank of 6 + w_b(3+2K) bits, with K < 2m/h, serves every cut at loop heads, and each decode takes at most h probes. This is proved by hand for every even m below 2^63 (the bank's width field has 6 bits) and all h and g, and checked exhaustively at small m by two independent checkers. So those runs cannot refute shared-bank charts, while whether another linear-time program on the same files does remains the open part of barrier (d). Corollary 6 of the seed note already counts a shared bank, and the chart meets it within O(log m) when Q counts distinct values of f per decoded word. Nothing here bears on time lower bounds, and the linear, quadratic and cubic questions remain open. [Seed note](checking-an-interval-against-a-seed-of-unknown-bits.md) · [Barrier (d)](what-any-proof-of-superlinear-sat-time-must-get-past.md#d-the-checkpoint-technique-and-the-snapshot-frontier)

## What is new and what is not

That the trade-off is tight is not new. The inverse-snapshot frontier note already says that on the same work array "the best achievable product of advice bits and lookup time is determined up to logarithms", and it uses this decoder; Section 4 transfers that result to the seed note's P and its chart format. The square-root balance of the landmark index on a scatter-inverse array is in the scatter-inverse note, and the same √m choice is in the prefix-certificate note; the computed-controller row of Section 4 is that balance written in the seed format. Both cite eprint 2019/1046 for the cycle index, which was not accessed here. [Inverse-snapshot frontier](inverse-snapshot-frontier.md) · [Scatter-inverse live reads](scatter-inverse-live-reads.md) · [Prefix certificates](prefix-certificates-for-cnf.md)

New here:
- the chart written out in the seed format, at instruction level for the loops, on both families, including the data-dependent stale registers;
- a checker that follows the format, with a negative control;
- the bound of at most h probes per decode, where the journal's audit had 2h;
- the exponent split between an explicit and a computed cut list.

## 1. The lemma

Fix a family F: either *main* (2m+7 clauses, where P accepts a permutation file, which is satisfiable) or *first* (4m+7 clauses, where the scatter program gives the UNSAT signal exactly on permutations). Fix an even m with 2 ≤ m < 2^63 and integers h, g ≥ 1. Then for every permutation f of {0,…,m−1}, the run of the register-machine model of P_F's two loops (Section 2; `program()` in `landmark_shared_bank_chart_check.py`) on the file of f has a **degree-0 chart** in the seed note's format with the following properties.

- **Rows.** Row 0 is at time 0. Row k, for 1 ≤ k ≤ ⌈2m/g⌉, is at the loop head with global loop counter G = (k−1)g; G < m is phase 1 and G ≥ m is phase 2. The last row is at the accepting halt. All of these times are computed from (m, g) by the fixed evaluator.
- **Advice.** The only advice is one bank Z shared by all rows: a 6-bit width w_b, then g, h and K, then K sorted pairs (mark, preceding mark). Here K = Σ over cycles C of f with |C| > h of ⌈|C|/h⌉, which is less than 2m/h, and |Z| = 6 + w_b(3 + 2K) bits.
- **Evaluator.** One fixed program receives a row index, a coordinate (the pc, a register or any memory address), the file bytes and Z, and returns one bit. Each call:
  - parses the header (O(log m) bytes) and four bank fields;
  - decodes at most once, using **at most h** unit-row field parses of D+1 bytes each and at most (h+1)⌈log₂(K+1)⌉ directory reads. This holds for the honest bank. For an arbitrary bank, the format fixes a parameter h_fmt before f is chosen, and the decoder stops after 2·min(h, h_fmt)+2 probes, where h is the bank's field. So the per-call cap E is fixed in advance, as Corollary 6 and the defect-time bound require; the checks use h_fmt = h;
  - parses at most one more field.
- **Soundness.** Row 0 is the genuine initial configuration, every interval identity holds, and the last row's pc is the accepting halt: SAT on the main family, the UNSAT signal on the first.

The quantitative case h = g = ⌈m^{1/3}⌉ gives a bank of O(m^{2/3} log m) bits, defect time R = O(m^{2/3} log² m) and O(m^{2/3}) rows, against 2m loop iterations.

## 2. Model and proof

**Model.** A register machine with indirect LOAD and STORE runs the two loops of P at instruction level: registers I, A, V, T, U, M, H and the pc; the work array B at addresses 0..m−1, with every other address zero; word width W = max(bitlen(m+1), bitlen(|program|), 2). The digit-by-digit field parse is abstracted as one input read `INP r ← f(index)`. Input reads are constants in the chart format, so they cost no entry bits. On a permutation, P_main runs 8 instructions per phase-1 iteration (P_first runs 6) and 9 per phase-2 iteration, and the halt comes at time 6 + (c₁+9)m. The checker asserts, on every run, that the genuine pc at every scheduled cut is the claimed loop head.

**(1) Decode lemma.** Take y on a cycle C.
- If |C| ≤ h, the cycle has no marks, and walking forward from y returns to y after |C| ≤ h probes. The last vertex before that return is f⁻¹(y).
- If |C| > h, let M be the first mark at or after y and M′ its stored preceding mark. The walk spends dist(y, M) probes reaching M, then dist(M′, y) probes walking from M′ until the image equals y: dist(M′, M) ≤ h probes in total, including the case y = M.

This tightens the journal audit's bound of 2·span to h. The count K < 2m/h holds because each long cycle has ⌈|C|/h⌉ < |C|/h + 1 < 2|C|/h.

**(2) Snapshot formulas.** These hold by induction over iterations, using that f is injective; in particular P_main's same-half test always sees V = 0. Write j(a) = f⁻¹(a).

| Cut | B[a] for a < m | Registers |
|---|---|---|
| Phase-1 head i | j(a)+1 if j(a) < i, else 0 | I = i, A = f(i−1), V = 0, T = i, U = 0 (all zero at i = 0) |
| Phase-2 head y | j(a)+1 | I = y, A = f(m−1); V = j(y−1)+1, T = j(y−1), U = y−1 if y ≥ 1; (V, T, U) = (0, m, 0) if y = 0 |
| Halt | j(a)+1 | the phase-2 values with y = m |

In every row after row 0, M = m and H = m/2. Row 0 is all zero, and every address outside [0, m) holds 0 in every row.

**(3) Degree 0.** Each row equals the genuine snapshot, so each interval identity holds because the machine is deterministic, and Lemma 2 of the seed note gives the verdict. ∎

**Is the register program P?** Yes, on every map at small m. On all maps f, not only permutations (m = 2, 4 for the main family; m = 2, 3, 4 for the first), its halt kind agrees with the journal audit's `scatter_solver` (with the fallback reported as such) and `surjection_solver`, copied unchanged:

```
register programs agree with the audit's solvers on all maps: {('first', 2, 'accept'): 2, ('first', 2, 'reject'): 2, ('first', 3, 'accept'): 6, ('first', 3, 'reject'): 21, ('first', 4, 'accept'): 24, ('first', 4, 'reject'): 232, ('main', 2, 'accept'): 2, ('main', 2, 'reject'): 2, ('main', 4, 'accept'): 24, ('main', 4, 'fallback'): 112, ('main', 4, 'reject'): 120}
```

**A qualifier on the seed note's "the cut controllers need no advice".** The stale data registers V and T at phase-2 heads hold f⁻¹(y−1)+1 and f⁻¹(y−1), so the evaluator spends one decode on them. They need no advice beyond the bank, but they depend on the data. This is true even of the seed note's loop-level P, whose register v is stale there.

**Defect time.**
- A gap of g iterations reads at most g table words plus ρ = 8 controller words (the pc and seven registers), so q ≤ W(g+8).
- Each bit call re-decodes its word, so E_bit = E_word = O(h log m + log m): h fields of D+1 bytes plus the binary searches.
- R ≤ 9g + (q+2)E_bit = O(g·h·log² m).

## 3. Finite checks

The checker `check_chart` follows the seed note's format:
- **Replay.** Each gap is replayed with a private overlay. Every entry word is fetched from row k by W separate bit calls, and those costs are summed.
- **Exit comparison.** Every exit coordinate is compared with row k+1: the pc, all registers, B[0..m−1], the guard addresses m, m+1 and 2^W−1, and every address touched in the gap. Untouched addresses outside [0, m) are 0 in every row, for any bank, so they cannot carry a defect.
- **Initial and terminal conditions.** Row 0 must equal the all-zero initial configuration on the same universe, and the last row's pc must be the accepting halt.
- **Cross-check.** Every row is compared with the direct simulation's snapshot.

```
all (h,g) in [1..m]^2, every permutation, both families: charts sound: {(2, 'first'): 8, (2, 'main'): 8, (4, 'first'): 384, (4, 'main'): 384, (6, 'first'): 25920, (6, 'main'): 25920}
m=8 family=main h=g=2 W=5: 40320 permutations, all charts sound; max (bank bits, decode probes, q, R) = (58, 2, 25, 641), rows = 10
m=8 family=first h=g=2 W=5: 40320 permutations, all charts sound; max (bank bits, decode probes, q, R) = (58, 2, 25, 626), rows = 10
decoder alone, m=8, h=1..8: 2580480 inversions correct, probes <= 2h-1, K*h < 2m
2606792 decodes (m = 2,4,6,8; every permutation; h = 1..m): all correct, probes <= h; 1303180 decodes use exactly h probes
```

**An independent checker, written during review,** shares no code with these scripts. Its file generators are the journal audit's own, and it has its own interpreter and program text, bank encoder, evaluator written from the snapshot table, and decoder. It checks the initial condition, every gap replay and the terminal condition at every coordinate, including all 2^W addresses, and compares every row with direct simulation.
- For m ∈ {2, 4, 6}, both families, every permutation and every (h, g) ∈ [1..m]²: 52,624 charts, all sound, with decode probes ≤ h.
- For m = 8 and h = g = 2, every permutation on both families: 2 × 40,320 charts, all sound at all 32 addresses.
- The two machines agree at every instruction step (165,200 steps over all permutations at m ≤ 6), and the two evaluators agree on all 14,710,400 (row, coordinate) values.

**Negative control.** The bank was corrupted in four ways: a random bit flip, a wrong preceding mark, a dropped mark and an added mark. For every one of the 32,356 corrupted banks (m ∈ {4, 6}; both families; (h, g) ∈ {(1,1), (2,2), (2,1), (3,2)}; h_fmt equal to the honest h), the checker's accept/reject equals "every row equals the genuine snapshot". The tally is the same under PYTHONHASHSEED = 0, 1, 2, 3 and 7:

```
corrupted banks: checker verdict == (all rows equal the true snapshots) in every case: {('add', 'accepted'): 2597, ('add', 'rejected'): 1871, ('drop', 'accepted'): 3235, ('drop', 'rejected'): 1781, ('flip', 'accepted'): 10247, ('flip', 'rejected'): 7609, ('pred', 'accepted'): 3266, ('pred', 'rejected'): 1750}
```

All 13,011 rejected banks give at least one false row, and all 19,345 accepted ones give only true rows. Many corruptions are harmless: the decoder tolerates a preceding-mark pointer that lands earlier on the same cycle within its probe cap, and a changed g field just gives another valid schedule.

The clamp to h_fmt decides 117 of the flipped banks. All 117 are single-bit flips of the 6-bit width field, at bits 1, 2 or 3 (37, 38 and 42 banks), and all occur at m = 6 with (h, g) = (1, 1): 54 on the main family and 63 on the first. In each, the parsed h exceeds h_fmt. Without the clamp the decoder still returns true rows, but only after more than 2·h_fmt+2 probes, beyond the cap fixed before f. With the clamp some row is false and the checker rejects the bank, which the independent checker, examining all 2^W addresses, confirms. The review's own corruption tests agree with these scripts: 29,184 banks at m = 4, exhaustively over every (h, g) and all four kinds, and 64,512 banks at m = 6 on 120 random permutations per family, with identical tallies under both evaluators.

**Scale.** One random permutation per size, main family, h = g = ⌈m^{1/3}⌉. Every gap is replayed. Memory coordinates are restricted to 48 random addresses, the guards and every touched word, so these runs are measurements, not exhaustive checks.

```
 m      N(bits)  h=g  W  K(marks) bank_bits  m^(2/3)log2m  probes_max  E_max  q_max  R_max  rows  gaps_sampled
    64      15224   4  7       16       251           96          4     47     49    1715    34    33
   512     140336   8 10       67      1376          576          8    102    110    8196   130   129
  4096    1311968  16 13      257      6727         3072         16    230    247   41863   514   513
 32768   12060056  32 16     1027     32918        15360         32    537    560  221680  2050  2049
```

- **Bank.** The bank divided by m^{2/3} log₂ m is 2.61, 2.39, 2.19 and 2.14 at the four sizes. At m = 32768 the bank is 0.27% of N; the whole inverse table, log₂ m!, is 3.68% of N.
- **Defect time.** R_max divided by m^{2/3} log₂² m is 2.98, 1.58, 1.14 and 0.96. The model run has 6 + 17m instructions, so R_max divided by the run length is 1.57, 0.94, 0.60 and 0.40. It falls like m^{−1/3} log² m, but it is not small at these sizes.
- **Explicit cut list.** Written out, at about rows × (8W + bitlen(6+17m)) bits (8 controller words plus the time), the cut list costs 2,278, 12,220, 62,194 and 303,400 bits at the four sizes: about nine times the bank, with the same order m^{2/3} log m. So u = v = 2/3 is an asymptotic statement; at these sizes the cut list dominates the description.

With g = 1 and h = ⌈√m⌉, where the controllers are computed rather than listed, the same runs give smaller banks and R (the "h=g" column is h here):

```
 m      N(bits)  h=g  W  K(marks) bank_bits  m^(2/3)log2m  probes_max  E_max  q_max  R_max  rows  gaps_sampled
    64      15224   8  7        7       125           96          8     67     28    1010   130   129
   512     140336  23 10       21       456          576         23    222     40    3312  1026  1025
  4096    1311968  64 13       64      1709         3072         64    727     52   11797  8194  8193
```

At m = 4096 this gives a bank of 1,709 bits and R_max = 11,797, against 6,727 and 41,863 for h = g = 16. Both are about m^{1/2} times a polylogarithmic factor. The price is 8,194 rows, which are free only because the evaluator computes the cut times and controllers.

**Per-cut count against the shared bank** (`landmark_bank_per_cut_crossover.py`).
- *Per-cut total.* Corollary 6 part 2 says that all but an m·2^{1−t} fraction of permutations need more than t = ⌊m/(4(Q+1))⌋ bits at every phase-2 head y ≤ m/2 simultaneously. The total is ⌊m/(2g)⌋·t; part 1's one-cut bound for the worst permutation is not summed.
- *Shared bank.* The landmark bank, with K bounded by 2m/h.
- *Two conventions for Q.* With Q = h (values of f per decoded word), the per-cut total first exceeds the bank between m = 2^12 and 2^14: the ratio is 0.575 at 2^12, 1.257 at 2^14 and 2.866 at 2^16, and the exceptional fraction is 7·10⁻¹⁵ at 2^12. With Q = W·h (Corollary 6's convention with C₀ = 1, counting one field parse as one word probe, so a lower estimate of the literal Q), the crossover lies between 2^20 and 2^22, with ratios 0.726 and 1.527.
- *Formula and measurement.* The per-cut side is a formula, a lower bound, at every size. The bank side is the bound 6 + w_b(3 + 4m/h); the measured banks of one random permutation per size, for m ≤ 2^20, are about half of it.

## 4. The shared-bank version of Corollary 6, and the trade-off for the runs of P_main and P_first

**Proposition (immediate from Corollary 6).** Fix the format before f is chosen: the evaluator, the degree and D*. Let Q be the number of distinct values of f used to decode one word. Corollary 6 is stated with Q = C₀·E·w′·K_d(D*), but its proof uses only this distinct count, because Proposition 5 counts distinct positions. For the landmark evaluator the w′ bit calls of one word repeat one decode, so Q ≤ h. Corollary 6 counts any bank shared by all rows in each cut's advice, together with the cut index and length fields, which is O(log m) bits beyond |Z_f|; write s(Z_f) for the total. Then:
1. **Worst case (part 1).** If every permutation file has such a chart, with a cut at a phase-2 head y ≤ m/2, and s(Z_f) ≤ s for all f, then (s + 2)(Q + 1) > m/2.
2. **Almost all (part 2).** For t = ⌊m/(4(Q+1))⌋, all but an m·2^{1−t} fraction of the permutation files have s(Z_f) > t.

The bound is for the worst file, or for almost every file, not for every file: the identity permutation has K = 0, and its bank has a few dozen bits.

The landmark chart has Q ≤ h and |Z| ≤ 6 + w_b(3 + 4m/h), so (|Z|+2)(Q+1) ≤ (1+o(1))·4·w_b·m. It therefore meets the bound within a factor 8w_b = O(log m) at every cut simultaneously, with Q counted as distinct values of f. With Corollary 6's literal Q = C₀·E·w′ the factor is O(log² m). No lower bound on (|Z|+2)(Q+1) larger than O(m log m) can hold for the runs of P_main and P_first on this family, because the chart attains that value.

**The trade-off in the seed note's accounting** (degree 0; worst permutation, or all but an m·2^{1−t} fraction). The note charges R ≥ q·E. Let g be the longest gap among the phase-2 cuts with y ≤ m/2. That gap reads g distinct forced words, so R ≥ g·w′·E = g·Q/C₀ with Q = C₀·E·w′. Corollary 6 gives |Z| ≳ m/Q, and that half of phase 2 holds at least m/(2g) cuts. Write the description length as m^u and R as m^v; up to polylogarithmic factors, N = m.

| Format | Lower bound | Attained by the landmark chart at | Exact value in the note's accounting |
|---|---|---|---|
| Any degree-0 chart that cuts at loop heads (note's accounting R ≥ q·E; worst permutation, or all but an m·2^{1−t} fraction) | u + v ≥ 1 | — | — |
| Cut list (times, controllers) written explicitly, as the persistent-query note pays for boundaries (its PL term) | the list costs ≥ 2m/g words, so max(u,v) ≥ max(1 − b, 1 − δ, b + δ) for g = m^b, Q = m^δ, which is at least 2/3 | g = h = m^{1/3} | max(u,v) = 2/3 |
| Controllers computed by the evaluator | max(u,v) ≥ 1/2 | g = 1, h = m^{1/2} | max(u,v) = 1/2 |

With unequal gaps, take b from the longest phase-2 gap and δ from the smallest per-row Q; the three inequalities still hold. So g = m^{1/3} is forced only by an explicit cut list, and for these runs both exponents lie below 1 in either format. The explicit-cut-list row reads the persistent-query note's boundary charge by analogy; the signed-window note, where Claim L's recurrence lives, was not opened. [Persistent queries](persistent-snapshot-query-cost.md)

**Effect on Claim L: none.** Claim L asks for max(u,v) < 1 for every near-linear UNSAT signaler, and given the borrowed recurrence it restates the exclusion. For the runs of P_first (rejecting runs) as well as those of P_main (accepting runs), the shared-bank requirement is met with u = v = 2/3 even with an explicit cut list. This is asymptotic: at m = 32768 the description is 3·10⁵ bits against N = 1.2·10⁷, and R_max over the run length is 0.40. For these runs the family therefore excludes per-cut advice and polylogarithmic decoders, as the seed note says, and nothing more.

## 5. The three standard tests

No lower bound is claimed; the result is an upper bound on describing one program's memory.
- **(a) A fast globally correct solver on the family?** Yes: P itself, and the mark pass, decide it in O(N). The chart is consistent with that.
- **(b) The same statement for a trivially easy language?** Yes. The files are 1-CNF in width-three dress, and the chart depends only on P's loops.
- **(c) Does it survive the oracle of the relativized-clock note?** Yes. P makes no oracle query, and the decode lemma and the counting are oracle-free. [Relativized clock](relativized-clock.md)

## 6. Exact obstruction and next step

- **The failed statement.** "The runs of the seed note's P on the main family, or of the scatter program on the first family, refute shared-bank charts" is false. Its precise form, "(|Z|+2)(Q+1) ≥ m^{1+ε}" or "u + v ≥ 1 + ε", fails because the landmark chart attains (|Z|+2)(Q+1) = O(m log m) at every cut simultaneously. The same is expected, but not proved, for any family whose forced memory is the inverse of a permutation with cheap forward access to the input, or of a composition of a constant number of such permutations (landmarks on the composed cycle).
- **What a refutation on some easy family would need.** A linear-time program whose forced memory at some cut is a table T(x) such that every shared advice string Z with an evaluator of Q input probes per word satisfies |Z|·Q ≥ N^{1+ε}, or |Z| ≥ N^{1−o(1)} whenever Q ≤ N^{1−ε}. That is a lower bound of the form redundancy × query time ≫ N, for a systematic static data structure on an explicit table. Recalled, not checked at source: the known bounds of this shape give r·t = Ω(n) (Gál–Miltersen, which the persistent-query note cites), and for function inversion a result of Corrigan-Gibbs and Kogan (2019) says that improving S·T ≥ N in a non-adaptive setting would give new circuit lower bounds.
- **Next lemma.** Find, or rule out, an easy family with a linear-time program whose forced table is not a permutation inverse, and prove such a lower bound for it. Short of that, barrier (d) reads: per-cut advice is refuted (Corollary 6); shared-bank charts are not refuted by the seed note's runs; and for those runs, in the note's accounting and for charts that cut at loop heads, the optimal shared-bank exponents are 2/3 with an explicit cut list and 1/2 without one. Another linear-time program on the same files is not addressed.

## 7. What is not proved

- No time lower bound of any kind, and nothing about Claim L beyond "the runs of P_main and P_first do not refute it".
- **Scope.** Only the runs of P_main and P_first are charted. Another program that is linear-time on the same files, and whose runs might have no short shared-bank chart, is not addressed. That is the open part of barrier (d).
- **Model.** Everything is instruction-level only for the two loops. The DIMACS parse is one input read per row rather than the digit-by-digit parse on an actual word RAM. The layout check that precedes the loops, and P_main's fallback (the mark pass), are not charted. The evaluator generates and probes the file byte by byte, but the machine itself reads parsed values. That the register program equals the seed note's P is checked only on all maps at m ≤ 4. The parse registers are expected to be file-computable stale values, as A is, but this is not written out.
- **Proved versus checked.** The decode lemma, the snapshot formulas and the soundness for all m are manuscript proofs, checked exhaustively only at the sizes in Section 3. The scale rows check one random permutation each, on a sampled coordinate set.
- **Lower bounds in Section 4.** These are in the note's accounting (R ≥ q·E with E the per-call cap) and written only for degree 0. For d ≥ 1 the upper bound applies verbatim, since a degree-0 chart is a degree-d chart, but the lower bound's extension is not written out.
- **Constants.** The O(log m) tightness factor and the crossover sizes depend on the cost model: one step per file byte, per bank field and per walk step.
- **Borrowed.** Corollary 6 and Lemma 2 are borrowed from the seed note, and its recurrence is not re-derived. The literature remark in Section 6 is unverified.

## Reproducing the checks

Run from `audits/`. Without an argument the chart checker runs a smoke test (the exhaustive check at m = 2 and 4, about a second); the modes below run the full checks.

```
python3 landmark_shared_bank_chart_check.py exhaustive
python3 landmark_shared_bank_chart_check.py mutation
python3 landmark_shared_bank_chart_check.py scale 64 512 4096 32768
python3 landmark_shared_bank_chart_check.py scale1 64 512 4096
python3 landmark_decode_probe_bound_check.py
python3 landmark_register_program_equivalence_check.py
python3 landmark_bank_per_cut_crossover.py
```

The modes take about 3 minutes, 45 seconds, 45 seconds and 2½ minutes; the other three scripts take at most 15 seconds each.
