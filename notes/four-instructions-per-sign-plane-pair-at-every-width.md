# Four instructions per sign-plane pair at every width, with a matching lower bound only for one and two pairs

On the word-aligned sign-plane catalog with j words per sign plane (k = 2j input words of w bits), one explicit program decides every file within 4j+1 = 2k+1 executed instructions of the native RAM, at every width w and every j. This upper bound is kernel-checked in Lean 4.19 for all (w, j), including equivalence with existence of a satisfying assignment, and it is checked on every input at ten sizes, up to 2^30 inputs. The matching lower bound is known only at j = 1 (w = 2, 3 and 5 from the journal; **w = 4 new here**, from the journal's exhaustive native search, which also re-derives w = 5 independently) and at j = 2 (w = 4, 5, from the journal's censuses). For j ≥ 3 the value 4j+1 is a conjecture, and only the trivial bound T ≥ 2j+1 is proved; the missing step is the leaf-capacity lemma Cap(w, j) of Section 6. For the physical-word reading "2k+1 for k words" the journal already has a counterexample at k = 5 (Section 3.1). All of this concerns exact finite clocks with unrestricted program text on a family that has a scan-time solver, so even a full proof of the rule would have no running-time consequence for SAT. The linear, quadratic and cubic questions remain open.

**A linear rule cannot reach a superlinear target, for two independent reasons.**
- T(w, j) is a minimum over programs with unrestricted text chosen separately at each length. By Theorem 1 of the ceiling note, every predicate on W words has such a clock at most N + W = N + N/w. Leaf capacities, marked trees and exact clocks are size-oblivious arguments, so they can never certify more than that, on any family. [Ceiling of the unbounded-code clock](the-ceiling-of-the-unbounded-code-clock.md)
- This family also has a globally correct solver running in (2/w)n + 1 instructions. No argument on it can certify more than Θ(n/log n).

Even a full proof of the rule would only finish the exact-clock census line for this one family. It gives a C → C+1 step along input length, not along program size.

## 1. The family, the machine and the conjecture

**Family F(w, j)**, for w ≥ 2 and 1 ≤ j with 2jw ≤ 2^w. The formula has V = jw variables x_1..x_V. The input is 2j words of w bits. P_i is at address i, for i < j, and holds the positive-unit mask of variables iw+1..iw+w. M_i is at address j+i and holds the negative-unit mask of the same variables. The formula is the selected unit clauses plus the fixed clause (x_1 ∨ … ∨ x_V), which can be written as a fixed 3-CNF OR-chain with no per-instance selectors. The machine is the journal's native RAM of width w: [Machine convention](exact-clocks-for-two-word-sat-inputs.md)
- 2^w words of memory; scratch and registers start at zero; unrestricted code and registers;
- all w-bit immediates; direct or register-indirect loads and stores;
- the twenty binary operations of [native_four_bit_planes.hpp](../audits/native_four_bit_planes.hpp), taken at width w (shift counts saturating or reduced mod w, as in [split_word_sat_adaptive_audit.py](../audits/split_word_sat_adaptive_audit.py));
- equality, unsigned and signed comparison branches;
- each instruction costs 1, and fixed verdicts are free.

T(w, j) is the minimum, over all correct programs, of the worst-case number of executed instructions. The journal's tight-length convention w = ⌈log2 n⌉, with n = 2jw selector bits, picks out the sub-sequence (2,1), (3,1), (4,2), (5,2), (5,3), (6,3), (6,4), (6,5), …

**Conjecture.** T(w, j) = 4j + 1 for every w ≥ 2 and 1 ≤ j ≤ 2^(w−1)/w. The restriction w ≥ 2 is needed: at w = 1 the journal's clock is 2 (load M and test it for zero), not 5.

**Semantics (proved for all w, j).** F(w, j) is satisfiable ⇔ P_i & M_i = 0 for all i, and M_i ≠ 2^w − 1 for some i.
- (⇒) A satisfying assignment obeys every unit, so no variable carries both units. The long clause needs a true variable, and that variable carries no negative unit.
- (⇐) Set x = ¬M bitwise. The positive units hold because P_i ⊆ ¬M_i. The negative units hold trivially. The long clause holds because some bit of M is 0.

## 2. Upper bound for every (w, j): kernel-checked, and checked on every input at ten sizes

Program U_j processes the pairs in order, with the flag "every M seen so far is all-ones" still pending:
- load M_i, then branch on M_i = ones;
- if M_i = ones and i is the last pair, reject;
- if M_i = ones and i is not last, load P_i, reject unless P_i = 0, and continue with pair i+1 (4 instructions per such pair);
- otherwise load P_i, AND it with M_i and reject on a nonzero result. Then, for each later pair, load P, load M, AND, and test for zero (4 each). Accept.

**Proof of the count.** Let U(i) be the worst case from pair i. Then U(j−1) = 5 and U(i) = max(4 + U(i+1), 5 + 4(j−1−i)), so U(i) = 5 + 4(j−1−i) by induction, and U(0) = 4j + 1. Correctness is the semantic equivalence above. On the branch M_i = ones, P_i & M_i = 0 ⇔ P_i = 0.

**Kernel check for all w, j.** [PairSelectorUpper.lean](../lean/PairSelectorUpper.lean) uses the journal's instruction semantics: load, AND and equality branch cost 1 each, and terminals are free. It proves `correct_and_bounded`: for every width w, every j and every memory f, the program accepts ⇔ an assignment exists (`hasModel`), and it executes at most 4j + 1 instructions. The Lean memory is indexed by natural numbers, and the `Code` type would allow free dispatch inside a continuation. The theorem is a native-RAM statement because this program loads only from the literal addresses i and j+i, below 2j ≤ 2^w whenever 2jw ≤ 2^w, and uses loaded values only as operands of AND and equality branches. The journal's [NineStepSelectorUpper.lean](../lean/NineStepSelectorUpper.lean) uses the same convention. The semantic equivalence is proved bitwise for general w.

The kernel-checked program is a slight variant of U_j. On the last pair, if M = ones, it still loads P and branches on P = 0 before rejecting, where U_j and the C interpreter reject at once. That path costs 4j ≤ 4j + 1, so the worst case is unchanged. To make the C check and the kernel check cover the same program, the interpreter run with `LEAN_VARIANT=1` executes this exact Lean program. It passes all ten sizes of the table below with zero mismatches and maximum 4j + 1. Only the histogram entry of the last-pair all-ones path moves, by two steps: for example `2:4` becomes `4:4` at (2,1), `6:16` becomes `8:16` at (4,2), and `10:32` becomes `12:32` at (5,3). Two further theorems show the bound is attained. `attained_nine` gives a run of exactly 9 steps on (4,4,11,11) at (w, j) = (4, 2), and `attained_thirteen` gives 13 steps on the all-zero memory at (5, 3). Both are proved by `decide`, with axioms propext and Quot.sound.

```
$ lean PairSelectorUpper.lean        # Lean 4.19.0, Std only
'PairSelectorUpper.correct_and_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'PairSelectorUpper.attained_nine' depends on axioms: [propext, Quot.sound]
'PairSelectorUpper.attained_thirteen' depends on axioms: [propext, Quot.sound]
```

**Exhaustive check.** [sign_plane_pairs_upper_check.cpp](../audits/sign_plane_pairs_upper_check.cpp) interprets U_j instruction by instruction and counts every executed instruction. On every input it checks the verdict against the closed form, and against a brute-force search over all 2^(jw) assignments when jw ≤ 10. The source is plain C that also compiles as C++. Compile it with `c++ -O2 sign_plane_pairs_upper_check.cpp -o /tmp/sign-plane-pairs` and run `/tmp/sign-plane-pairs W J`; `JOURNAL_ORDER=1 /tmp/sign-plane-pairs 4 2` runs the journal's own instruction order, and `LEAN_VARIANT=1` the Lean program.

| (w, j) | inputs | satisfiable | mismatches (closed form / brute force) | max steps | histogram |
|---|---:|---:|---|---:|---|
| (2,1) | 16 | 8 | 0 / 0 | 5 | 2:4 5:12 |
| (3,1) | 64 | 26 | 0 / 0 | 5 | 2:8 5:56 |
| (4,1) | 256 | 80 | 0 / 0 | 5 | 2:16 5:240 |
| (5,1) | 1,024 | 242 | 0 / 0 | 5 | 2:32 5:992 |
| (6,1) | 4,096 | 728 | 0 / 0 | 5 | 2:64 5:4032 |
| (7,1) | 16,384 | 2,186 | 0 / 0 | 5 | 2:128 5:16256 |
| (4,2) | 65,536 | 6,560 | 0 / 0 | 9 | 4:3840 5:40960 6:16 9:20720 |
| (5,2) | 1,048,576 | 59,048 | 0 / 0 | 9 | 4:31744 5:768000 6:32 9:248800 |
| (6,2) | 16,777,216 | 531,440 | 0 / (skipped, jw=12) | 9 | 4:258048 5:13533184 6:64 9:2985920 |
| (5,3) | 1,073,741,824 | 14,348,906 | 0 / (skipped, jw=15) | **13** | 4:32505856 5:786432000 8:31744 9:194306048 10:32 13:60466144 |

The satisfiable counts equal 3^(jw) − 1 in every row, as they must: each variable has none/positive/negative, and only the all-negative choice fails. The (5,3) run takes about half a minute on one core.

**Interpreter calibration.** With `JOURNAL_ORDER=1` the interpreter runs the journal's nine-step program from [NineStepSelectorUpper.lean](../lean/NineStepSelectorUpper.lean). It reproduces the journal's histogram exactly, `histogram: 4:256 5:40960 6:3600 9:20720`, the distribution recorded with the seed-interval audit. [Recorded histogram](checking-an-interval-against-a-seed-of-unknown-bits.md)

The tight-length points (6,3), (6,4) and (6,5) are covered by the Lean proof only. They have 2^36 to 2^60 inputs, which is not enumerable at this scale.

## 3. Lower bound: what is known, what is new, what is open

### 3.1 The physical-word reading is already false at k = 5

The journal's consecutive-length catalog at 21 selector bits occupies five physical words. Its fifth word holds one bit. It is decided in at most 9 < 2·5+1 instructions, kernel-checked in [FifthSelectorWordUpper.lean](../lean/FifthSelectorWordUpper.lean). So the rule cannot count every occupied physical word. The remaining candidate is 4j + 1 for j word-aligned pairs. The conjecture states it for complete pairs, and the journal's exact clock 9 on the 17-, 18- and 19-selector word-aligned layouts at w = 5 (partly filled words) is consistent with the same form for partly filled pairs (last paragraph of the five-bit cross-pair note; first paragraph of the twenty-bit note). [Fifth word](the-first-fifth-word-does-not-increase-the-nine-step-upper-bound.md) · [Five-bit cross-pair read](forcing-an-early-cross-pair-read-at-five-bit-width.md) · [Twenty bits](nine-steps-at-twenty-tightly-packed-selector-bits.md)

### 3.2 Exact values already in the journal

- T(2,1) = T(3,1) = 5: exhaustive search, [split_word_sat_adaptive_audit.py](../audits/split_word_sat_adaptive_audit.py).
- T(5,1) = 5, even with arbitrary fixed contents in every other cell and register: the one-live-pair theorem, row "Five raw bits per mask". [Five-bit cross-pair read](forcing-an-early-cross-pair-read-at-five-bit-width.md)
- T(4,2) = 9. [Exact nine](exact-nine-step-clock-for-four-sat-words.md)
- T(5,2) = 9. [Twenty bits](nine-steps-at-twenty-tightly-packed-selector-bits.md)

All five values agree with 4j + 1.

### 3.3 Exact values at j = 1 (one pair, k = 2), all programs of the native model: w = 4 new, w = 5 re-derived

[one_sign_plane_pair_native_search.py](../audits/one_sign_plane_pair_native_search.py) imports the search of [split_word_sat_adaptive_audit.py](../audits/split_word_sat_adaptive_audit.py) unchanged and runs it at width w. That search's documented coverage is every ordering of loads and stores, direct and indirect addresses, the twenty operations, and the three comparison types with both outcomes. The script uses the pinned suite P ∈ {0..3}, M ∈ {2^w−4..2^w−1}, the analogue of the journal's six-bit suite. If no program is correct on the suite, none is correct on the whole catalog. The times in parentheses are from one run and vary.

```
$ python3 one_sign_plane_pair_native_search.py 3 4     # calibration: reproduces the journal
w=3 suite=16 inputs (P<4, M>=4) target_mask=0x35f steps<=4: program exists = False  (1.8s)
$ python3 one_sign_plane_pair_native_search.py 3 5
w=3 suite=16 inputs (P<4, M>=4) target_mask=0x35f steps<=5: program exists = True  (0.6s)
$ python3 one_sign_plane_pair_native_search.py 4 4
w=4 suite=16 inputs (P<4, M>=12) target_mask=0x35f steps<=4: program exists = False  (12.0s)
$ python3 one_sign_plane_pair_native_search.py 4 5
w=4 suite=16 inputs (P<4, M>=12) target_mask=0x35f steps<=5: program exists = True  (4.2s)
$ python3 one_sign_plane_pair_native_search.py 5 4
w=5 suite=16 inputs (P<4, M>=28) target_mask=0x35f steps<=4: program exists = False  (140.0s)
$ python3 one_sign_plane_pair_native_search.py 5 5     # positive control
w=5 suite=16 inputs (P<4, M>=28) target_mask=0x35f steps<=5: program exists = True  (18.9s)
```

**T(4,1) = 5 (new) and T(5,1) = 5 (re-derived; already a journal theorem with arbitrary advice).** In each case the upper bound is U_1 from Section 2. The points (4,1) and (5,1) lie outside the tight-length convention, since 2w bits would give a smaller width, but inside F(w, j). The w = 5 search with at most four steps peaks at about 4.8 GB of resident memory.

**w = 6: no result.** The same search at w = 6 with at most four steps grew past 7.3 GB of resident memory within about seven minutes and was stopped undecided. The memoised Python search does not fit an 8 GB memory limit at 64 literals. A stop at the memory limit is evidence neither way.

**No computation at j = 3 (k = 6), or on the five-word 21-bit file, was possible with the journal's tools.** The journal's other census script, [clocked_native_path.py](../audits/clocked_native_path.py), is hard-coded to four 4-bit words: `BITS = range(4)`, 16-bit codes, the (p,q,m,n) verdict and 4-bit rotations. It is also a library that synthesizes one accepting path of a fixed opcode shape per base input, which bounds pointwise clocks, not the global optimum. Running it at five or six words would need a rewrite of its word gadgets and a 2^30-file catalog, beyond an 8 GB memory limit. The unchanged Python search above is the only global tool that runs within that limit, and only at k = 2.

**Known exact values of T(w, j).** Every known value equals 4j + 1:

| (w, j) | T(w, j) | source |
|---|---:|---|
| (2,1) | 5 | journal |
| (3,1) | 5 | journal |
| (4,1) | 5 | new here |
| (5,1) | 5 | journal (five-bit one-live-pair theorem); re-derived here |
| (4,2) | 9 | journal census |
| (5,2) | 9 | journal census |

### 3.4 What is proved for every (w, j)

Only T(w, j) ≥ 2j + 1. Take a target with every pair complementary and P_i ∉ {0, ones}. Replacing any word by ones creates a conflict, so every word is pivotal. A correct run must read every original cell before overwriting it, and some comparison must follow the last fresh load. Everything between 2j + 1 and 4j + 1 is open for j ≥ 3.

A restriction argument does not transfer the j = 2 census to larger j in the layout above. Fixing pairs 2..j−1 moves M_0 and M_1 away from addresses 2 and 3, and the census is specific to its layout, because raw words 4..11 are chosen to point into scratch.

One structural fact does hold. In the interleaved layout with complemented negative masks, (P_0, N_0, P_1, N_1, …) with N_i = ¬M_i, F becomes "P_i ⊆ N_i for all i, and N ≠ 0". There the zero restriction of the last pair leaves memory, scratch and verdict identical to the (j−1)-pair catalog. Hence T′(w, j) ≥ T′(w, j−1), proved in one line. U_j carries over with 4j+1 steps by testing (P & N) = P and N = 0. That count is by the same induction; the program was not run separately. Restriction gives only this monotonicity, not the +4 per pair. A per-pair step would need a direct-sum theorem for native paths, and none is known.

## 4. Marked-tree arithmetic: the journal's capacities and the pattern 4, 8, 16, 32

[marked_tree_capacity_arithmetic.py](../audits/marked_tree_capacity_arithmetic.py) runs the recursion of [EightStepMarkedCapacity.lean](../lean/EightStepMarkedCapacity.lean), namely F_d = max(w_d, 2F_{d+1}) and E_d = F_{d+1} + E_{d+1}. The marked root covers E_0 = Σ_{d≥1} F_d.

```
journal k=4 caps (16-bit census): weights [36, 18, 8, 1]  marked-root capacity E_0=63  targets |S|=64  closes=True
journal k=4 caps (20-bit census): weights [18, 18, 8, 1]  marked-root capacity E_0=63  targets |S|=64  closes=True
Kraft pattern 64/2^c, k=4: weights [32, 16, 8, 4]  marked-root capacity E_0=60  targets |S|=64  closes=True
Kraft K=2: |S|=64 E_0=48 margin=16 (= |S| 2^-K = 16)
Kraft K=4: |S|=256 E_0=240 margin=16 (= |S| 2^-K = 16)
Kraft K=6: |S|=1024 E_0=1008 margin=16 (= |S| 2^-K = 16)
Kraft K=8: |S|=4096 E_0=4080 margin=16 (= |S| 2^-K = 16)
Kraft K=10: |S|=16384 E_0=16368 margin=16 (= |S| 2^-K = 16)
k=4: cap at depth 1 raised from 36 to 37 first gives E_0=64 >= 64
k=4: cap at depth 2 raised from 18 to 19 first gives E_0=66 >= 64
k=4: cap at depth 3 raised from 8 to 9 first gives E_0=64 >= 64
k=4: cap at depth 4 raised from 1 to 2 first gives E_0=64 >= 64
```

**Where the pattern 4, 8, 16, 32 comes from.** It is a real journal quantity, but a different one from the full-model table.
- The four-word coupling note states the Kraft criterion. If every sound accepting path with c comparisons covers at most 64/2^c targets, then 64 targets cannot all be accepted, because one rejecting leaf has positive Kraft weight. [Coupling four-word paths](coupling-four-word-native-sat-paths.md)
- The direct-addressing note uses the upper bounds 4 and 8 for c = 4, 3, from the census of the coupling note, and proves the upper bounds 16 and 32 for c = 2, 1 in the **direct-addressing submodel**, where every load and store address is a literal along the path. The c = 1, 2 bounds come from its 90,388,089 and 58,578,564 arithmetic/literal assignments. [Direct addressing](nine-steps-for-direct-addressing-on-four-sat-words.md)

**Why the full model needs the marked tree instead.** With value-dependent addresses the journal's census proves only (36, 18, 8, 1).
- The c = 4 cap tightens from 4 to 1.
- The c = 1 and c = 2 caps, 36 > 32 and 18 > 16, exceed the Kraft values. So the full-model proof uses the marked-tree recurrence. It closes with a margin of one target, and no cap in (36, 18, 8, 1) has slack in the recurrence: raising any one by 1 gives E_0 ≥ 64. Here "tight" concerns the arithmetic, not attainment. In the 20-bit list (18, 18, 8, 1) the depth-1 cap can rise to 36 without changing E_0 = 63.
- The journal does not decide whether 36 or 18 is attained. The largest attained single-leaf support found is 16, at c = 2: the eight-step path of the seven-step cohort note. That is consistent with Kraft. [Seven-step cohort](which-four-word-sat-targets-finish-in-seven-steps.md)

So 4, 8, 16, 32 are upper bounds proved for direct addressing, and (36, 18, 8, 1) are upper bounds for arbitrary addressing. They are bounds of two different models, not a conflict.

**Capacity pattern, stated as a conjecture (direct-address submodel).** For every (w, j) ≠ (2, 1) in the family and every c ≤ 2j, with S_j the target set of Section 6 (|S_j| = (2^w − 4j)^j), a sound accepting path with c comparisons within 4j instructions covers at most |S_j|·2^(−c) targets. The exclusion is needed: at c = 2j, 2j fresh loads and 2j literal-equality tests soundly accept one target, so the conjecture requires |S_j| ≥ 4^j, that is 2^w ≥ 4j + 4. This fails only at (2, 1).
- By the Kraft argument above this gives T_direct(w, j) ≥ 4j + 1 for every j.
- The evidence is a single data point, (w, j) = (4, 2), in the journal's direct census. Its conclusion agrees with the j = 1 clocks at w = 3, 4, 5; the caps themselves were not checked at j = 1.

**Capacity pattern (full model).** The one data point j = 2 has two different cap lists, (36, 18, 8, 1) at 16 bits and (18, 18, 8, 1) at 20 bits, valid when the first comparison precedes the deadline, plus a separate exclusion at the deadline. Both are upper bounds only. They support no specific pattern beyond the existence statement Cap(w, j) of Section 6.

## 5. Three standard tests

- **(a) Fast globally correct solver on the hard family?** Yes. U_j decides all of F(w, j) in 4j + 1 = (2/w)·n + 1 instructions, about twice the number of input words, and the conjectured lower bound *equals* that solver's clock. No argument on this family can exceed the word-scan scale Θ(n/log n). Independently of the family, every exact unrestricted-code clock is at most N + N/w (ceiling note, Theorem 1). On a DIMACS presentation of the same formulas the input-reading cost alone dominates.
- **(b) Same bound for a trivially easy language?** Yes. F(w, j) is itself trivially easy, a bitwise check. The argument, pivotality plus leaf capacities plus one marked negative, never uses NP-hardness. It is expected to apply in the same way to the unit-clause (1-CNF ⊂ 2-SAT) sublanguage "all units consistent", whose natural program costs 4j (OR of ANDs, then a zero test); nothing was run or proved for that sublanguage. What the argument measures is the binary fan-in of native instructions, not SAT. The ceiling note's Theorem 1 also applies to 2-SAT, parity and constants.
- **(c) Relativized-clock oracle?** The test passes vacuously. A (2k+1) = O(N/log N) bound is consistent with the linear-time SAT oracle world (p = 1), so relativization cannot refute it, and for the same reason the bound cannot separate anything. It uses the property that this oracle model shows every proof must use, that one instruction reads O(w) bits: pivotal words need individual loads, and operations have fan-in two. But it uses that property only to count to a constant per word. [Relativized clock](relativized-clock.md)

## 6. Exact obstruction and next step

The missing statement is the capacity lemma.

**Cap(w, j).** There are integers w_1, …, w_{2j} with Σ_{d=1}^{2j} max_{e≥d} 2^(e−d)·w_e < |S_j|, such that every accepting leaf reached by a target of S_j within 4j instructions, with d comparisons on its path, contains at most w_d targets. Here S_j is a complementary-pair target set whose raw values avoid the input addresses and the all-ones word, for example p ∈ [2j, 2^w−1−2j].

Given Cap(w, j), the journal's reductions give T(w, j) ≥ 4j + 1: pivotality forces 2j fresh loads, so d ≤ 2j, and the Lean marked-tree recurrence finishes the argument. The journal proved Cap(4,2) by census, with caps (36, 18, 8, 1). At (5,2) it proved T(5,2) ≥ 9 by the same scheme with a case split: caps (18, 18, 8, 1) when the first comparison precedes instruction eight, and a separate census showing that no comparison at the deadline accepts all 64 targets. The one-comparison case at j = 2 alone needed 202,695,726 (16-bit) and 908,907,086 (20-bit) first-table/second-operation pairs, plus manuscript reductions for stores and indirect addresses. At j = 3 a one-comparison leaf carries five arithmetic operations instead of three, so the census does not scale. No structural proof of any w_d for general j is known.

A cheaper intermediate target is the direct-address Kraft conjecture of Section 4 for general j, which would give T_direct(w, j) ≥ 4j + 1. Toward it, in the direct-address, store-free submodel, the following pinning lemma holds. Its j = 2 factored case is in the coupling note; the component form for general j is new here. [Coupling four-word paths](coupling-four-word-native-sat-paths.md)

**Pinning lemma.** Make the input words vertices, and let each comparison on the path contribute a hyperedge: the set of words its operands depend on. If P_i and M_i lie in different connected components of this hypergraph, every target at that leaf, if the leaf is an accepting leaf of a correct program, has the same value of pair i. Proof: with direct addresses and no stores, each outcome is a function of its own words, so the leaf set is a product over components. Suppose two targets at the leaf carry values p ≠ p′ of pair i. The two hybrids that take one component from each target lie in the leaf and contain (p, ¬p′) and (p′, ¬p). One of these is a conflict, because p ⊄ p′ or p′ ⊄ p.

A further step, "each component needs at least as many non-load instructions as it has words", would give the pointwise bound 4j in that submodel. It still would not give the Kraft supports, and it is not proved here for the native operation set. The pointwise bound 4j is false in the full model: 32 of the journal's 64 targets at j = 2 finish in seven steps, through an indirect load at address q & n. [Seven-step cohort](which-four-word-sat-targets-finish-in-seven-steps.md)

The best possible output of this line is a constant of two instructions per word on a family with a matching scan solver. Every size-oblivious argument of this kind is capped at N + N/w on any family in any case.

## 7. What is not proved

- T(w, j) ≥ 4j + 1 for any j ≥ 3. The best proved lower bound on T(5,3) is the trivial 7 = 2j + 1, against the conjectured 13.
- Cap(w, j) for any j ≥ 3, and whether the k = 4 caps (36, 18, 8, 1) are attained.
- That the j = 1 search at w = 4 covers the model. This rests on the journal's documented coverage argument for its search code, not on a new proof. At w = 5 the value is independently a journal theorem.
- Anything about ordinary DIMACS SAT beyond the trivial: every statement here concerns a special encoding with a Θ(n/log n) solver.

## Reproducing the checks

Lean commands run from `lean/`; the others from `audits/`.

```
lean PairSelectorUpper.lean
c++ -O2 sign_plane_pairs_upper_check.cpp -o /tmp/sign-plane-pairs && /tmp/sign-plane-pairs 5 3
LEAN_VARIANT=1 /tmp/sign-plane-pairs 5 3
JOURNAL_ORDER=1 /tmp/sign-plane-pairs 4 2
python3 one_sign_plane_pair_native_search.py 4 4
python3 marked_tree_capacity_arithmetic.py
```

The interpreter takes the width and the number of pairs as arguments; the table rows are `/tmp/sign-plane-pairs W J` for each listed (w, j), and its exit status is 0 exactly when there is no mismatch and the maximum is 4j+1. The search takes the width and the step bound; without arguments it runs the w = 3 calibration. [PairSelectorUpper.lean](../lean/PairSelectorUpper.lean) · [sign_plane_pairs_upper_check.cpp](../audits/sign_plane_pairs_upper_check.cpp) · [one_sign_plane_pair_native_search.py](../audits/one_sign_plane_pair_native_search.py) · [marked_tree_capacity_arithmetic.py](../audits/marked_tree_capacity_arithmetic.py) · [Search machine](../audits/split_word_sat_adaptive_audit.py)
