# Five halves per word is tight on the single-edit suite: a fixed 14-instruction program meets 5m/2 + O(1)

On the single-edit suite of the five-halves note (the positive file F with m marked words, its m one-bit edits B and its m whitespace edits B′), a fixed program with 14 stored instructions, PAIR-HB, found during review, decides every file in 5m/2 + O(1) steps, on both the journal audit's layout and the manuscript's space-padded layout. The 5/2-per-word lower bound uses only correctness on that suite, so it is tight there, and no lift of that argument can pass 5/2. This sharpens the journal's upper bounds for that promise and contradicts nothing: the journal states (3+ε)m + o(m) for the one-bit promise and 3m + o(m) for its globally correct scan, and claims neither as optimal. The window [7/3, 5/2] stays open for the one-bit-only promise. PAIR-HB is suite-correct, not globally correct. All bounds here are constants per packed word, and the linear, quadratic and cubic questions remain open. [Five halves](generating-fresh-addresses-on-one-native-sat-file.md) · [One-bit promise](small-address-images-of-shifts-and-products.md)

Two further statements, each in a short section below: the program-size lift of the five-halves argument extends to every deadline K < 5/2, conditional on the manuscript 5/2 proof (Section 4); and a sum test caps every single-length suite of single-word edits at 3 steps per word, provided every edit flips the verdict (Section 5).

## 1. The machine, the suite and the two layouts

**Machine.** The separate-operation RAM of the five-instruction loop note: registers start at zero except the public N and w; LOAD and STORE take a register or an immediate as the full address; there are binary catalog operations; a branch compares two operands. [Five-instruction loops](five-instruction-loops-on-dimacs-sat.md)

**Step and size conventions.** The journal's convention (JNL) treats the two verdicts as terminals and gives each branch two fixed successors. The scripts' simulator (SIM) charges one step for the verdict and stores the two verdicts as instructions. JNL equals SIM minus one step, and the JNL size is two entries smaller. Figures below are JNL unless marked SIM; the scripts print SIM. [Sparse word edits](exact-executed-clocks-for-sparse-word-edits.md)

**Suite.** The 5/2 file F with m marked words A, its m one-bit replacements by B, and its m whitespace replacements by B′ (B′ ≡ A mod w): 2m+1 files of one length. At power-of-two widths B′ = B, so only the widths 33024 and 49152 test a distinct B′.

**Layouts.**
- **Audit layout:** prefix + A^m + a 7-byte trailer, exactly as built by the journal audits; the trailer is the last, partial word, and ⌈n/w⌉ = m + 2. [fresh_native_address_audit.py](../audits/fresh_native_address_audit.py) · [dimacs_whitespace_residue_audit.py](../audits/dimacs_whitespace_residue_audit.py)
- **Padded layout:** the manuscript's F_N, with m = ⌊N/w⌋ − c and the remaining bytes filled with spaces, placed before the trailer digit or after its newline. Runs used the padding count c ∈ {2, 3, 4, 6} and r ∈ {0, 7, 100} extra bytes. (The letter C is kept for the program-size budget below.)

## 2. PAIR and PAIR-HB

**PAIR** compares adjacent marked words in pairs: loop `p+=1; u=M[p]; p+=1; v=M[p]; if u==v loop`; on exit it accepts iff v = 0, or the next word is 0 and u equals the first marked word. It has 11 stored instructions (JNL) when the public prefix is one word (`first = 1`, as at every width run); a longer prefix adds one `mov`. On the audit layout it decides every suite file in 5m/2 + 7 steps for even m and 5m/2 + 8.5 for odd m. It is correct whenever there are m ≥ 2 equal marked words, then exactly one trailer word T ∉ {0, A}, then zero words, under single-word replacements by words ∉ {0, T}; on the audit layout every ASCII replacement word satisfies this. On the padded layout PAIR rejects the satisfiable base on most layouts: it is wrong somewhere on 546 of the 648 padded layouts run, and in the failing layouts sampled during review the base was the only misclassified file.

**PAIR-HB** (found during review in an independent interpreter, re-encoded in the scripts here) keeps PAIR's loop and changes the exit test. It accepts iff the high byte of v is neither '4' nor '5', and either u = x1 (the first marked word) or the high byte of u is neither '4' nor '5'. It uses the public w to compute the shift and has 14 stored instructions at `first = 1` (one more otherwise). Why it works for any placement of the space padding:
- every marked or edited word has '4' or '5' as its high byte, and no trailer word does (their high bytes are space, newline, a digit of the trailer, or zero padding);
- a word holding a trailer byte never equals its pair partner, so the loop halts no later than that pair;
- an edit inside the block makes its pair unequal with v or u marked, so the test rejects. For odd m an edit to the last word fails u = x1 (this needs m ≥ 3), and an edit to word 0 exits at the first pair with v = A.

The runs confirm this on both layouts; other placements of the padding rest on this argument.

## 3. Runs and the tightness statement

`python3 pair_hb_both_layouts_check.py` (about 30 s) runs PAIR-HB and PAIR on every file of the audit layout and of 24 padded layouts per (w, m), at w ∈ {32768, 33024, 49152} and m ∈ {2, 3, 6, 7, 11, 40, 41, 300, 301}; the SAT status of every file is checked by enumeration for m ≤ 11. Its summary lines (SIM): [pair_hb_both_layouts_check.py](../audits/pair_hb_both_layouts_check.py)

```
675 layout runs; PAIR-HB correct on all; worst max T(SIM)-5m/2: audit +15.0, padded +25.0 (JNL: one less)
PAIR wrong somewhere on 0/27 audit layouts, 546/648 padded layouts
PAIR-HB size: 16 entries = 14 stored instructions + 2 verdicts (first=1)
```

So PAIR-HB decides every file of every layout run within 5m/2 + 24 steps (JNL; 5m/2 + 14 on the audit layout). The extra passes over all-space tail words cost O(c).

**Base-file steps on the audit layout** (SIM; JNL is one less), from `python3 pair_scan_suite_calibration.py 120 121 300 301` and identical at the three widths run (abridged to w = 32768, m = 300 and 301): [pair_scan_suite_calibration.py](../audits/pair_scan_suite_calibration.py)

```
width m first | PAIR steps(base) 5m/2 diff | HYB j instr steps saved/instr | CHK k steps 3m+m/k
32768 300 1 | PAIR 758 750.0 +8.0 (size 13) | j=0:C=13,T=758,r=0.000 j=37:C=125,T=685,r=0.652 j=75:C=239,T=609,r=0.659 j=149:C=461,T=461,r=0.663 | CHK k=4 T=977 3m+m/k=975.0 (size 16)
32768 301 1 | PAIR 762 752.5 +9.5 (size 13) | j=0:C=13,T=762,r=0.000 j=37:C=125,T=689,r=0.652 j=75:C=239,T=613,r=0.659 j=149:C=461,T=465,r=0.663 | CHK k=4 T=980 3m+m/k=978.2 (size 19)
```

The `size 13` is the SIM size; it is 11 stored instructions under JNL.

**Tightness.**
- On the audit layout (⌈n/w⌉ = m + 2), for every K > 5/2 and m ≥ max(2, 8.5/(K − 5/2)), PAIR meets K⌈n/w⌉ on the whole suite. On the padded layout PAIR-HB does the same for all large m.
- So no lift of the five-halves argument exists above 5/2 on this suite once the program-size budget C is at least the size of that fixed program: 11 stored instructions on the audit layout, 14 for the padded variant.
- PAIR uses m loads, m first productions, and m/2 branches that each receive two charges: exactly the 5/2 count. The theorem's proof uses only correctness on F and the B′ edits, so it is tight on this promise.
- Whether some fixed program meets K = 5/2 exactly was not decided; PAIR misses it by a constant.

**Relation to the journal's figures.** The journal states (3+ε)m + o(m) for the one-bit promise (the last paragraph of the small-address note) and 3m + o(m) for a globally correct scan (the five-halves note), and claims neither as optimal. PAIR, and PAIR-HB on the padded layout, are correct on both kinds of edit. They sharpen the promise bound to 5m/2 + O(1), which matches the 5/2 lower bound for the whitespace edits; nothing in the journal is contradicted. The window [7/3, 5/2] stays open for the one-bit-only promise. No pair-comparison program or 5/2 upper bound was found in the notes.

**Not globally correct.** Both programs accept an unsatisfiable file in which both words of one pair are replaced by B, because an equal pair keeps the loop going. For PAIR, `python3 pair_scan_variants.py` prints: [pair_scan_variants.py](../audits/pair_scan_variants.py)

```
two-edit file (pair 1,2 both B) w=32768 m=6: sat=False, PAIR verdict=True -> PAIR WRONG (expected: suite-correct only)
two-edit file (pair 1,2 both B) w=32768 m=7: sat=False, PAIR verdict=False -> ok
two-edit file (pair 1,2 both B) w=32768 m=40: sat=False, PAIR verdict=True -> PAIR WRONG (expected: suite-correct only)
```

PAIR-HB keeps the same loop, so it accepts that file too; a separate check, not among the scripts linked here, confirmed this at m = 6 and 40. (At m = 7 PAIR rejects, by an accident of the odd-m exit test.) At m = 1 PAIR accepts the edited file. The 5/2 theorem for globally correct programs, with upper bound 3m + o(m), is untouched.

**Other families with o(m) instructions** (the constructive test, audit layout). `python3 pair_scan_unroll_and_shared_stride.py` and the calibration script run four families, every program correct on every suite file. Base steps at m = 300 and 301 (SIM): [pair_scan_unroll_and_shared_stride.py](../audits/pair_scan_unroll_and_shared_stride.py)

| family | stored instr. (JNL) | m = 300 | m = 301 |
|---|---|---|---|
| PAIR | 11 | 758 | 762 |
| UNROLL(k), k = 2, 4, 8 | 17, 27, 47 | 758 | 762 |
| SHARED(k), shared stride k, k = 2, 4, 8 | 17, 28, 50 | 764–766 | 768–770 |
| HYBRID(j): PAIR after j = 149 hardwired pairs | 459 | 461 | 465 |

Unrolling only replaces the back-edge by exit branches, still 5 steps per pair, and a shared stride still needs one address update per word. HYBRID saves 2/3 of a step per added instruction (measured 0.663), so it gets below K·m, for a fixed K < 5/2, only with C ≥ (3/2)(5/2 − K)m − O(1) = Θ(m) instructions. No family with o(m) instructions beats 5/2.

## 4. The program-size lift below 5/2 (conditional on the manuscript 5/2 proof)

**Lemma.** For every K < 5/2 there is m_0(K) such that, for every m ≥ m_0(K) and every program with at most C stored instructions that is correct on the suite, T(F) > K⌈n/w⌉ whenever (5/2 − K)m > 10C + e0 + 2K·b0. Here e0 is a machine-and-layout constant and b0 = ⌈n/w⌉ − m. Equivalently, one more instruction is compensated by ⌈10/(5/2 − K)⌉ more marked words: +20 at K = 2, +40 at K = 9/4. This extends the journal's lifts (K < 2 by address production, 2 + δ without raw predecessors), conditionally. [Address-production lift](address-production-and-a-program-size-lift.md) · [Without raw predecessors](addresses-without-raw-predecessors.md)

**Trace (a reading of the manuscript proof; the 5/2 proof itself is assumed, not re-proved).** The journal's Lean core is 5m ≤ 2T + sparse + 2·init. Split the stock of initially available values (literals, register initial values, zero, A and the public words) into S_I, the values inside the marked interval I, and S_out, the values outside it. Every term of `sparse` and `init` falls into one of five groups: [FirstGeneratedNativeAddresses.lean](../lean/FirstGeneratedNativeAddresses.lean)
1. **Exceptional values that depend only on the file:** small shift, rotation, AND and comparison outputs, and small products whose partners lie in the five intervals I, −I, near A, near −A and near 2A. They form a set Z determined by (w, A, ℓ, I) alone; each value's first producer receives at most 2 charges, so the contribution is ≤ 2z with z = |Z| = o(m), uniform over programs.
2. **Machine constants:** f(A,A), the exceptions to c(y) ≤ 1, and unary operations on A contribute ≤ c0, a constant of the instruction set.
3. **Preavailable partners y ∈ S_out:** each gets b(y) ≤ 2 generic address charges (shift and rotation counts get none, because B′ ≡ A mod w). Contribution ≤ 2|S_out|.
4. **Preavailable reserves z ∈ S_out:** a high-charge scalar whose reserve is preavailable cannot be booked and leaves one excess charge; each of the three reservation rules is injective, so at most 3 such scalars share one z (cross-rule disjointness in the manuscript gives 1, so this overcounts). Contribution ≤ 3|S_out|. Reserves inside I, and in the other four intervals, arise only in the product case; there the translated product estimate bounds the number of high-charge y = Az by a file-only o(m), and this count is added to z(m).
5. **init ≤ |S_I|.**

Hence sparse ≤ 2z + 5|S_out| + c0 and init ≤ |S_I|. With |S_I| + |S_out| ≤ 2C + d0 this gives 5m ≤ 2T + 2z + 10C + 5d0 + c0, that is **T ≥ 5m/2 − 5C − z(m) − e0/2** with e0 = 5d0 + c0. Absorbing z(m) ≤ (5/2 − K)m/2 for m ≥ m_0(K) gives the lemma. m_0(K) is not explicit: none of the o(m) terms in z(m) is explicit at realistic widths (the shift and rotation sets alone are about m·2^{−w/100000}), so m_0(K) is astronomically large.

**Lean.** [FiveHalvesLift.lean](../lean/FiveHalvesLift.lean) checks the arithmetic only: `traced` (from the journal's `five_halves` form and the four trace hypotheses to 5m ≤ 2T + 2z + 10C + 5d0 + c0), `fails_at_two` and `fails_at_nine_quarters` (the contradictions at K = 2 and K = 9/4 under m > 20C + 2e0 + 8b0, respectively m > 40C + 4e0 + 18b0), the successor steps +20 and +40, and a witness (m = 40, T = 90, z = 5, C = 1) showing that the 9/4 size condition cannot be weakened to 39C within this arithmetic. `lean FiveHalvesLift.lean` exits 0 with no output; the file has no sorry, axiom or native_decide.

## 5. A cap of 3 for single-length suites of single-word edits (sum test)

Take any base file at one length and any replacement words B_i ≠ A_i at arbitrary positions, **each of which flips the verdict** (true in the journal's suites). A single replacement changes the sum of all file words mod 2^w by B_i − A_i ≠ 0. So CHECKSUM, which adds the words k at a time and compares with a per-length literal S, has O(k) instructions and per-length literals (S, the start and the end address) and is suite-correct in (3 + 1/k)⌈n/w⌉ + O(k) steps. (The scripts' unrolled version appends a straight-line tail of m mod k copies, so its logged sizes range from 16 to 25; a k-aligned start with the extra words folded into S avoids this.) Hence for K > 3 no single-length suite of single-word edits supports the lift, and the lift's suites as formulated in the journal are single-length.

On a non-homogeneous base (the digit of each marked word varies), the sum test stays correct where PAIR fails; `python3 pair_scan_variants.py` prints, for example:

```
mixed base w=32768 m=300 (4 distinct marked words): PAIR wrong on 1/301 files; CHECKSUM(k=4) correct on all, base steps 977 (3m+m/4=975.0)
mixed base w=32768 m=301 (4 distinct marked words): PAIR wrong on 1/302 files; CHECKSUM(k=4) correct on all, base steps 980 (3m+m/4=978.2)
```

The cap does not cover a suite that spans more lengths than a size-C program has literals, on non-homogeneous bases: there a program must produce each length's checksum, or an equivalent summary, itself. A base family whose per-length checksum no small program can compute in o(m) steps would need a word-RAM lower bound of its own.

## 6. The three standard tests

- **(a)** The family has fast solvers: the journal's globally correct scan, and PAIR or PAIR-HB on the suite. All bounds are constants per packed word.
- **(b)** Ran: on a 2-CNF analogue (audit layout), PAIR is correct with the same step counts (for example `2-CNF suite w=32768 m=301: PAIR correct on 302 files, base steps 762 (5m/2=752.5)`). The test does not separate SAT from 2-SAT.
- **(c)** Argued only. The load count uses one-word reads. A bound at N/w scale is too weak to be contradicted by the oracle world of the relativized-clock note, whose solver spends Θ(n) word steps. [Relativized clock](relativized-clock.md)

## 7. Obstruction

On this suite the lift runs exactly up to 5/2, and on every single-length suite of single-word edits it is capped at 3. A lift to an unbounded cost per word, which the target needs, needs suites in which no O(1)-operation per-word summary separates the base from its edits: multi-word edits that cancel in every such summary, or multi-length suites with expensive checksums. Both are word-RAM lower bounds of the kind recorded as obstacle 2 of the barrier note (every hard family has a packed-scan solver). [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)

## 8. What is not proved

- The lower side below 5/2 is the journal's manuscript proof. The trace of its dependence on C, giving T ≥ 5m/2 − 5C − z(m) − e0/2, is a reading of that proof, not an independent proof; the runs only fail to find a counterexample.
- The families are explicit constructions, not a census.
- Correctness is checked only at the sizes and layouts run. PAIR-HB on other placements of the space padding rests on the short argument of Section 2.
- No fixed program meeting K = 5/2 exactly, and none beating 5/2 + O(1) on the one-bit-only promise, was searched for.
- The general correctness of PAIR (m ≥ 2) and of CHECKSUM is a short argument, not a formal proof.
- No literature was accessed.

## Reproducing the checks

Run from `audits/` (each command takes under 30 s); the Lean file from `lean/`.

```
python3 pair_hb_both_layouts_check.py
python3 pair_scan_suite_calibration.py 6 7 40 41
python3 pair_scan_suite_calibration.py 120 121 300 301
python3 pair_scan_unroll_and_shared_stride.py
python3 pair_scan_variants.py
lean FiveHalvesLift.lean
```
