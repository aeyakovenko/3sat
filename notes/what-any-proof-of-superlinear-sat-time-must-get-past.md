# What any proof of superlinear SAT time must get past: each barrier with its exact hypotheses

This note consolidates the journal's barriers to a proof that ordinary DIMACS SAT is not in linear time on the log-word RAM with one finite program. Each barrier is stated in its own model, and each statement was checked against its source note; Section 6 lists how much of each source was read. It is a consolidation only. The proofs in the source notes were **not** re-verified (their status, manuscript, Lean or audit, is copied from the sources), no lower bound is proved, and the linear, quadratic and cubic questions remain open. No known technique survives all of (a)–(e) by itself. Two combinations pass all of (a)–(g), on paper only (they meet none of these barriers; nothing more is claimed), and neither has been built:
- **A. Circuit route:** an explicit circuit lower bound above the threshold set by simulating a fixed RAM program with circuits (about N log² N with the known simulation). [Simulation threshold](simulating-a-ram-step-by-exact-networks.md)
- **B/C. Uniform route:** diagonalization plus a transfer step (a speedup or a succinct compiler). The step must be non-relativizing, and non-algebrizing in the packed-query interface, because it uses the fixed instruction set with O(w)-bit instructions (or, for sum-check steps, another escape the source names). It must also never store a whole memory snapshot.

A single merged barrier theorem would overclaim. The barriers are of two kinds, and they have to be stated separately:
- **(a), (b), (c) are counter-models.** In each, the analogue of the target is false, so every proof needs a step that fails there.
- **(d)–(g) are counterexamples to one method's key lemma.** They bind only proofs that go through that lemma. So does the speedup half of (c), which holds in the same world as the (c) counter-model.

## 1. The consolidated statement

Let Π be a purported proof that ordinary DIMACS SAT is not in DTIME_RAM(O(N)). The machine is the log-word unit-cost RAM with one finite program, unrestricted workspace and indirect addressing.

*Part I. Counter-models; every Π has a step that is false in each.*
- **(a)** RAM with unrestricted program text at each length: every predicate, SAT included, has a clock of at most N + ⌈N/w⌉.
- **(b)** Packed oracle RAM with the p = 1 recursive oracle: plain CNF SAT takes O(n) oracle steps.
- **(c)** Boolean oracle plus its multilinear extension: alternating linear time with extension queries collapses to deterministic linear time with the Boolean oracle, and SAT is O(n). In the same world, with queries through the packed contiguous-buffer interface, no o(n²) alternating speedup of DTIME[n²] exists. This second part binds only proofs that use such a speedup; it is listed here because it holds in the same world.

*Part II. Method counterexamples; they bind Π only if Π uses the lemma.*
- **(d) Checkpoints.** The conclusion that linear SAT forces hard snapshot windows (e + d < 1) is realized by a linear-time program on an easy family. Unconditionally, the technique has so far given only the time–space band.
- **(e) Proof systems.** On an explicit family, polynomial calculus (PC) over every field needs degree Ω(t) and size 2^{Ω(t)}, while one globally correct program runs in O(N/log N) word steps.
- **(f) Segregators.** A linear-time two-plane tape computation has a robust grate as its access graph.
- **(g) Capacity counts.** Per-path codimension measures are at most n − 1. The multiplicative-complexity form needs oblivious code.

The exact statements, their sources and the checks follow.

## 2. Each barrier in its own model

### (a) The unrestricted-text ceiling

- **Sources:** Theorems 1, 2 and the Corollary of the ceiling note, and the worst-labelling note. [Ceiling](the-ceiling-of-the-unbounded-code-clock.md) · [Worst labelling](worst-labelling-clock-with-unbounded-program-text.md)
- **Model (ceiling note):** the native RAM with word width w.
  - The input fills the first W ≤ 2^w of the 2^w words. Other memory and the registers start at zero.
  - Every w-bit literal is an immediate. A load, a store, one of the twenty word operations, or a binary comparison branch costs one step.
  - Program text is unrestricted, and verdicts are free. N = Ww.
- **Theorem 1:** every predicate on W words has clock at most W(w+1) = N + W.
- **Theorem 2:** for w ≥ 1, 1 ≤ W ≤ 2^w and an integer T ≥ 0 with T ≤ N − 1 − log₂(6 + 2 log₂(2N + 2^w)), at most a 2^{−2^{T+1}} fraction of predicates have clock at most T.
- **Corollary:** for every language and every N with ⌈N/w⌉ ≤ 2^w, the clock at length N, with the unused bits of the last word zero, is at most N + ⌈N/w⌉. The side condition ⌈N/w⌉ ≤ 2^w is part of the statement.
- **Sharper form (worst-labelling note):**
  - Model: the separate-operation RAM with fixed branch targets and w = Θ(log n). The program is chosen after n and the whole truth table.
  - D(n,w) = n + ⌈n/w⌉ − log₂ w + O(1) for large n.
  - About 2^n/n stored instructions suffice to attain this, and that order is necessary in the worst case.
- **SAT finite-horizon form (same note):**
  - With the public input length, for every horizon N there is **one globally correct** SAT program.
  - It runs within 7n/8 + O(⌈n/w⌉ + log(n+2)) steps on every well-formed ASCII formula of byte-aligned length n ≤ N.
  - It uses O(2^{7N/8}/N) stored instructions, and its constants do not depend on N.
- **Proof status (from the sources):**
  - The upper-bound programs are run by finite interpreters.
  - Lean checks only the prefix count 16·2^{T−⌊T/(w+1)⌋}. [ExecutedPrefixCount.lean](../lean/ExecutedPrefixCount.lean)
  - The normalization and the minimax conclusion are manuscript arguments.
- **Check run here.** An independent reimplementation of the counting inequality (not the journal's audit), `python3 unbounded_code_floor_recheck.py`, prints: [unbounded_code_floor_recheck.py](../audits/unbounded_code_floor_recheck.py)

  ```
  W= 4 w= 4 N=   16  ceiling W(w+1)=   20  closed-form floor(RHS)=   10  exact: more than half need >=    12
  W= 4 w= 5 N=   20  ceiling W(w+1)=   24  closed-form floor(RHS)=   14  exact: more than half need >=    16
  W= 8 w= 4 N=   32  ceiling W(w+1)=   40  closed-form floor(RHS)=   26  exact: more than half need >=    28
  W=16 w=16 N=  256  ceiling W(w+1)=  272  closed-form floor(RHS)=  249  exact: more than half need >=   250
  W=64 w=16 N= 1024  ceiling W(w+1)= 1088  closed-form floor(RHS)= 1017  exact: more than half need >=  1018
  ```
  - Exact bit-length evaluation, "more than half need at least": 12, 16, 28, 250, 1018.
  - Closed form floor(RHS): 10, 14, 26, 249, 1017. Since predicates need more than the RHS, this is floor + 1 = 11, 15, 27, 250, 1018.
  - The ceilings W(w+1) are 20, 24, 40, 272, 1088.
  - All three rows match the ceiling note's table and text.
- **The hypothesis is unrestricted program text.** The paraphrase "programs chosen separately at each length" is not the source hypothesis. The ceiling note calls an argument size-oblivious if "it applies to every correct program at one input length, whatever the size of its text and whatever programs are used at other lengths".
  - A per-length argument with a program-size budget is **not** capped.
  - The finite-horizon form shows that correctness on all lengths up to any finite horizon does not help either.
- **What Π must use (source):** "A proof of superlinear time must fail for it, so it must use a hypothesis that this family violates, such as one finite program at every length or a budget on program size."
  - The barrier names only the threshold: a budget must exclude the O(2^{7N/8}/N)-instruction finite-horizon SAT programs.
  - It does not say that a smaller budget suffices.
- **Relation to the target:** the target fixes one program, so (a) is a counter-model to the per-length relaxation, not to the target itself.

### (b) Relativization

- **Source:** the relativized-clock note. [Relativized clock](relativized-clock.md)
- **Model:**
  - RAM with Θ(log(n+2))-bit words. A query names the start and bit length of a contiguous packed string in memory and returns one membership bit at unit cost.
  - Each step writes O(1) words, memory starts at zero, query memory persists, and the length of a large zero buffer may be specified.
  - The input problem is CircuitSAT with oracle gates of explicitly listed arity, with core type 0D (explicit circuit) or 1F (the original CNF byte for byte).
- **Theorem:**
  - For each integer p ≥ 1 there are a recursive oracle A and an O(n^p) deterministic oracle RAM for oracle-gate CircuitSAT.
  - Every deterministic oracle RAM solving it takes at least c·n^p steps on infinitely many lengths.
  - For p = 1: "plain SAT without oracle gates in its input also has an O(n) oracle algorithm". It writes Q₁(1F), with P = 2m⌈log₂(m+2)⌉ padding ones, in O(n + P/log(n+2)) = O(n) word steps, then makes one query.
- **Scope checked against the source:**
  - The Ω(n^p) half concerns **oracle-gate CircuitSAT only**. The note's own scope sentence: "It is the validity of the *high-arity oracle gate* on Cₖ that changes when the fresh bit is set. An ordinary 3CNF clause has its truth table fixed in advance."
  - The p = 1 world gives a counter-model to the target's conclusion, linear SAT, for plain CNF.
  - Source sentence: "The oracle example by itself does not refute a lemma restricted to actual ordinary Boolean algorithms."
  - Diagonalization is untouched: "The nondeterministic oracle-tape time hierarchy still applies with a fixed oracle because its diagonal universal simulation forwards an explicitly written query to the same oracle".
- **Two positive transfers in the same note (quoted, not re-derived):**
  1. Excluding O(n^d) for oracle machines that decide ordinary SAT with the R-empty oracle and submit only strings of length at most |Q_p(0^b)|, with b = ⌊(d−ε)log₂(n+2)⌋, would suffice to exclude O(n^d) for ordinary SAT.
  2. If ordinary SAT ran in O(m^d) time for d = 2 or 3, and p > d, the full oracle (for empty or linear-time R) would have an ordinary O(L) algorithm.
- **Proof status:**
  - The replay and unprobed-bit lemmas are checked in Lean. [OracleReplay.lean](../lean/OracleReplay.lean)
  - The size estimates, the oracle construction and the padded fixed point are manuscript arguments.
- **What Π must use:** a step that fails when one instruction may read Θ(n log n) bits.
  - The seed note's wording for its own missing lemma (its Claim L, Section 4(c)): "A proof of the missing lemma must therefore use that one instruction reads O(w) bits." [Seed note](checking-an-interval-against-a-seed-of-unknown-bits.md)
  - The relativized note locates the departure here: "Compiling that truth condition into a fixed small ordinary Boolean gadget is precisely where the model with R departs from ordinary SAT."

### (c) The multilinear-extension oracle (algebrization) and the speedup counter-world

- **Source:** the multilinear-oracle note. [Multilinear oracle](multilinear-oracle-clock.md)
- **Model:**
  - A Boolean query reads a contiguous packed string.
  - An extension query names a checked field (a prime and a monic irreducible) and a contiguous array of j field elements in fixed slots. It returns a specified bit or one bounded word.
  - Invalid queries return 0, and queries have no bulk side effects.
  - Each instruction writes at most a fixed number of w-bit words, and a nondeterministic instruction may guess a word.
- **Theorem 1:**
  - There is a recursive Boolean oracle A, with canonical multilinear extension Ã over every effectively presented finite field, such that a deterministic packed RAM using only A decides in O(n) steps whatever a nondeterministic packed RAM decides in O(n) with Boolean and extension queries.
  - "In fact the source machine may alternate at every step."
  - Ordinary SAT and explicit mixed-oracle CircuitSAT are decided in O(n) with A alone.
- **Theorem 2 (same world, R recursive, R ⊆ {1^k}):** DTIME^A_word[n²] ⊄ ATIME^{A,Ã}_word[o(n²)], counting worst-branch native steps.
  - The hard language accepts every string of length n exactly when R(1^{K(n)}) = 1, where K(n) = n²⌈log₂(n+2)⌉.
  - A relativizing proof of DTIME[t] ⊆ ATIME[o(t)] would give DTIME^A[n²] ⊆ ATIME^A[o(n²)] ⊆ ATIME^{A,Ã}[o(n²)]. So, for oracle access through this packed contiguous-buffer interface, the speedup DTIME[n²] ⊆ ATIME[o(n²)] cannot be proved by an argument that relativizes or algebrizes to that interface. This holds for every unbounded saving and any number of alternations. (This one-line deduction is made here; the note states the separation.)
  - The source's own qualifier: "a concrete failure for a speedup preserved under the stated algebraic oracle interface". Dymond–Tompa's tape speedup, cited in the same paragraph, lives in a different oracle convention. This is not a general algebrization barrier.
- **Scope, quoted:**
  - "It is possible for a proposed sum-check or PCP proof to exploit the fixed syntax of ordinary SAT, a restricted family of verifiers, or a different query interface. Retiring that proof requires showing its actual steps and costs extend to the oracle setting above."
  - On the speedup: "The hard clock here is the cost of creating a dense external query. A proof of an ordinary native RAM alternation speedup could rely on the fixed, oracle-free instruction set and avoid this obstruction."
- **Proof status:**
  - Finite support lemmas are checked in Lean, and finite fields by an audit. [MultilinearClockSupport.lean](../lean/MultilinearClockSupport.lean) · [multilinear_clock_support_audit.py](../audits/multilinear_clock_support_audit.py)
  - The construction is a manuscript argument.
- **What Π must use:** something beyond Boolean-plus-extension black-box access in this interface.
  - For sum-check or PCP proofs, the source names the fixed syntax of ordinary SAT, a restricted family of verifiers, or a different query interface.
  - For speedups, it names the fixed oracle-free instruction set. Any speedup step must fail for a machine that pays Θ(K) steps to write a dense query.
- **The J premise in this world (an inference made here; the speedup note's proof is not re-checked).**
  - Theorem 1 gives NTIME^A[n] ⊆ DTIME^A[n].
  - If the implication of the alternating-speedup note relativizes to this query interface, then its premise for J^A is false in this world. [Alternating speedup](alternating-native-speedup.md)

### (d) The checkpoint technique and the snapshot frontier

**Sources:** the signed-window, inverse-frontier, seed, band and materialized-census notes, and the steering section "Where the hierarchy proof stops". [Signed windows](signed-snapshot-windows.md) · [Inverse frontier](inverse-snapshot-frontier.md) · [Seed note](checking-an-interval-against-a-seed-of-unknown-bits.md) · [Band](sat-time-space-band.md) · [Materialized census](materialized-input-census.md) · [Where the hierarchy proof stops](../research-steering.md#where-the-hierarchy-proof-stops)

**What the technique proves (the window theorem).**
- *Hypotheses:*
  - a deterministic RAM with arbitrary workspace gives a sound signal on one designated sign within N^{c+o(1)} steps;
  - a sound nondeterministic UNSAT recognizer runs in N^{r+o(1)};
  - a fixed uniform decoder takes the formula, the time, a string and an address.
- *Cheap time:* a time is cheap if one string of N^e bits lets the decoder answer every work address within N^d steps.
- *Conclusion:* for 0 < b < c, if r(c−b+e) < 1 and b+d < 1 (UNSAT row), then arbitrarily large instances have a block of ⌈N^b⌉ consecutive pre-signal times, none of them cheap.
- At linear time the note's own example is c = r = 1, e = d = 1/3, b = 1/2: on arbitrarily large formulas of each sign, every one of ⌈√N⌉ consecutive states fails the joint budget.
- Eliminating b gives r(c+e+d−1) < 1 on negatives and r(c+e+d) < 2 on positives. At c = r = 1 both say e + d < 1.
- Finite exponent checks are in Lean. The checkpoint soundness proof is in the snapshot-description note, which was not opened for this note. [SignedSnapshotWindows.lean](../lean/SignedSnapshotWindows.lean) · [Snapshot descriptions](solver-snapshot-descriptions.md)
- Source sentence: "An unconditional upper bound on the cost of describing some state within the required windows of every fast SAT solver remains missing."

**Frontier theorem.**
- *Family:* for m a power of two, a permutation π of [m] is written as m fixed-stride tautological clauses plus two leading units that fix the sign. The length is N = Θ(m log m).
- *Program:* it is globally correct, with a fallback, and takes Θ(N) steps on the family.
- *Hardness:* for every fixed decoder and all but a vanishing fraction of π, at every time in the first half of the scans (Θ(N) consecutive times) and on both signs, no s-bit description reconstructs every inverse word within q steps when 1 ≤ q ≤ m/log² m and (s+1)(q+1) ≤ cm.
- *Matching decoder:* O((m/h) log m) bits and O((h+1) log m) time.
- *Consequence:* the window theorem's linear-time conclusion is realized by a correct linear-time program on an easy family, so by itself it contradicts nothing.
- Source: "An unrestricted lower bound has to force additional work for every correct solver, or exploit an additional property of the hard SAT inputs."

**The band.**
- On the packed word RAM with binary 3-CNF records, no deterministic SAT algorithm has both O(n L^a) time and O(n/L^{2a+7}) auxiliary bits, for each fixed a ≥ 0 (L = log). The band note first proves 2a+8; the census note improves it to 2a+7.
- Steering: a linear-time RAM touches up to O(n) words, that is O(n log n) bits ("b = −1"). The direct checkpoint simulation "gives no saving when even a single snapshot can cost the whole time budget", so with unrestricted workspace it gives nothing more.

**Seed rows.**
- Theorem 3 of the seed note: any sound seed row must reproduce forced memory exactly.
- Corollary 6: per-cut advice is refuted on an explicit DIMACS family with a linear-time loop-level program.
- **Shared-bank charts are neither proved nor refuted.** The landmark-decoder escape is "a sketch: I did not write the chart out, no script checks it".
- Claim L, which asks for a short seed chart with fast defect checks for every near-linear UNSAT signaler, is equivalent to excluding N^{1+o(1)} only through the signed-window recurrence. The seed note borrows that recurrence and does not re-derive it.

**So (d) is not a ban on snapshots.** It says that the window lemma is insufficient, and that a proof through checkpoints must contain a step that fails for the frontier program. Such a step uses either correctness on all formulas (not only running time on the inputs considered) or a property of hard SAT inputs that the frontier family lacks. It must also certify each imported word (the value of its last write) at a cost below a snapshot (about N log N bits) or a replay (the elapsed time). Whether a shared-bank chart can be refuted is the open part of (d).

### (e) Proof-system bounds

**Journal form at the target's scale:** the charge-decision note. [Charge decision](charge-decision-on-simple-permutations.md)
- *Family:* a distributed mod-6 charge family on an explicit 10-regular expander with t = 13·25^j vertices, encoded in ordinary CNF via a not-all-equal/coloring construction on simple permutations.
- *Lower bound:* on "every one of these negative permutations", PC on "the final coloring CNF" needs degree Ω(t) over every field. "The degree-size inequality gives total monomial size 2^{Ω(t)}" because there are O(t) variables. The SoS degree bound transfers only "if the real sign-system version is used".
- *Upper bound:* "One globally correct program attains O(t) word steps on this entire family … This gives the matching upper bound O(N/log N) on both file formats." The program regenerates the candidate file, compares it with the whole input, returns the charge sum mod 6, and otherwise falls back to a complete procedure. The negative members carrying the PC bound are members of this same family.
- *File format:* the canonical rendering (section "The same mandatory reads on proper DIMACS files" of the single-permutation note, seen by grep only) is ordinary ASCII 3-SAT. [Single simple permutation](sat-on-a-single-simple-permutation.md)
  - Its names are X_{i,c} = 3i + c and Z = 3m + 1.
  - It has an at-least-one-colour clause at each vertex, and for each consecutive pair in each order the clauses ¬X_{u,c} ∨ ¬X_{v,c} ∨ Z and ¬X_{u,c} ∨ ¬X_{v,c} ∨ ¬Z.
  - That the degree bound on "the final coloring CNF" carries over to this Z-split rendering is an inference made here, confirmed during review with no loss: restricting to Z = 0 maps any PC refutation of the Z-split CNF to one of the 2-clause CNF of no larger degree.
- *Additional (an inference made here, not in the note; confirmed during review):* PC degree Ω(t) gives resolution width Ω(t), since resolution width is at most PC degree up to a constant. Ben-Sasson–Wigderson (recalled, not accessed) then gives resolution size exp(Ω((W−3)²/n)) = 2^{Ω(t)} with n = O(t).

**General statement (standard).** Any deterministic O(N^D) SAT algorithm has run transcripts that form a Cook–Reckhow proof system with O(N^D)-size refutations. A size bound for a fixed system binds only algorithms whose runs translate into that system. Tseitin formulas over GF(2) are the classical illustration; Urquhart's exponential resolution bound for them is recalled, not accessed.

**What Π must use:** no inference from a fixed proof system's size bound to RAM time, unless Π proves that every fast RAM's runs become short proofs in that system. The family above shows that this fails for PC over every field.

### (f) Segregators

**Source:** the two-plane grate note. [Two-plane grates](two-plane-directed-grates.md)
- *Machine:* a fixed deterministic TM with two writable 2-D tapes (one nearest-neighbour head each) and a sequential read-only instruction tape.
- *Graph:* on an infinite input family, take the chronological cell-access graph, with time arcs and arcs between consecutive visits to the same cell.
- *Robustness:* deleting any c₀T step vertices leaves at least c₁T² directed connected ordered pairs.
- *Contractions:* every partition into K = Θ(T/b) consecutive intervals with b = o(T) keeps Ω(K²) directed pairs after deleting any O(c₀T/b) intervals.
- *Fixed machine:* a version with four planar tapes is block-respecting on every input at clock p³.
- *Scope, quoted:* "It proves a negative answer for a method requiring small segregators for all such multitape graphs. It does not exclude choosing a different simulation of a language."

The three-page note adds a three-page ordered DAG in which deleting aN/log N vertices leaves bN vertices that each keep bN ancestors. So Santhanam's (o(N), o(N/log N)) hypothesis fails already at three pages. [Three pages](three-page-segregators.md)

**Transfer to the RAM (an inference made here, not in the notes; the lift argument was contributed during review).**
- The RAM graph here is the one the segregator method uses: time arcs plus arcs between consecutive accesses to the same word.
- A log-word RAM simulates each tape step with O(1) instructions. Each simulated step first reads the two scanned cells (one word each) and then writes them.
- Deleting k RAM steps removes at most k step groups. A path of the grate that avoids those groups lifts to a RAM path. Within a group every read comes before every write, so an incoming arc (to a read, or to the group's first instruction) lands before an outgoing arc (from a write, or from the last instruction) leaves, and the time arcs inside the group connect them. Register arcs only add reachability.
- The RAM run has T_RAM = Θ(T) steps. So deleting a small enough constant fraction of the RAM steps leaves Ω(T_RAM²) connected pairs, and "every linear-time RAM run has o(T) segregators" is false.

**What Π must use:** a per-language normal form ("some machine deciding L has small segregators"), not a statement about all machines. A proof may rely on the locality of a normal form it constructs itself.

### (g) Capacity counts

Source: the capacity-line note. [Capacity line](the-instruction-capacity-line-is-capped-at-a-packed-scan.md)
- **Theorem 1/1′:** every per-step-capacity lower bound is at most about n/c\* charged steps for every Boolean function, with c\* ≥ w − 1 once a full-word ADD or AND is available.
- **Theorem 2:** the multiplicative-complexity form holds only for oblivious code.
- **Proposition 4:** MC(MUX_k) = 2^k − 1, while one indirect load computes it.
- These are manuscript proofs plus finite checks.

### Seven recorded obstacles, mapped

| Obstacle | Where it sits |
| --- | --- |
| 1 Ceiling ([ceiling](the-ceiling-of-the-unbounded-code-clock.md)) | (a) |
| 2 Every hard family has a packed-scan solver | Empirical observation; this is standard test (a), not a theorem |
| 3 Hierarchy stops at the speedup ([steering](../research-steering.md#where-the-hierarchy-proof-stops)) | (d) and (f) |
| 4 Relativization ([relativized clock](relativized-clock.md)) | (b), strengthened by (c) |
| 5 Hypothesis turns against you ([hard tables](output-linear-hard-tables.md)) | **Outside (a)–(e).** Under linear SAT, a fixed RAM writes a 2^m-bit table needing 2^m/m^{O(1)} gates in O(M/log M) steps |
| 6 Tensor-network ceiling ([network ceiling](exact-network-ceiling-for-ordinary-sat.md)) | **Outside.** O_F(N²) exact networks over each fixed field |
| 7 Program-size induction ([five instructions](five-instructions-cannot-decide-dimacs-sat.md)) | **Outside.** Exhaustion is complete only through 5 instructions; no C → C+1 mechanism |

## 3. Which techniques survive (each cell names the step that fails)

| Technique | (a) ceiling | (b) oracle | (c) multilinear | (d) checkpoints | (e) proofs | Other |
| --- | --- | --- | --- | --- | --- | --- |
| Diagonalization (J ∉ DTIME[o(n²)], proved) | passes: one fixed program is diagonalized | **fails alone**: the hierarchy holds relative to A, yet SAT ∈ DTIME^A[O(n)] | fails alone (same) | does not arise | passes | needs a transfer step to SAT |
| Alternation trading (speedup, collapse, hierarchy) | passes | the speedup must fail for oracle machines; relativizing speedups (this interface) are excluded by (c) Thm 2 | **algebrizing speedups at t = n² excluded (this interface)** for every unbounded saving (Thm 2) | snapshot-based speedups have so far stopped at the band; with unrestricted workspace a snapshot is as long as the run | passes | speedups that assume small segregators for every block-respecting machine are defeated by (f), whose four-tape version is block-respecting on every input |
| Segregators (PPST) | passes | not determined by these notes | not determined | does not arise | passes | **all-machines form false** (two-plane grate; three pages) |
| Arithmetization (sum-check, PCP, low-degree descriptions) | passes if applied to the fixed program's tableau | can pass (non-relativizing) | **fails** if it uses only Boolean + extension access (Thm 1 collapses even per-step alternation at linear time) | seed rows cannot shorten forced memory; Claim L is the target again | passes | [hidden-word opcode](hidden-word-opcode-and-local-verification-of-a-gap.md): with one recursive word opcode, an o(T)-bit proof plus ≤ T³ short branches cannot verify a constant-fraction gap, so black-box local checks fail |
| Proof-system bounds | does not arise | RAM conclusion fails in the p = 1 world, where SAT is linear | — | — | **fails**: PC degree Ω(t) on a family with an O(N/log N) solver | — |
| Circuit bounds (route A) (combination: RAM→circuit simulation plus a circuit bound that is not known) | passes **only** through the program-size term of the RAM→circuit simulation | passes **only** because each instruction is a fixed Boolean map on O(w) bits; relative to A, SAT has a one-gate A-circuit | passes for the same reason | passes (no snapshots) | passes | outside (a)–(e): the threshold is pinned only to the run exponent c_lin ∈ [σ_k, 2], with N log² N for the known simulation ([Simulation threshold](simulating-a-ram-step-by-exact-networks.md)); the journal's bound N(log N)^σ has σ unspecified and is imported from an external preprint, and its list-distinctness technique certifies at most O(n log n) for restriction-type embeddings ([Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)); a bound proved through tensor-network volume is capped at quadratic by the O_F(N²) network upper bound, which says nothing about circuit size |
| Information, communication, probe and capacity arguments | **fails** whenever size-oblivious: capped at N + ⌈N/w⌉ (minus log₂ w + O(1)); per-path capacity ≤ n − 1 (g) | passes naturally (O(w) bits per instruction is exactly what they charge) | passes | — | passes | none of the journal's arguments of this kind uses program size; with a size budget they become circuit- or branching-program-type statements |

**No known technique survives all of (a)–(e), or all of (a)–(g), by itself.** Among combinations of the journal's techniques, two pass all of (a)–(g), on paper only: they meet none of these barriers, and nothing more is claimed. This is a survey of the listed techniques, not a claim that no other shape exists. External barriers (natural proofs, locality of hardness magnification) were not assessed, and they bear on route A. [Circuit bound for 3-SAT](checking-the-sat-circuit-bound.md)

1. **Route A (nonuniform, size-bounded).**
   - A RAM→circuit simulation for programs of O(1) instructions gives circuits of size T(log T)^c. (An inference made here: the per-step instruction selection costs gates proportional to the text size, so this is the only point where (a) is met.)
   - Add a circuit lower bound above N(log N)^c for a SAT-projectable decision problem.
   - It uses the program-size budget for (a) and the O(w)-bit fixed instruction set for (b) and (c).
   - The simulation-threshold note brackets the exponents: per step, c* ∈ [1+σ_k, 2] for exact networks over a finite field k; for an N-step run on N bits, which is what this route needs, c_lin ∈ [σ_k, 2]. With the known simulation, an exact-network (or unambiguous-circuit) SAT bound unbounded relative to N log² N would exclude linear RAM time; a bound for deterministic Boolean circuits alone is not shown to suffice. [Simulation threshold](simulating-a-ram-step-by-exact-networks.md)
   - It is blocked outside (a)–(e) by the missing explicit bound of that order. The list-distinctness technique cannot supply it: for restriction-type embeddings it certifies at most O(n log n). [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)
   - If the circuit bound is proved through tensor-network volume, the O_F(N²) network upper bound caps it at about quadratic RAM time. That ceiling says nothing about Boolean circuit size, nor about unique-witness verifier size, which has no known polynomial cap ([unique-witness verifiers](unique-witness-verifier-size-of-sat-and-unsat.md)).
   - It clears (f) and (g) because it uses neither segregators nor per-path capacities. Its measure is total circuit size after compiling the run obliviously, which the capacity-line note names as one of the measures that can exceed n.
2. **Route B/C (uniform).** The proved hierarchy for J, plus one transfer step with three properties:
   - (i) it fails when one instruction reads Θ(n log n) bits (b);
   - (ii) it uses something beyond Boolean-plus-extension black-box access in the packed-query interface (c). For sum-check or PCP steps, that can be the fixed syntax of ordinary SAT, a restricted family of verifiers, or a different query interface; for speedups, the fixed oracle-free instruction set;
   - (iii) it certifies every imported word below snapshot or replay cost, with no full snapshots (d), and it does not assume that every machine, or every block-respecting machine, has small segregators (f). A transfer may still rely on the locality of a normal form it constructs itself.

   The speedup form is the exact premise of the alternating-speedup note: "Fix k≥1 and ε>0. It suffices to construct one alternating procedure M such that each valid opponent-program prefix has arbitrarily long extensions x where all branches halt, the verdict is J(x), there are at most k actual blocks, and s(x)+b(x)=O(n²/(log n)^{3k+ε})". Here s is the maximum path length in instructions. b is, in the note's words, "the maximum number of choice bits already consumed immediately before the first choice of a new block, over all changes of player on all paths". [Alternating speedup](alternating-native-speedup.md)

   It clears (f) as long as it does not assume small segregators for arbitrary machines. It clears (g) because a transfer step is not a capacity count.

   The compiler form is the journal's compiler criterion: a decision-preserving compiler for unary-clock nondeterministic word-RAM acceptance, with a uniform local bit indexer and proper DIMACS output of length o(s log s) on inputs of length s, would exclude deterministic O(N) SAT time. [Compiler criterion](compact-compilers-and-linear-sat-time.md)
   - The steering file records a proved obstruction to its algebraic form: "A locally indexed, O(t)-bit ordinary SAT encoding of the unary hierarchy source must have address degree Ω(log t) on infinitely many lengths." That is quoted from the steering file; the underlying note was not read. [Algebraic degree of a compact indexer](algebraic-degree-of-a-compact-physical-sat-indexer.md)
   - That result covers O(t)-bit encodings only, a sub-range of the o(s log s) criterion.
   - Not assessed: the short-branch note. It bounds how many variables a short RAM-to-3-SAT reduction must introduce, and its opening announces "an unconditional obstruction to decision-preserving local compilers at both proposed SAT deadlines" (k = 2 or 3). It may bear on the compiler route. Only its first paragraphs were read. [Short-branch verification](short-branch-verification-and-the-one-guess-compiler-barrier.md)

**Concretely, a surviving proof must use all three of the following:**
- one finite program for infinitely many lengths, or O(1)-size text in route A;
- the fact that each instruction is a fixed local predicate on O(w) bits, which is the feature the source notes identify as absent from both oracle worlds;
- either an explicit circuit bound above the simulation threshold, or a transfer that handles memory written at arbitrary addresses without snapshots and survives grates. It may use a normal form it constructs itself, but not small segregators for arbitrary machines.

## 4. The three standard tests

No lower bound is claimed, so the tests are applied to the two surviving shapes.

- **(a) Fast solver on the hard family?**
  - Route A has no family; its bound is worst case over a projection-closed function.
  - Route B/C's hard object is J, which provably has no o(n²) solver.
  - By contrast, every barrier in Part II is built on a family **with** a fast solver: frontier O(N), charge family O(N/log N), seed family O(N). That is why they bind only methods.
- **(b) Same bound for an easy language?**
  - Route A: any circuit bound above N(log N)^c is automatically false for 2-SAT, because a linear-time RAM for 2-SAT gives circuits below the threshold.
  - Route B/C: the transfer goes through the packed reduction of the native complete problem U to SAT. No packed reduction of U to 2-SAT is known (one would put nondeterministic linear time into near-linear deterministic time), so the argument as built does not apply to 2-SAT. [Native unary clock](native-unary-clock-band.md)
- **(c) Survives the relativized-clock oracle?**
  - Both shapes are built to fail there, as (b) requires.
  - Route A's simulation step breaks on a Θ(n log n)-bit query.
  - Route B/C's transfer must break by design.

## 5. Exact obstruction and next step

- **Obstruction.** No step in either surviving shape exists in the journal or, as far as these notes record, in the literature:
  - Route A needs an explicit network bound above N(log N)^c, where c is the run exponent c_lin of the RAM simulation (c ≥ 1 for any simulation that spends Ω(w) gates per w-bit word operation; c_lin ∈ [σ_k, 2] in general, and c = 2 for the known simulation). The journal's imported Ω(N(log N)^σ) has σ unspecified, and its list-distinctness technique certifies at most O(n log n) for restriction-type embeddings. [Simulation threshold](simulating-a-ram-step-by-exact-networks.md) · [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)
  - Route B/C needs a RAM speedup or compiler that is non-relativizing, non-algebrizing in the packed-query interface, and snapshot-free.
- **Next lemmas, by route:**
  1. **Route A:** narrow the run exponent c_lin, then find a SAT-projectable function whose network complexity provably exceeds n(log n)^{c_lin+1} in its n input bits (n(log n)^{c_lin} with a linear-length SAT projection). That needs a new lower-bound technique; the surviving candidate of the product-checking kind is cross-characteristic, such as [AB = C over F_3] with networks over F_2. [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)
  2. **Route B/C:** before any proposed speedup is developed, check that it fails for the multilinear world's machine that writes a dense K(n)-bit query and for the frontier program.
  3. **Inside (d):** decide whether shared-bank seed charts can be refuted. The landmark escape is an unchecked sketch.

## 6. What is not proved

- No lower bound on SAT, in any model.
- None of the cited theorems was re-proved. Their status is as stated in the sources: mostly manuscript, with the Lean files and audits named above covering only parts.
- The following deductions are made here and are unchecked:
  - the grate-to-RAM transfer in (f), with the lift argument contributed during review;
  - the resolution consequence of the PC degree bound in (e), which relies on Ben-Sasson–Wigderson (recalled) and was confirmed during review;
  - the claim that relativizing speedups, in this packed-query interface, are excluded via (c) Theorem 2;
  - the inference about the J premise in the multilinear world;
  - the program-size dependence of the RAM→circuit simulation.
- Whether segregator (PPST-type) arguments relativize in this oracle interface: not determined.
- External barriers (natural proofs, hardness-magnification locality) are not assessed. They concern route A at nearly linear circuit scale (recall only, not accessed).
- The circuit bound N(log N)^σ is the journal's import from an external preprint, and it was not checked here. It is already superlinear; what route A lacks is the exponent.
- "Passes" in the table means only that none of (a)–(g) applies, not that the technique works.
- No paper was read in full or in abstract for this note.

**How much of each source was read.**
- **Read in full:** the ceiling, worst-labelling, relativized-clock, multilinear-oracle, inverse-frontier, seed, signed-window, alternating-speedup, two-plane-grate, charge-decision and capacity-line notes.
- **The steering file:** lines 1–90 and 275–411 as they stood on 27 November, which include the section "Where the hierarchy proof stops" and the section on what counts as progress.
- **Opening paragraphs only (theorem statements):** the band, three-page, network-ceiling, hard-table, hidden-word-opcode and circuit-bound notes. [Hard tables](output-linear-hard-tables.md) · [Network ceiling](exact-network-ceiling-for-ordinary-sat.md)
- **Grep only:** the single-permutation note (the DIMACS rendering paragraph).
- **First 1,200 characters only:** the short-branch note.
- **Not opened:** the materialized-census note (the 2a+7 is quoted from the band note's opening and from the steering file), the snapshot-description, algebraic-degree, native-unary-clock and packed-band-transfer notes. [Packed band transfer](packed-band-transfer.md)

## Reproducing the check

Run `python3 unbounded_code_floor_recheck.py` from `audits/`. It takes well under a second and prints the five rows quoted in (a). The journal's own audit of the same inequality is `unbounded_code_ceiling_audit.py`. [unbounded_code_floor_recheck.py](../audits/unbounded_code_floor_recheck.py) · [unbounded_code_ceiling_audit.py](../audits/unbounded_code_ceiling_audit.py)
