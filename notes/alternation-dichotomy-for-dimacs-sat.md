# Either no linear-time program decides DIMACS SAT, or no few-block alternating speedup of the diagonal exists: the alternation dichotomy with explicit parameters

The alternation criterion of the [alternating-speedup note](alternating-native-speedup.md) is stated there only as an implication. This note states and proves the unconditional dichotomy it gives, with explicit parameters. Either no O(N)-time program decides DIMACS SAT, even only on the rendered compilations of native instances, or the following holds for every k and every alternating program: some prefix of the diagonal J has no sequence of good extensions, of lengths tending to infinity, along which (n + s + b)·L^{3k}/n² → 0. The note also gives the form for SAT time N·log^a N, where the exponent becomes (3 + a)k, the class form, which is correct but conditional and not new, being the standard collapse-plus-hierarchy argument, and the native-milestone form. It is a precise restatement for citation. Its only new step is Lemma B, which renders the fixed-width binary encoding as ASCII DIMACS at O(1) steps per literal, so the exponent stays 3k. The idea of banking the dichotomy came from an external review. It is not progress on the open problem; the linear, quadratic and cubic questions remain open. [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)

**What is already in the journal.**
- The alternating note's section "A sufficient speedup for ordinary linear-time SAT exclusion" says that a k-block speedup of J excludes linear SAT, for the fixed-width binary encoding. For that encoding, Theorem 1 below is exactly its contrapositive.
- Other notes use "the alternation criterion's contrapositive" in prose, for instance the [description-first note](description-first-games-fail-on-one-hard-table-opponent.md). No note states the unconditional dichotomy with explicit parameters, for DIMACS input, or with the solver's log-exponent as a dial.
- The same description-first note states a sharper form of the implication, its Lemma 3 (refined driver charge): under linear SAT, a j-block game for J with s·L^{3j} + (b + n)·L^{3j−2} = o(t) on good extensions of every prefix contradicts the diagonal. Its proof re-derives only the cost, not the driver's two caps or the two-default test, and that note lists it as on paper only. A full proof would sharpen (II) below in b by L² (Section 4).
- The dial's ingredient, A = a + 3 for a solver taking O(N·log^a N) steps, is standard in the journal: [log-factor trades](log-factor-trades.md), [materialized input census](materialized-input-census.md), [checkpoint-table selection](checkpoint-table-selection-for-sat.md). Theorem 2 applies it to the alternation criterion.
- The DIMACS form adds the one step the journal does not prove, Lemma B, a hand argument with a finite check.
- The proofs are manuscript-level and rest on the imported lemmas listed at the end.

## 1. Statements

**Model R.** The journal's log-word RAM ([native unary clock band](native-unary-clock-band.md), section "Machine and complete language"):
- word width w(m) = 12⌈log₂(m + 2)⌉ on m input bits;
- a fixed register file, a read-only packed input and zero-initialized work words, with unrestricted workspace;
- the basis is load, store, Boolean operations, shifts, add, subtract, multiply, unsigned divide (with fixed zero-divisor semantics) and conditional control.

An alternating program may also guess a word, or a designated binary choice, owned by ∃ or ∀. Put L = ⌈log₂(n + 2)⌉.

**The diagonal J** (the alternating note, sections "The diagonal and the leading constant in the alternation bound" and "Accuracy needed on padded programs"). An input x of n bits starts with a self-delimiting program prefix p, and the rest is free. J(x) = 1 exactly when the deterministic program coded by p, run on all of x at width w(n), rejects within n² of its own steps. So J ∈ DTIME_R[O(n²)], and a deterministic program that halts within n² steps on all long inputs answers 1 − J on every extension of its own prefix.

**Resources of an alternating program M on x** (the alternating note, "How much of the path becomes a public input?").
- s(x) is the maximum path length in instructions.
- k(x) is the maximum number of blocks on a path. A block is a maximal run of choices by one player; deterministic steps may sit between them.
- b(x) is the maximum, over all changes of player on all paths, of the number of choice bits consumed before the first choice of the new block. A word choice counts w(n) bits, b = 0 if the player never changes, and always b ≤ s·w(n).
- Good_k(M, x) means that all branches halt, the game value is J(x), and k(x) ≤ k.

**F_red** is the set of fixed-field DIMACS renderings (Lemma B) of the packed-reduction 3-CNFs ([packed-band transfer](packed-band-transfer.md), "A virtual formula for a bounded computation") of instances of U, the unary-clock nondeterministic RAM acceptance problem of the native unary clock band note.

**Theorem 1 (linear dichotomy).** At least one of the following holds.
- **(I)** No deterministic program of R decides satisfiability of every ordinary ASCII DIMACS CNF file in O(N) steps, N the file's bit length. A stronger form also suffices: no such program is correct on all of F_red.
- **(II)** For every integer k ≥ 1 and every alternating program M of R there is a valid prefix p with the following property. No sequence of extensions x₁, x₂, … of p with |x_i| → ∞ has both Good_k(M, x_i) for all i and (n_i + s(x_i) + b(x_i))·L_i^{3k}/n_i² → 0.

**Corollary 1a (the ε form, at the journal's parameters).** (II) implies that for every k ≥ 1, every ε > 0 and every M there is a prefix p such that, for every C > 0, every sufficiently long extension x of p violates Good_k(M, x) ∧ s(x) + b(x) ≤ C·n²/L^{3k+ε}. Indeed, if infinitely many extensions satisfied both, then along them (n + s + b)L^{3k}/n² ≤ nL^{3k}/n² + C·L^{−ε} → 0, contradicting (II).

**Supplement (the explicit cylinder; not new).** If (I) fails through a solver S, one may take p = p_D in (II), where D = D(S, M, k) is the fixed driver of Section 2, explicit given S and M. Its scaling constant γ depends only on S, the fixed interpreter, the verifier V and k. In the little-o form the conclusion is only that no sequence exists on p_D; in the ε form, the length beyond which every extension of p_D fails depends on M, C and ε. This own-cylinder form is already in the alternating note ("The cylinder of the driver's own code contradicts this conclusion") and in the description-first note. The [padded-game separation](padded-game-separation.md) note proves related unconditional own-cylinder results, but has no form with a SAT hypothesis and the L^{3k} charge.

**Theorem 2 (a dial in the solver's log-exponent).** For every rational a ≥ 0, at least one of the following holds.
- **(I_a)** No deterministic program of R decides DIMACS SAT, or even is correct on F_red, in O(N·log^a(N + 2)) steps.
- **(II_a)** Statement (II) with L^{3k} replaced by L^{(3+a)k}.

Theorem 1 is the case a = 0. The exponent a must be rational (or computable) because the driver computes ⌊γn²/L^{(3+a)k}⌋ and the factor L^{3+a}. For real a, pass to a rational a′ ∈ (a, a + ε/(2k)); the ε form and Corollary 3 then hold for every real a ≥ 0.

**Corollary 3 (the worst-case class form).** If (I_a) fails, then for every k ≥ 1 and ε > 0 the language J ∈ DTIME_R[O(n²)] has no alternating program with at most k blocks, all branches halting, and s + b = O(n²/L^{(3+a)k+ε}) on all inputs. Since b ≤ s·w(n) = O(sL), and b = 0 when k = 1, the failure of (I_a) gives:
- DTIME_R[n²] ⊄ NTIME_R[n²/L^{3+a+ε}], and likewise for co-nondeterministic time;
- for every k ≥ 2, DTIME_R[n²] ⊄ Σ_kTIME_R[n²/L^{(3+a)k+1+ε}], for k-block alternating time with either player first.

The case k = 1, a = 0 (exponent 3) is what the [round-three summary](parallel-proof-attempts-of-27-november-round-three.md) calls "the known α > 3". Corollary 3 is not new. It is the standard combination of an alternation collapse with the hierarchy theorem, at the journal's exponents: a fast solver removes each block at a cost factor O(L^{3+a}), which [linear SAT batches](linear-sat-batches.md) states with an unspecified polylogarithm, so a k-block program for J with s + b = o(n²/L^{(3+a)k}) would put J in DTIME_R[o(n²)]. The journal records no unconditional separation of this kind on this RAM. The multitape speedup that the alternating note cites (Dymond–Tompa) needs a growing number of alternations, and with slowly growing r it saves only about log r. The [moving-the-milestone note](moving-the-milestone-to-nlin-versus-dlin-removes-no-barrier.md) lists "A RAM analogue of the PPST speedup at Grandjean scale" as a next lemma (its section 5, line 216), not as a known result. The literature was not checked for one.

**Corollary 4 (the native-milestone form; the first half of the alternating note).** At least one of the following holds.
- **(I′)** NTIME_R[n] ≠ DTIME_R[n], the native milestone.
- **(II′)** For every ε > 0 and every M there is a valid prefix p with no sequence of extensions x_i, |x_i| → ∞, along which all branches halt with value J(x_i), s + b = O(n_i²/(log n_i)^ε), and k(x_i)/log log n_i → 0.

(I) ⇒ (I′), because DIMACS SAT ∈ NTIME_R[n]: the trie verifier of the RESULTS.md paragraph on the native milestone interns decimal names just as it interns binary ones. Also (II′) ⇒ (II). So neither dichotomy follows from the other branch by branch: Theorem 1 has the stronger first branch and Corollary 4 the stronger second branch.

## 2. Proofs

**Lemma B (the DIMACS bridge).** Let Φ be the packed-reduction 3-CNF of a U-instance y of N bits. Φ has O(N·L²) clauses and variable indices below 2^{O(L)}, by item 3 of the packed-band transfer's virtual formula (O(H·L²) gates and constraints, with H = O(N)). A fixed program of R writes a proper ASCII DIMACS file for Φ with these properties:
- the header is "p cnf V C" with the exact clause count;
- every literal sits in a fixed-width field: a right-justified canonical signed decimal with leading spaces, followed by a separating space, and each clause ends with "0";
- the file has O(N·L³) bits;
- writing it takes O(N·L²) steps after O(N^{1/4}·L) steps of table setup.

*Proof.*
1. Take d = max(1, ⌊log₁₀(N + 2)/4⌋), and build two tables of size 10^d ≤ N^{1/4}: T0[v] holds the d digits of v zero-padded, and TS[v] holds them space-padded.
2. Indices have O(L) bits, so each splits into O(1) chunks by O(1) divisions by 10^d.
3. The top nonzero chunk is read through TS and the lower chunks through T0, and the digit count gives the position of "−". A field of O(L) bits occupies O(1) host words and is assembled by shifts and ORs.
4. Clause literals come from the single-row templates in O(1) word operations after poly(L) setup (the packed-band transfer, "Packed access to the reduction").
5. So each literal costs O(1) steps, and the whole file costs O(#literals) = O(N·L²).
6. Repeated literals are legal in ordinary DIMACS. If three distinct variables per clause are wanted, the pin gadget of the [locally uniform circuit depth](native-linear-time-and-locally-uniform-circuit-depth.md) note, in its paragraph on ordinary ASCII DIMACS, changes the size only by a constant factor.
7. The solver's reads of its own w_S-bit input words are served from the written bank in O(1) steps each, since one read spans O(1) host words, by the journal's limb simulation. ∎

The fixed-field form matches the journal's DIMACS convention, in the same note, and CaDiCaL accepts it. During review it was also suggested, without being checked, that single-space variable-width fields would work equally well. Since the file is written physically, each O(L)-bit field could be appended at a running bit offset with O(1) shifts and ORs. That would cover a strict reading of the 1993 DIMACS description, under which items are separated by a single whitespace character; that reading is quoted from memory. The proof deliberately does not use the polylog-per-byte indexer of the locally uniform circuit depth note, which would break the exponent 3k.

**Finite check of Lemma B** ([the check](../audits/dimacs_fixed_width_literal_check.py)):
```
field rendering: 7 value ranges x 300 random literals, mismatches=0
cadical: trials=300 agree=300 sat=275 unsat=25
```
The chunk-and-table rendering equals the right-justified canonical decimal on 2,100 random literals plus boundary indices, for index ranges up to 2³¹ − 1. CaDiCaL gives the same verdict on the space-padded fixed-field files as on the single-space files in 300 of 300 trials. The check has limits:
- it models the rendering in Python rather than in RAM steps, so the O(1) cost per literal is not exercised;
- its CaDiCaL half uses at most 40 variables, so wide fields are never parsed;
- it renders no actual F_red file.

**Proof of Theorem 2 (Theorem 1 is a = 0).** Suppose (I_a) fails: S decides DIMACS SAT, or is merely correct on F_red, in at most c_S·N·log^a(N + 2) steps for all large N. The steps follow the alternating note, with the encoding step replaced by Lemma B.
1. **A native decider A.** On a U-instance y of N bits, form Φ(y) by the packed reduction, write its rendering by Lemma B in O(N·L²) steps, and run S on it in O(N·L³·log^a(N·L³)) = O(N·L^{3+a}) steps. A is correct on every y, because Φ(y) is satisfiable iff y ∈ U and the rendering lies in F_red. S runs at its own width with O(1) limbs and the fixed-depth radix trie for sparse addresses (the width paragraph of the native unary clock band note), and every operand stays below n³ bits, inside that note's width accounting.
2. **Verifier and clocks.** These are the alternating note's sections "One fixed verifier" and "Clocks and machine widths", with A in place of the linear native decider.
   - V(M, x, prefix π, player q, depth j, default d, clocks) answers the signed question whether the truncated subgame's value is 1 (q = ∃) or 0 (q = ∀). V guesses q's choices, replays M from the start with π, and accepts at a halt or cutoff iff the bit is the one sought.
   - At an allowed change of player, V builds the child query (π extended, the opposite player, depth j − 1 and the unary clock H_{j−1}) and accepts iff A answers 0 on it.
   - Truncation happens after P source steps, before passing more than P choice bits to the next block, or before a block beyond depth j.
   - Clocks: H₁ = KP and H_j = K·L^{3+a}·H_{j−1}. One child call, including building its operand of O(P + H_{j−1}) bits, costs O(L^{3+a}·H_{j−1}).
   - The driver first runs M's deterministic prefix for at most P steps and settles an early halt or cutoff directly. Otherwise it starts the root query with the owner of the first choice, so that no empty initial block is charged (the alternating note's variant in "A sufficient speedup for ordinary linear-time SAT exclusion"). This is what gives depth k, and so the exponent 3k rather than 3(k + 1), since the imported sections use k + 1 blocks with a possibly empty existential first block. Corollary 3's co-nondeterministic case and its "either player first" also rest on it.
   - The driver runs A on that query (depth k) once for each default d ∈ {0, 1}, at cost O(L^{3+a}·H_k) = O(K^k·L^{(3+a)k}·P), inverts the signed answer when the first block is universal, and outputs the common answer, or 0 if the two answers differ.
   - Along any chain the solver is called once per block, so k times, and each call multiplies the operand length by O(L^{3+a}). For k = 1, b = 0 and the root operand has O(P) bits, at cost O(P·L^{3+a}). For k = 2 the inner operand has O(P) bits and costs O(P·L^{3+a}) inside V, so H₂ = Θ(P·L^{3+a}), and the root operand of O(P·L^{3+a}) bits costs O(P·L^{2(3+a)}).
3. **Scale.** Take P = ⌊γn²/L^{(3+a)k}⌋. Every well-formed trial, including the deterministic prefix of M and both defaults, ends within C_k·P·L^{(3+a)k} + o(n²) instructions, where C_k depends on S, the interpreter, V and k. With γ < 1/(2C_k), the driver D halts within n² steps on every sufficiently long input.
4. **Correctness where it matters.** The signed-query meaning holds by induction on j: a child that accepts witnesses the opposite signed verdict; OR and AND are monotone, so default 0 gives a lower bound on the value and default 1 an upper bound; and when the two defaults agree, the common answer is the value. This two-default lemma is checked in Lean: `cutoff_bounds` and `agreement_decides` of the journal's `AlternatingNativeCutoffs.lean`, which proves it on an abstract finite game tree. Along a sequence with Good and (n + s + b)·L^{(3+a)k}/n² → 0, eventually P ≥ n + |M| + s + b + 1. From then on nothing is truncated, so D(x_i) = val_M(x_i) = J(x_i).
5. **Diagonal.** D halts within n² steps on long inputs, so J(x) = 1 − D(x) on every extension of D's own prefix p_D. Hence no such sequence exists on p_D, which is (II_a), and the explicit-cylinder supplement follows. The hypothesis on S was used only on renderings of queries that D builds, which lie in F_red. ∎

**Corollary 3.** J ∈ DTIME_R[O(n²)], and a worst-case k-block program for J with s + b = O(n²/L^{(3+a)k+ε}) meets Corollary 1a's premise on every extension of every prefix. Then use b ≤ s·w(n) = O(sL), with b = 0 at k = 1.

**Corollary 4.** It is the contrapositive of the first half of the alternating note. If NTIME_R[n] = DTIME_R[n], then U has a linear decider (the displayed equivalence in "Machine and complete language" of the native unary clock band note). The simulation then costs O(C^{k+1}(n + |M| + s + b + 1)), with C independent of M and k, and on the given sequence C^{k+1} = (log n)^{o(1)}. The search is capped at budget t/log^η t with η < ε, returning 0 on exhaustion. This gives a deterministic o(n²) tester that is correct on the sequence, and the diagonal contradicts it on its own prefix.

## 3. The three standard tests

- **(a) A fast, globally correct solver on the hard family?** No lower bound on a family is claimed. The strong form of branch (I) names F_red, the rendered compilations of native instances. A fast correct solver on F_red is exactly what (I) denies, and nothing is known either way.
- **(b) 2-SAT.** The proof fails at the compile step. U is compiled to 3-CNF, and no quasi-linear compile of U to 2-CNF is known; one would put NTIME_R[n] inside DTIME_R[n·polylog]. Since 2-SAT is linear-time, a 2-SAT analogue would assert (II) unconditionally, and that is not obtained. Passes.
- **(c) The oracle of [the relativized clock](relativized-clock.md).** Branch (I) is false in its p = 1 world, where plain SAT is O(n). The proof compiles V's run into plain 3-CNF at O(L³) bits per step, using that one instruction reads O(w) bits. A relativized V makes oracle queries of Θ(n log n) bits, which plain CNF cannot encode. So the proof does not relativize to that interface, and no relativized form is claimed; the description-first note finds the same for its uses of the criterion.
  - In the multilinear world of the barrier note's case (c), (I′) fails, since NTIME^A[n] ⊆ DTIME^A[n].
  - Its Theorem 2 gives DTIME^A[n²] ⊄ ATIME^{A,Ã}[o(n²)], but for a different hard language, not for J^A.
  - Whether (II′)^A holds for J^A depends on whether the native proof relativizes to that interface, which the barrier note leaves conditional. No contradiction arises either way.

## 4. Exact obstruction and next step

The missing step is unchanged: an alternating procedure for J with at most k blocks and (n + s + b)·L^{3k} = o(n²) on arbitrarily long extensions of every prefix. Snapshots and access logs cost Θ(t) words, as the [round-two summary](parallel-proof-attempts-of-27-november-and-why-each-stopped.md) records. Proving (II) outright would be an unconditional no-speedup theorem for alternating RAMs that no known technique gives. Relative to the multilinear oracle, a worst-case no-speedup theorem holds for a different language (the barrier note's case (c), Theorem 2). Whether (II) holds there for J^A is not known; it would follow only if this proof relativizes to that interface.

Two strengthenings of the statement remain open:
1. **The refined budget.** The description-first note's Lemma 3 states the implication with budget s·L^{3k} + (n + b)·L^{3k−2} = o(n²), compiling each child directly, but re-derives only the cost, not the driver's caps or the two-default test. A full proof of that driver would sharpen (II) in b by L².
2. **A polynomial dial.** SAT in N^c with J at clock n^τ, τ > c^k, would need a k-block speedup to n^{τ/c^k}, by the same clock recursion with H_j ≈ H_{j−1}^c. This needs the width accounting beyond n³ redone.

## 5. What is not proved

- The imported lemmas were not re-derived:
  - the packed reduction, with O(H·L³) bits and templates evaluated in O(1);
  - the width and sparse-address simulation;
  - U ∈ NTIME_R[N] with variable programs;
  - the hierarchy for J.
- The signed-query induction was checked by hand. Only the abstract two-default lemma is formalized.
- Lemma B is a hand proof plus the limited finite check above; its O(1) cost per literal relies on unit-cost division and the 10^d tables.
- The refined budget and the polynomial dial of Section 4.
- Anything about which branch of either dichotomy holds.

## Reproducing the checks

Run the check from the audits directory and the Lean file, which is the journal's own, from `lean/`:
```
python3 -B dimacs_fixed_width_literal_check.py 300
lean AlternatingNativeCutoffs.lean
```
The check takes about 2 seconds with 300 trials, and with no argument it runs 200. It finds CaDiCaL on the PATH or in a Lean toolchain and skips the solver half without one. The Lean file checks with exit status 0. [DIMACS bridge check](../audits/dimacs_fixed_width_literal_check.py) · [Two-default lemma](../lean/AlternatingNativeCutoffs.lean) · [Alternation criterion](alternating-native-speedup.md)
