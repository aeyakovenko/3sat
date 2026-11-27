# Log-word RAM time T fits in Õ(T^{2/3}) bits under the two-fifths preprint's evaluation lemma

On the unit-cost log-word RAM, time T is simulated in Õ(T^{2/3}) bits by a manuscript-level instantiation, at block width one, of the evaluation lemma of the unrefereed two-fifths-power preprint behind the space-route note, and so conditionally on that lemma (Claim R below). It is recorded alongside that note's exponent 4/5, which uses the preprint's stated one-tape theorem (the one the Lean comparator encodes), not in place of it. If it holds, the space route's ceiling moves from N^{5/4} to N^{3/2}, and the hierarchy by-product becomes DSPACE(n) ⊄ DTIME_RAM(n^{3/2−ε}): a space-versus-time hierarchy statement, not progress on SAT. The preprint's method also implies d-dimensional Turing-machine bounds below those of Williams 2025 for large d, so the preprint's standing is uncertain. The QBF chain lemma cαβ ≥ 1 then excludes only QBF exponents below 3/4. The linear, quadratic and cubic questions remain open. [Space route](the-space-route-caps-below-n-to-the-five-fourths.md) · [Factored lookups](factored-lookups.md)

## 1. Claim R and its standing

**Claim R.** Let P be a fixed log-word RAM program: word width w = Θ(log n), O(1) registers, indirect addressing, and each instruction loading or storing at most one cell. Then:
- for every input x of length n and every cap T ≥ n, P's outcome after T steps is computable in O(T^{2/3} polylog T) work bits;
- with unknown halting time t ≥ n, doubling caps give Õ(t^{2/3}).

**Standing.**
- Claim R is at manuscript level. It is conditional on the preprint's abstract evaluation lemma (`lem:weighted-evaluation`) at N = 2^w cells, together with restated forms of `lem:local-replay` and `lem:factored-history` in which epoch length and block width are decoupled. The restated proofs are unchanged (Section 2).
- The Lean comparator statement in the preprint's repository (`OneTapeSpace.lean`, scope in its `lean/docs/137.md`) states only the one-tape theorem and does not expose the evaluation lemma. The space-route note's 4/5 uses that theorem itself, after a manuscript quadratic one-tape scan. So 2/3 is recorded alongside 4/5, not in place of it.
- No failing step was found during review. Review read all of `evaluation.tex` and checked its algebraic identities: the homogenization and top-coefficient lemmas, the ordinary-vertex identity, the history-vertex identity chain and the register restoration. The evaluator's stack-pointer discipline, frame accounting and uniformity were read but not verified line by line.

[Preprint](https://github.com/openai/math/blob/main/preprints/Simulating-One-Tape-Time-in-Two-Fifths-Power-Space-September-25-2026/article.pdf) · [Evaluation lemma](https://github.com/openai/math/blob/main/preprints/Simulating-One-Tape-Time-in-Two-Fifths-Power-Space-September-25-2026/build/source/sections/evaluation.tex) · [Visit and replay lemmas](https://github.com/openai/math/blob/main/preprints/Simulating-One-Tape-Time-in-Two-Fifths-Power-Space-September-25-2026/build/source/sections/simulation.tex) · [Formalization scope](https://raw.githubusercontent.com/openai/math/main/lean/docs/137.md)

## 2. The instantiation

The preprint's own balance estimate (`sec:balance`) already gives 2/3 at block width one. Tape geometry enters only through the averaging in `lem:visits`, and `lem:weighted-evaluation` constrains the number of blocks only by a polynomial bound. So the question is whether every hypothesis of the evaluation lemma holds with single-cell blocks and data-dependent selection.

- **Blocks and controller.** Blocks are single cells, so N ≤ 2^w = n^{O(1)} ≤ T^{O(1)}. The raw controller is z = (pc, registers, τ, flags), with c = O(w + log T) = O(log T) bits.
- **Selection.** sel(z) runs the register-only instructions from z and returns the cell of the next memory access. It returns a designated cell 0 if z is terminal, or if the run halts or reaches the cap first.
- **Totality.** A raw string that is not a canonical controller encoding, including τ > T, is rejected as in the proof of `lem:visits`: sel returns cell 0, and Visit returns a fixed terminal dummy controller and leaves the cell unchanged. This makes sel, Visit and the replay flags total Boolean functions, as `lem:weighted-evaluation` requires. At semantic arguments the bitwise checks reject every non-canonical guess anyway.
- **One visit.** Visit(z, v) runs from z, with the selected cell holding v. It stops at the first memory instruction addressing another cell, and that instruction opens the next visit. It also stops at halt or cap.
- **Why register-only runs are folded in.** Folding them into visits makes every raw controller select exactly one block. That is what makes exactly one round guess pass.
- **Initial contents.** The initial cell contents (an input word or 0) come from an O(log T)-space accessor.
- **Visit count.** Distinct visits start at distinct steps, so there are R ≤ T + 1 visits. No averaging is used.
- **Parameters.** Epochs have L = k² visits in k rounds of k. The history word H_{e,j} holds at most L+1 controllers, so d = max(w, (L+1)c) = O(k² log T). There are E = ⌈(T+1)/L⌉ epochs.

**How the preprint's lemmas carry over.** The proofs of the local replay lemma, the checkpoint identity, `lem:factored-history` and `lem:epoch-weight` go through with "block" read as "cell". Wherever the source uses the block width b to bound a visit count, the epoch length L = k² takes its place:
- m ≤ L for m ≤ b in `lem:local-replay`;
- (j+1)k ≤ L for (j+1)k ≤ b in `lem:factored-history`;
- d = max(w, (L+1)c) for the width formula (eq:word-width).

These are restatements with unchanged proofs. Only `lem:weighted-evaluation` is used exactly as stated. The restated proofs use only three facts:
1. a visit is determined by (controller, selected block) and changes only that block;
2. the controller determines the block;
3. N and d are polynomially bounded.

**Hypotheses of `lem:weighted-evaluation`,** checked against its statement:
- polynomially many word identifiers, E(N + k + 1), each of O(log T) bits;
- base, ordinary and history vertices;
- N and d polynomially bounded, with Δ = (N+1)d, so field elements have O(log T) bits;
- local functions (sel, Visit, replay) computable in O(d polylog T) space from explicit arguments. sel's register-only search takes O(w + log T) space and unbounded time.

In the history-vertex part of the lemma's proof, N enters only through the degree D = (N+1)d, which sets the field size at O(log T) bits, and through the loop over i, which costs time and an O(log T)-bit index. Nothing there uses N ≤ T/b or b = k².

**The bound.** The lemma gives O((d + W) polylog T) with W = O(E(k + kc + 1)) = O((T/k) log T). That is Õ(k² + T/k), and k = ⌈T^{1/3}⌉ gives Õ(T^{2/3}). This is the balance of `sec:balance` with R = T visits in place of T/B: the stack is R/q + Rq/L ≥ 2R/√L and the word is at least L, so S ≈ R^{2/3}, and the block width B drops out. Numerically (`ram_two_thirds_space_exponents.py`):

```
  t=2^12  best k=2^3.69  log_t(space)=0.7432
  t=2^96  best k=2^31.69  log_t(space)=0.6762
  limit exponent 2/3
  T=2^80  log_T(space)=0.4121
```

The last line is the preprint's one-tape balance k² + T/k³, whose limit is 2/5.

## 3. Why the two-fifths exponent is not known to transfer to the RAM

The preprint's mechanism is stated in `introduction.tex` (paragraph "The mechanism") and proved in `simulation.tex`. It uses the single writable head in two places.

**(S1) Few visits: the shifted-grid crossing count.** The proof of `lem:visits` begins: "Every unit head move crosses a boundary for exactly one offset; a stationary move crosses none. The sum of crossing counts over all b offsets is at most T". So some offset has at most T/b crossings, hence at most ⌈1+T/b⌉ visits. This is a crossing-sequence argument and needs unit head moves. It is the source of the factor T/b in the epoch count E = T/b², and that factor is what turns 2/3 into 2/5.

**(S2) One selected block per visit.** A visit reads and changes one block and exchanges only an O(log T)-bit controller, so once a controller transcript is fixed the consistency check factors over blocks (`lem:local-replay`, `lem:factored-history`). The preprint's multitape section says so: "The single selected block in Lemma visits is essential to the factored round rule". It gives a counterexample with two blocks per visit, whose passing pairs {00, 11} are not a product of per-block predicates.

**On a RAM, (S2) survives and (S1) has no known form.**
- (S2) survives: a visit is "run until the next memory access leaves the current block", the controller is (pc, registers, elapsed time, flags), and every instruction touches at most one cell.
- (S1) fails for partitions fixed independently of the run's data: the visit count is the number of consecutive accesses that fall in different blocks. Take a RAM that writes a pseudorandom permutation of m cells and then chases pointers through it. Any partition into blocks of at most b cells that is fixed independently of the run's data has about t(1 − b/m) visits in expectation. This is a heuristic expectation calculation, not a theorem about every simulation.
- A partition along the permutation's cycles would give only about t/b visits, but sel would then need the run's intermediate data to locate a cell's block. So no RAM form of the crossing count is known; cleverer data-dependent blockings are not ruled out.

**Proposition O.** Suppose that for some α < 1/2 every fixed RAM program with polynomially bounded time t ≥ n is simulated in O(t^α polylog t) space. Then the same holds for every fixed multitape Turing machine.

*Proof.* A fixed k-tape machine with time t ≤ n^a is run by a fixed RAM program in O(t + n) steps:
- cell j of tape h is stored at address k·zz(j) + h, with zz(j) = 2j for j ≥ 0 and −2j−1 for j < 0, so no bound on t is needed in advance;
- the head positions are kept in registers, and the word constant is fixed by the exponent a;
- an input bit is extracted from its packed word by shifting, or by a table of 2^i for i < w built in O(w) steps. ∎

The multitape statement is open. Williams 2025 proves O(√(t log t)) and mentions TIME[t] ⊆ SPACE[t^{1/2−ε}] only as a hypothetical (Discussion). The preprint proves only Õ(√T) for several writable tapes (`prop:multitape`) and states that "neither the conversion nor the factorization argument establishes a new general-multitape exponent". So a RAM form of the two-fifths theorem would contain a multitape two-fifths theorem, a polynomial improvement of Williams 2025 that the source does not claim. Its factorization needs one selected block per visit, which fails for joint multitape visits, and the source says this observation concerns its factorization, "not the possibility of other multitape simulation methods". [Williams 2025](https://arxiv.org/abs/2502.17779v1)

## 4. Consequences if Claim R holds

Each item is conditional on Claim R, and so on the preprint's evaluation lemma. They sit alongside the space-route note's results, which rest on the preprint's Theorem 1 and the exponent 4/5.

- **(a) The QBF chain** (Section 6) gives only c ≥ 3/4, which says nothing about QBF.
- **(b) The space route's ceiling moves from N^{5/4} to N^{3/2}.**
  - Proposition B of the space-route note becomes: SAT ∉ DSPACE(N^{2b/3} log^c N) for every fixed c would exclude RAM time O(N^b).
  - Since SAT ∈ DSPACE(O(N/log N)) (that note's Proposition D), the route can exclude only b < 3/2. With 4/5 it was b < 5/4.
  - That note's RAM model is covered by Claim R's: a fixed program's direct addresses are determined by the controller, and an instruction touching several cells splits into a constant number of single-cell steps whose intermediate words are carried in the controller.
- **(c) The hierarchy by-product** becomes DSPACE(n) ⊄ DTIME_RAM(n^{3/2−ε}) for every ε > 0, via the preprint's bounded-space halting language H, as in the space-route note. This is a space-versus-time hierarchy statement. It is not progress on SAT: a polynomial reduction from H to SAT would put DSPACE(n) in NP.
- **(d) The diagonal J of the simultaneous-space note** runs in RAM time O(n^{49/40}), so it gets a direct Õ(n^{49/60})-bit decider in place of Õ(n^{49/50}).
  - The closest existing instantiation is the section "The fixed RAM diagonal admits cheap extensions for its local rules" of the factored-lookups note. It uses a public sweep schedule with R = O(t(1+t/b)) visits and gets O(t^{4/5} polylog t).
  - Claim R replaces the public schedule with data-dependent selection and R ≤ t+1.
  - That section's constant-depth local formulas rely on the public schedule, so its fast-lookup conclusion does not transfer to Claim R as it stands.

[Simultaneous space](simultaneous-space.md)

## 5. The d-dimensional flag and the preprint's standing

The instantiation applies to any machine whose steps each touch one cell and carry an O(log T)-bit controller.
- **d-dimensional multitape Turing machines.** Each step becomes at most 2p single-cell accesses: p reads whose symbols are kept in the controller, then p writes. That would give Õ(t^{2/3}) for every d. Williams 2025 gives (t log t)^{1−1/(d+1)}, with exponent d/(d+1): 2/3 at d = 2, 3/4 at d = 3, 4/5 at d = 4. So Õ(t^{2/3}) is below it for d ≥ 3 and equal at d = 2. Williams says his bound "matches the best known space bounds for simulating time-t machines with one d-dimensional tape" (Loui; Liśkiewicz–Loryś).
- **A single d-dimensional head with cube blocks.** Here (S1) also holds: a unit move along one axis crosses a boundary for s^{d−1} of the s^d offsets, so some offset has at most T/s crossings. The balance s^d + k² + T/(sk) then gives T^{2d/(3d+2)}: 2/5, 1/2 and 6/11 at d = 1, 2, 3.

```
  d=3: factored(single head)= 6/11=0.545   RAM-instantiation=2/3   Williams= 3/4=0.750
```

Neither contradicts a known lower bound, since everything cited is an upper bound, but both go beyond published bounds.

**This is not specific to Claim R** (a derivation made during review, not a sourced statement). A d-dimensional multitape machine with polynomially bounded time t runs on a one-writable-tape machine in Õ(t²) steps, by the record-list scan of the space-route note's Step 1 or through a linear-time log-word RAM. That note's Lemma A then gives Õ(t^{4/5}) space, which is below (t log t)^{d/(d+1)} for d ≥ 5, with equal exponents at d = 4. So the tension with published bounds comes from the preprint as a whole, and the journal already carries it through the 4/5. The preprint's standing is therefore uncertain beyond the usual caution for an unrefereed source.

## 6. The QBF chain lemma

**Lemma (chain).** Fix rationals c ≥ 1, α ∈ (0,1] and β ≥ 1, and assume:
- **(H1)** a fixed log-word RAM program Q decides QBF (QDIMACS, N bits) in at most κN^c steps;
- **(H2)** for every fixed RAM program P there is C(P) such that, on inputs of length n where P halts within t ≥ n steps, a deterministic Turing machine computes P's output in O((t+n)^α log^{C(P)}(t+n)) work bits;
- **(H3)** for a language L ∈ DSPACE(n) \ DSPACE(o(n)) there is a map x ↦ φ_x to QDIMACS with |φ_x| ≤ K n^β log n, computable by a RAM in time O(|φ_x|), such that x ∈ L ⟺ φ_x is true.

Then cαβ ≥ 1.

*(H3) with β = 2 is the Stockmeyer–Meyer/Savitch formula.*
- Take L ∈ DSPACE(n) \ DSPACE(o(n)) from the space hierarchy theorem, and a one-tape machine M for L that never leaves the input region (it uses a larger alphabet, by linear compression).
- A configuration takes m = O(n) bits. Make the accepting configuration absorbing, and let 2^m bound the running time.
- Φ_0(X,Y) is [X = Y or X ⊢ Y], a local check of O(m) clauses of width at most 3, with existential Tseitin variables.
- Φ_{i+1}(A,B) = ∃Mid ∀z ∃X ∃Y [(¬z → X = A ∧ Y = Mid) ∧ (z → X = Mid ∧ Y = B) ∧ Φ_i(X,Y)], where each implication is O(m) clauses of width 3. In prenex form each level's clauses mention only its own variables and the next level's.
- With m levels there are O(m²) variables and O(m²) clauses, and each literal is written with O(log n) digits, so |φ_x| = O(n² log n) bits, generated in O(|φ_x|) RAM time. This size is a hand count; no formula was generated.

*Composition.* Let P be the fixed program "write φ_x into memory, then run Q on it". On input x of length n it halts within O(n^{βc} log^c n) steps. Q expects words of Θ(log N) bits with N = Θ(n^β log n), so log N = Θ(log n); P's word-width constant is chosen large enough to hold Q's words and to address the cells Q uses, and P still touches one cell per instruction, as Claim R needs. By (H2) applied to P, L ∈ DSPACE(O(n^{αβc} log^{C'} n)) with C' = C'(P). If αβc < 1 this is o(n), contradicting the choice of L. ∎

The quantifier over C(P) is harmless because P is one fixed program. The argument works for any space-constructible S ≥ n in place of n.

*Exponents* (`ram_two_thirds_space_exponents.py`):

```
  alpha= 4/5 beta= 2  excludes c <  5/8 = 0.625   vacuous (c <= 1)   [RAM via one-tape scan + two-fifths (space-route note)]
  alpha= 2/3 beta= 2  excludes c <  3/4 = 0.750   vacuous (c <= 1)   [RAM, direct instantiation of the two-fifths method (Claim R)]
  alpha= 1/2 beta= 2  excludes c <    1 = 1.000   vacuous (c <= 1)   [multitape TM, Williams 2025 (sqrt(t log t))]
  alpha= 2/5 beta= 2  excludes c <  5/4 = 1.250   non-trivial (superlinear)   [one-writable-tape TM, two-fifths theorem]
  alpha=2/3: need beta < 3/2 (Savitch gives 2)
  beta=2: need alpha < 1/2
```

How to read these rows:
- c < 1 is already excluded, up to a logarithmic factor, because the input must be read (Ω(N/log N) word reads). So the lemma says something only when αβ < 1.
- **Ceiling.** QBF with v occurring variables should be in DSPACE(v + O(log N)): evaluate the prefix depth first, indexing variables by first-occurrence rank as in the space-route note's Proposition D, with v = O(N/log N). This is not re-proved for QDIMACS. Granting it, the route can never exclude c ≥ 1/α, even with every space lower bound granted. At α = 2/3 that ceiling is c < 3/2.

**Attribution.** The chain is a remark of Williams 2025 moved to the RAM. In his Discussion he writes: "A yes-answer to this question would imply (for example) a super-linear time lower bound on solving quantified Boolean formulas (QBF), which is still open … Note that if Theorem 1.1 could be improved to TIME[t] ⊆ SPACE[t^{1/2−ε}] for some ε > 0, then we would have TIME[t] ⊆ ATIME[t^{1−2ε}]." No novelty is claimed for the chain.

**The two escapes.**
- α < 1/2 on the RAM would give α < 1/2 for multitape machines (Proposition O), which Williams 2025 leaves open.
- β < 1/α, which is 3/2 at α = 2/3, would be a QDIMACS encoding of deterministic space S in S^{3/2−ε} bits. Up to polylogarithmic factors (ATIME(t) compiles to QBF of size t·polylog t, and back) this means roughly DSPACE(S) ⊆ ATIME(S^{3/2−ε}). The best known is S² (Savitch; Chandra–Kozen–Stockmeyer), and the nondeterministic form NSPACE(S) ⊆ ATIME(S^{3/2−ε}) ⊆ DSPACE(S^{3/2−ε}) would improve Savitch's theorem. No literature search was made.

**A clean form of the gap.** Under (H1) with c = 1 and Claim R, QBF ∈ DSPACE(Õ(N^{2/3})). So the route proves "no O(N)-time QBF" if it can prove QBF ∉ DSPACE(N^{2/3+ε}). The known unconditional bound is QBF ∉ DSPACE(N^{1/2−ε}), from the hierarchy plus Savitch. The route's conclusion QBF ∉ DTIME_RAM(N^{1+δ}) would also give QBF ∉ DTIME_multitape(N^{1+δ}); with Williams 2025 and β = 2 that chain stops at c ≥ 1 exactly, and Williams 2025 (Discussion) states that a superlinear time lower bound for QBF is still open.

## 7. A finite check of the factored rule with single-cell visits

`single_cell_visit_replay_check.py` checks the visit and replay definitions at toy size.
- *Toy RAM:* 2 cells holding bits, registers mod 2, random 6-instruction programs over indirect LOAD and STORE, ADDI, MOV, SWAP, JNZ and HALT, cap T = 12, k = 2, L = 4.
- *Raw controller space:* 6·2·2·13·3 = 936 controllers.
- *Procedure:* for epochs 0 and 1 and rounds 0 and 1, every one of the 936² = 876,096 raw two-controller suffixes Y is evaluated against the product of the two per-cell replay flags, each computed from its cell's epoch-start value alone. Programs are kept when their texts are distinct and their runs have at least 4 live visits touching both cells.

Command (from `audits/`, about 18 minutes): `python3 single_cell_visit_replay_check.py 6`. Its output is kept in `single_cell_visit_replay_check_output.txt`. Without an argument the script keeps the first 4 of these programs (16 checks, about a minute and a half). Key lines:

```
prog 0 [('SWAP', 0), ('LOAD', 0), ('JNZ', 0), ('SWAP', 0), ('JNZ', 1), ('HALT', 0)] epoch 0 round 0: |raw|^k=876096 passing=1 OK
prog 5 [('LOAD', 0), ('MOV', 0), ('JNZ', 0), ('LOAD', 0), ('JNZ', 0), ('HALT', 0)] epoch 1 round 1: |raw|^k=876096 passing=1 OK
programs tried=873247 kept=6 checks=24
```

What the run shows:
- Six distinct program texts were kept. Every run touches both cells, with 4, 4, 5, 5, 5 and 4 live visits.
- All 24 check lines end `passing=1 OK`: for each program, epoch and round, exactly one of the 876,096 raw suffixes passes the product of per-cell replay flags, and it is the true continuation.
- Every kept program moves a loaded value into the address register before its next memory instruction (SWAP or MOV after LOAD, possibly through a JNZ back-edge), so the addresses are data-dependent, which is the RAM feature at issue.

What it does not show:
- 9 of the 24 checks guess a suffix that starts at a terminal controller, where the replay rule forces the repeat.
- No kept run halts; all time out at τ = 12.
- It is a toy-size check of the visit and replay definitions only (2 cells, 1-bit values, cap 12, k = 2) and says nothing about the evaluation lemma.

An independent reimplementation written during review from the description above reproduced the run exactly: the same 6 programs and identical check and controller lines.

## 8. The three standard tests

- **(a) A fast globally correct solver for the hard family.** Claim R is a simulation, not a lower bound. The chain's hard instances are Savitch encodings of a space-hierarchy diagonal, so it is a hierarchy argument, not a family argument, and it passes vacuously; at the available exponents it proves nothing anyway.
- **(b) 2-SAT.** Quantified 2-CNF is in linear time (Aspvall–Plass–Tarjan). A DSPACE(n)-hard compilation into 2-CNF matrices of polynomial size would put DSPACE(n) in P, so the chain cannot give the same bound for 2-SAT or quantified 2-SAT; it uses the width-3 clauses of Φ_i.
- **(c) Oracle of the relativized-clock note.**
  - Claim R's proof uses exactly "one instruction touches one cell, and the controller is O(w) bits".
  - That oracle's query instruction submits a contiguous packed string of unbounded length in one step. A visit containing a query spans many cells, so (S2) fails. The space-route note's one-tape route fails there too, at its Step 1.
  - So the proof of Claim R does not go through relative to that interface, and whether its statement holds there is not settled. Whether QBF has an O(N)-time algorithm relative to that oracle is not settled here either.
  - The space hierarchy and the Savitch compilation relativize under the usual Ladner–Lynch-type conventions; this was not re-checked.

[Relativized clock](relativized-clock.md)

## 9. What is not proved

- **The chain lemma** is proved from standard ingredients (space hierarchy, Stockmeyer–Meyer/Savitch). The QDIMACS size O(n² log n) is a hand count; no formula was generated.
- **Claim R** is a manuscript instantiation of an unrefereed preprint (OpenAI, 25 Sep 2026), whose reported Lean formalization covers only the one-tape theorem.
  - It was checked against the statement of `lem:weighted-evaluation` and its history-vertex proof, and against the proofs of `lem:visits`, `lem:local-replay`, `lem:factored-history` and `lem:epoch-weight`.
  - The evaluator's stack-pointer discipline, frame accounting and uniformity were not verified line by line.
  - The toy check covers only the factored identity at tiny size.
  - No priority is claimed. Li–Tell was not accessed, and one non-exhaustive search during review found no 2026 paper stating a RAM t^{2/3} bound.
- **The d-dimensional exponents** of Section 5 are flags, not results. The Õ(t^{4/5}) d-dimensional bound through Lemma A is a derivation made during review, not a sourced statement.
- **Standing of the open problems.** That a superlinear multitape time lower bound for QBF is open is stated by Williams 2025 (Discussion), so QBF ∉ DTIME_multitape(N^{1+δ}) is open a fortiori. That β < 2 is open for deterministic space is from memory, with no literature search.
- **No unconditional QBF or SAT lower bound** is claimed.

## Sources and access

| Source | Access |
| --- | --- |
| Two-fifths preprint (OpenAI, 25 Sep 2026): `simulation.tex`, `introduction.tex`, `multitape.tex` | read in full |
| Two-fifths preprint: `evaluation.tex` | read in full; lines 60–150 (homogenization and top-coefficient lemmas) only during review |
| Two-fifths preprint: `hierarchy.tex` | lines 140–156 read |
| `lean/docs/137.md` of the preprint's repository | read during review |
| Williams, arXiv 2502.17779v1 (e-print TeX) | abstract, `thm:d-dimensional`, `rem:RAM` and the Discussion questions read; the d-dimensional proof only in part |
| Li–Tell, ECCC TR26-233 | not accessed |
| Loui 1981; Liśkiewicz–Loryś 1990; Paul–Reischuk 1981; Halpern–Loui–Meyer–Weise 1986 | abstracts through secondary listings only |
| Stockmeyer–Meyer, Savitch, Chandra–Kozen–Stockmeyer, Aspvall–Plass–Tarjan | not accessed; standard facts or Williams's citations |

## Reproducing the checks

Run from `audits/`. The replay check with argument 6 takes about 18 minutes; without an argument it runs the first 16 of its 24 checks in about a minute and a half.

```
python3 ram_two_thirds_space_exponents.py
python3 single_cell_visit_replay_check.py 6
```
