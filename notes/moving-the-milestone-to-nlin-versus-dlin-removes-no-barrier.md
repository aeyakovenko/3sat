# Moving the milestone to Grandjean's NLIN ≠ DLIN (RISA) removes no barrier

Moving the journal's milestone, nondeterministic versus deterministic linear time on the log-word RAM, to Grandjean's NLIN ≠ DLIN, equivalently "RISA is not in deterministic linear time", removes no barrier: the per-word cap, the oracle collapse, the snapshot and space bounds, and the segregator obstruction all apply unchanged in Grandjean's units (Sections 3 and 5). The journal's milestone implies NLIN ≠ DLIN for the composite addition-RAM classes of Section 1, with no further hypothesis (Lemma A, a hand proof covering both the packed and the one-letter-per-register input conventions). The further step to "RISA ∉ DLINEAR" for Grandjean's 1994 classes needs the two-sided hypothesis H (H_N and H_D), which matches those classes to the composite model; whether the two milestones are equivalent is open. This is the first journal note on NLIN, DLIN or RISA; Grandjean–Jachiet were cited once before, for constant-time arithmetic. No lower bound is proved, and the linear, quadratic and cubic questions remain open. [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md) · [Earlier Grandjean–Jachiet citation](binary-word-interactions-in-a-sat-solver.md)

Grandjean's school measures linear time against the number of O(log N)-bit registers in the input.
- **Structures** (graphs, automata) under their natural encoding have bit length Θ(N_G log N_G) (Grandjean–Jachiet 2022, eq. (19)).
- **Words:** the same section (p. 53) calls one letter per register the most natural representation. It offers packing into Θ(n/log n) registers as a device from Grandjean 1996, Schwentick 1997 and Grandjean–Schwentick 2002.
- **So** on structures and packed words, Grandjean's "linear time" is **packed-scan time** O(N/log N) in the journal's units. With one letter per register it is O(N).
- **The 1994 RISA paper's convention is unread.** A secondary aggregator summary (Bohrium, found during review, not read for this note) gives DLINEAR = DRAM(n/log n).

**The identification does not cross unit systems.** A proposed identification held that "nondeterministic beats deterministic linear time on the RAM" is "exactly 'RISA is not linear-time', with no log-factor loss". That holds inside Grandjean's model, by his 1994 completeness theorem. Its translation to the journal's bit-linear milestone is not established:
- **Proved (Lemma A, hand proof):** the journal's milestone NTIME_RAM[N] ≠ DTIME_RAM[N] implies NLIN ≠ DLIN for the composite addition-RAM classes of Section 1. No hypothesis is needed for this.
- **The step to RISA ∉ DLINEAR** (the 1994 classes) additionally needs hypotheses H_N and H_D (Sections 1 and 6), which match the 1994 classes to the composite model on the nondeterministic and the deterministic side.
- **Open:** the converse. Nothing read refutes it. The routes visible here would need a log-factor downward translation, and on word inputs also a deterministic sparse-address simulation that Grandjean–Jachiet list as open.

**The barriers in Grandjean units:**
- The per-word cap of about n/w charged steps is exactly Grandjean-linear time. [Capacity line](the-instruction-capacity-line-is-capped-at-a-packed-scan.md)
- The multilinear-oracle collapse carries over (by reading the wrapper's size formula).
- The Kannan-type space bound, derived by the journal's argument and not re-proved, is tight in Grandjean units (Ω(n) registers against O(n) registers), so the space route ends there.
- The only proven RISA lower bound is the Turing-machine bound from Paul–Pippenger–Szemerédi–Trotter (PPST).

The compiler criterion at SAT exponent a = −1 (Section 4) holds only conditionally, on a packed failure-test emitter whose step count is sketched there. Its conclusion would be the packed-scan exclusion of SAT, and directly NLIN ≠ DLIN, not O(N).

## 0. Sources (ledger)

- **Read (text extraction with TeX glyph decoding; some letters were lost, so the papers are paraphrased with page numbers rather than quoted):**
  - Chapdelaine–Grandjean, https://arxiv.org/abs/cs/0606058 (2006): pp. 1–2, 6–7 and the references.
  - Chapdelaine, https://arxiv.org/abs/cs/0606080 (2006): pp. 1–3 and the references.
  - Grandjean–Jachiet, https://arxiv.org/abs/2206.13851 (2022), "Which arithmetic operations can be performed in constant time in the RAM model with addition?": abstract, §1, §2 opening, §2.5, §10 pp. 52–55 (including the p. 55 sentence listing the 1994 papers among those that defined LIN/DLIN for the addition RAM).
  - Grandjean–Jachiet, https://arxiv.org/abs/2509.10188 (2025): abstract.
- **Abstract only (Crossref or Semantic Scholar):**
  - Grandjean, SIAM J. Comput. 17 (1988) 786–809, https://doi.org/10.1137/0217050.
  - Grandjean, SIAM J. Comput. 19 (1990) 438–451, https://doi.org/10.1137/0219028.
  - Grandjean, SIAM J. Comput. 23 (1994) 573–597, https://doi.org/10.1137/S0097539791223206.
  - Grandjean–Schwentick, SIAM J. Comput. 32 (2002) 196–230, https://doi.org/10.1137/S0097539799360240.
  - Grandjean–Olive, JCSS 68 (2004) 546–597.
- **Not accessed:** HAL, Springer and ScienceDirect returned bot-check pages, and no attempt was made to get past them.
  - Grandjean, Ann. Math. AI 16 (1996) 183–236.
  - Grandjean, Comput. Complexity 4 (1994) 62–106.
  - Grandjean–Olive, Comput. Complexity 7 (1998) 54–97.
  - Creignou, Ann. Math. AI 16 (1996) 237–249.
  - Robson, TCS 82 (1991) 141–149 (title only).
  - Schnorr, JACM 25 (1978) (title only).
- **Cited only through the papers read (not accessed):** Paul–Pippenger–Szemerédi–Trotter (FOCS 1983); Cook (IPL 1988); Dewdney (1982); Creignou (TCS 1995); Barbanchon–Grandjean (CSL 2002); Schwentick (STACS 1997).
- **Seen only in a search-engine summary, so secondary and unverified:**
  - "CONTRACT is NLINEAR-complete" and "20 of Karp's 21 problems in NLINEAR".
  - "sort-lin reductions" and "SAT minimal" (1996).
  - Creignou 1996: k-RISA_r in P, and k-RISS_r linearly equivalent to SAT.

## 1. Statements

The proposed first lemma, read literally: for the journal's log-word RAM, NTIME_RAM[n] ≠ DTIME_RAM[n] ⇔ RISA ∉ DLIN, "with no log-factor loss".

What is stated and proved instead:

**Lemma A.** Let NLIN and DLIN be Grandjean's classes:
- unit-cost RAM with addition;
- register contents and addresses O(N_G), where N_G is the number of input registers;
- inputs given as arrays of N_G integers, each O(N_G);
- words packed into factors of Θ(log n) letters (Grandjean–Jachiet 2022 §10, convention attributed there to Grandjean 1996, Schwentick 1997, Grandjean–Schwentick 2002), or given one letter per register (the representation 2022, p. 53, calls most natural); the proof covers both;
- nondeterminism guesses one register per step.

If NLIN = DLIN, then every L ⊆ {0,1}* in the journal's NTIME_B[N] lies in DTIME_B[N]. Here B is the model of the native unary-clock note: N-bit packed input, w = 12⌈log2(N+2)⌉, unrestricted zero-initialized workspace, word guesses. [Native unary clock](native-unary-clock-band.md)

Hence journal milestone ⇒ NLIN ≠ DLIN for these composite classes, with no further hypothesis. Under H_N and H_D below, also journal milestone ⇒ NLINEAR ≠ DLINEAR ⇔ RISA ∉ DLINEAR, the last step by Grandjean 1994, abstract.

**Hypothesis H (two-sided).** The step "⇔ RISA ∉ DLIN" needs the 1994 classes to match the composite model on both sides.
- **(H_N)** The 1994 NLINEAR contains NLIN_+: linear time on the 2022 addition RAM with a one-register guess.
- **(H_D)** Every 1994 DLINEAR machine runs in linear time on the journal's RAM, on the encoding used in step 4. This holds if the 1994 deterministic model is no stronger than the 2022 addition RAM and uses either the packed or the one-letter word convention. The 1994 convention also selects which version of the proof applies: padding is needed for the packed convention and not for one letter per register.

**Evidence.**
- Grandjean–Jachiet 2022, p. 55, list the 1994 SIAM paper ([39]) and the 1994 Computational Complexity paper ([38]) among papers that "have defined and started to study the LIN class of our RAM model with addition and its subclass of decision problems called DLIN". That supports H_D and the addition-RAM part of H_N.
- Chapdelaine 2006, p. 3, asserts that the linear-time classes are essentially independent of the instruction set, citing Grandjean–Schwentick 2002.
- Against this: the 2022 paper defines no nondeterministic class, and the 2006 NRAM extracted has only +1/−1 and guess(A).
- The 1994 guess instruction and I/O convention are unread.

## 2. Definitions, the known RISA bound, and Lemma A

### 2.1 Definitions found

- **RISA.** Garey–Johnson AL7, as worded in the Grandjean 1990 abstract.
  - Instance: a positive integer K and an incompletely specified DFA A = (Q, Σ, δ, q0, F), with δ a partial function Q×Σ → Q.
  - Question: can δ be extended to a total transition function so that the completed automaton has an equivalent reduced automaton with at most K states?
- **Machine model.** It differs across papers, and the versions are kept apart:
  1. **1994 SIAM (abstract only).** "A random access machine with powerful input/output instructions"; the classes are named DLINEAR and NLINEAR. The I/O convention is not verified.
  2. **2002 Grandjean–Schwentick (abstract).** DLIN was "introduced in [Grandjean 1996]": essentially the functions computable in linear time on a RAM that uses only numbers of linear value.
  3. **Chapdelaine 2006, p. 2–3.** Input is a unary structure ([n], f) with f: [n] → [n]. A RAM works in linear time if it performs O(n) instructions and uses only integers O(n), as contents and addresses. DLIN and NLIN are the deterministic and nondeterministic versions.
  4. **Chapdelaine–Grandjean 2006, pp. 6–7 (time–space NRAM).**
     - Registers: accumulators A, B_1..B_d and memory R_0, R_1, ...
     - Instructions: A:=A+1, A:=A−1, guess(A) ("stores any integer"), input reads Q_j(B_1..B_k), indirect load and store, equality branch.
     - Register contents are O(n^s) for NTISP(n^t, n^s).
  5. **Grandjean–Jachiet 2022 §1–2.**
     - Contents and addresses are O(N), N = number of input registers; unit cost; addition is the only primitive operation.
     - LIN is invariant under adding −, ×, div and many other operations, after linear-time preprocessing.
     - Integers up to O(N^d) can be held in O(d) registers, and +, −, ×, div and bitwise operations on them take constant time after preprocessing.
- **Completeness theorem.**
  - 1994 abstract: RISA is NLINEAR-complete, "consequently NLINEAR ≠ DLINEAR iff RISA ∉ DLINEAR".
  - The reduction class is stated two ways in Grandjean-school papers, and the 1994 text could not be checked:
    - Chapdelaine 2006, p. 1 (Introduction): complete "under linear-time computable reductions", citing the 1990 paper.
    - Chapdelaine–Grandjean 2006, p. 2: "NLIN-complete via DTIME_TM(n) reductions", citing the 1990 paper.
  - 1990 abstract: every NTIME_TM(n) problem reduces to RISA in linear time on a deterministic TM, via generalized spectra of sentences ∀y ⋀ F_i(y) = G_i(y) with unary function words.
- **SAT's status.**
  - 1994 abstract: "this paper argues that propositional satisfiability is not NLINEAR complete."
  - Chapdelaine 2006, p. 2: SAT does not seem NLIN-complete because it uses only O(n/log n) nondeterministic instructions (citing the 1994 paper). Many natural NP-complete problems are linearly equivalent to SAT (citing Barbanchon–Grandjean 2002, Creignou 1995, Dewdney 1982, Grandjean 1996).
  - Chapdelaine–Grandjean 2006, p. 2: SAT is "complete" for quasi-linear time O(n (log n)^{O(1)}) under quasi-linear-time, log-space reductions (citing Cook 1988, Dewdney 1982, Schnorr 1978). So, as far as these sources state, SAT is NLIN-hard only under quasi-linear reductions and is conjectured not NLIN-complete under linear ones.
  - The claim that Grandjean "puts SAT at the bottom" rests only on a search summary of the 1996 paper ("SAT is, in some sense, a minimal NP-complete problem"). It is unverified.

### 2.2 The known RISA lower bound

- **The bound.** The 1990 abstract defines "linearly NP-complete" (every NTIME_TM(n) problem reduces in deterministic linear TM time) and shows it implies L ∉ DTIME(cn) for every c ≥ 1. It proves RISA linearly NP-complete. The separation used is PPST's ∪_c DTIME(cn) ⊊ NTIME(n), as quoted in the 1988 abstract.
- **Model: multitape Turing machines only.** Chapdelaine–Grandjean 2006, p. 2, call the RAM version, RISA ∉ DLIN, "much more significant", and say it is equivalent to DLIN ≠ NLIN.
- **Why it does not reach the RAM** (standard background, not from the sources read). The PPST step is a Turing-machine speedup through block-respecting computation graphs with small segregators. The journal records why segregator arguments fail for RAM access graphs, which can be grates or expanders (barrier (f) of the barrier note). [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)
- **The one proved RAM separation in this line.** Grandjean–Olive 2004 (abstract) prove vertexNLIN ≠ vertexDLIN, with time O(|V|) on graphs of size |V|+|E|. That clock is below input size: see test (b) in Section 3.

### 2.3 Units dictionary and Lemma A

| Quantity | Journal model B | Grandjean model G |
| --- | --- | --- |
| Input size | N bits, packed into w-bit words | N_G registers holding O(N_G) values. Graphs: N_G = Θ(m+n) and bit length Θ(N_G log N_G) (2022, eq. (19)). Words: N_G = Θ(n/log n) with the packed convention, N_G = n with one letter per register (2022 §10, p. 53) |
| "Linear time" | O(N) steps | O(N_G) steps. That is O(N/log N), the journal's packed-scan clock, on structures and packed words, and O(N) with one letter per register |
| Memory | addresses up to about N^{12}, sparse, zero-initialized | contents and addresses O(N_G), linear space |
| Operations | +, −, ×, div, shifts, Boolean | + only; equivalent after linear preprocessing (2022) |
| Guess | one word | one register (guess(A)) |

The 2022 paper states the clock point itself, on p. 53: with the packed word input, a RAM running O(N) unit-cost steps runs in O(n/log n) steps, and it is "a large and challenging goal" to determine which word problems known to be linear-time can be done in O(n/log n).

It also lists a deterministic question as open, at §10 p. 54 (with the setting introduced in §2.5): is a RAM with k-dimensional arrays that uses only O(N) cells equivalent to the 1-dimensional O(N)-memory RAM? Its Theorem 1 reduces arbitrary dimension only to N × N^ε arrays. The journal's polynomial address space (about N^{12} addresses, O(N) cells touched in linear time) is exactly this case.

**Proof of Lemma A** (manuscript level, checked by hand, not formalized).
1. **Pad.** Fix L ∈ NTIME_B[N], decided by an NRAM P in at most kn steps. Let y = x 0 1^{p}, with p = n⌈log2(n+2)⌉ and m = |y|. Its packed G-input has N_G = Θ(m/log m) = Θ(n) registers.
2. **L' = {x01^p : x ∈ L} is in NLIN.**
   - Build the 2022 tables in O(N_G).
   - Check the padding registers in O(N_G).
   - Re-block x into B-words. One B-word is O(1) G-factors, joined by constant-time concatenation and substring after preprocessing (2022 §8.1).
   - Guess P's run as at most kn records: instruction, operand values, result and address. Each value is a 12-log-bit word, i.e. a polynomial integer in O(1) registers. Check each record in O(1).
   - Check memory consistency: radix-sort the (address, time) keys, which are below N_G^{O(1)}, with base N_G. That is O(1) counting-sort passes of O(N_G) time and space. Then check that every load returns the last store, or 0.
   - The nondeterministic side never needs a deterministic sparse dictionary.
3. **Apply ¬G.** By NLIN = DLIN, a deterministic G-RAM D decides L' in O(N_G) = O(n) steps.
4. **Run D on B.** The B-RAM on x simulates D on the virtual y. Each G-input register is O(1) shifts and masks of x's words, or the constant all-ones factor. D's O(N_G)-bounded addresses index a direct array, at O(1) B-steps per D-step.

So L ∈ DTIME_B[N], which proves ¬G ⇒ ¬M.

If words are instead given one letter per register, the same proof works without padding; precompute x's B-words as O(1)-register integers by Horner's rule in O(n), so later reads cost O(1). Either way M ⇒ G, and T1 (no O(N) SAT) ⇒ M ⇒ G.

**Why the converse is not obtained.** From NTIME_B[N] = DTIME_B[N] one gets only that every bit-encoded NLIN problem is decidable in O(N_G log N_G) steps of the journal's RAM, because a G-input carries Θ(N_G log N_G) bits (eq. (19)). Even that is in journal-RAM steps, not G-steps. Padding moves a collapse upward in the clock, never downward by a log factor. For word languages at the bit-linear clock, DTIME_B[N] ⊆ DLIN would also need the open deterministic simulation above.

**Effect on the RISA route.** RISA is NLIN-complete under linear reductions in Grandjean units. In the journal's bit units:
- The generic NLIN → RISA reduction maps a t-step NRAM to O(t) transitions, which is O(t log t) bits. This is a reading of "linear reduction in register units" made here; the reduction itself was not read.
- So the known reduction makes RISA hard for the journal's NTIME_B[N] only with N log N-bit output: one log factor of loss. Any count-preserving reduction to full-table RISA must lose this factor. An R-bit full-table RISA instance has at most R witness bits, while a native instance can have Θ(N log N).
- The journal's own U_RAM already is the linear-reduction complete problem for NTIME_B[N]. The milestone was already "off SAT". [Native unary clock](native-unary-clock-band.md)

**Witness lengths in bits.** These explain Grandjean's SAT argument and the journal's Ω(s log² s) count-preserving compiler bound together:
- SAT has O(N/log N) witness bits (distinct names).
- RISA has O(N) witness bits when δ is given as a full |Q|×|Σ| table with undefined entries: the witness is the undefined entries, log|Q| bits each. It has Θ(N) when a constant fraction is undefined. If only defined transitions are listed, the completion can be much longer than the instance. (Count made here.)
- Native U_RAM has Θ(N log N): N guessed words.
- Each step is one log factor.

## 3. The three standard tests, in Grandjean units

No lower bound is claimed. These are the journal's tests rerun on RISA.
- **(a) Fast solver on the hard family.**
  - RISA's hard family under the completeness reduction is the image of all of NLIN. A packed-scan solver on it is a DLIN solver for NLIN, so test (a) is the open question itself.
  - Every family the journal built to carry a lower bound has a packed-scan solver on the journal's RAM. Where such a solver uses only O(N/log N) word addresses (O(N_G) registers), as scan-type solvers do, it is a DLIN solver and the family cannot witness G. Memory use was not checked for every journal family.
  - Restricted RISA families with fixed parameters are reportedly in P or SAT-equivalent (Creignou 1996, abstract via search only).
- **(b) The same bound for an easy language.**
  - The TM bound (RISA ∉ DTIME_TM(cn)) passes automatically. The method bounds only problems that are NTIME_TM(n)-hard under linear TM reductions, and by PPST none of these lies in ∪_c DTIME_TM(cn). But it is Turing-machine-only.
  - The one proved RAM separation in the line (vertexNLIN ≠ vertexDLIN) fails test (b), on an inference from the abstract. The same abstract states that 2-colourability ∉ vertexNLIN, although 2-colourability is deterministic O(|V|+|E|). So the clock-below-input-size setting yields lower bounds for easy problems: an input-access bound. That the two results share one method is inferred, not read.
- **(c) The oracle.**
  - The multilinear-oracle note collapses native nondeterministic, even alternating, linear time to deterministic, relative to A with its multilinear extension. [Multilinear oracle](multilinear-oracle-clock.md)
  - Its machine wrapper has budget B = |x|+|M|+O((t+1)w+w) and 4(B+|body|+1) padding ones, so its length is O(|x| + t·w).
  - For an NLIN source, |x| = Θ(N_G log N_G) bits and t = O(N_G), so the wrapper is O(N_G log N_G) bits and takes O(N_G) packed word writes. Hence NLIN^A = DLIN^A as well. This was checked by reading the wrapper's size formula, not by re-proving it; Grandjean's linear-memory model also needs the obvious query convention.
  - Any proof of G must therefore be non-relativizing, and in that note's sense non-algebrizing. The relativized-clock note (p = 1) already gives linear SAT relative to its oracle. [Relativized clock](relativized-clock.md)
- **Per-word argument.** The per-path caps of the capacity-line note limit the method to about n/w charged steps for every function. With n bits and w = Θ(log n), that is Θ(N_G): exactly Grandjean-linear time, which is the trivial input-reading bound in his units (on structures and packed words). So on RISA the method can at best reproduce the trivial Ω(N_G) input-reading bound, and it provably cannot give ω(N_G), which is what G needs. [Capacity line](the-instruction-capacity-line-is-capped-at-a-packed-scan.md)
- **Hierarchy and snapshot test.**
  - In Grandjean units a snapshot of s registers is s tokens. Kannan's split costs O(ps + N_G/p), so NLIN ⊄ DTISP_G(n, o(n)) by the argument of the native unary-clock note. That note's last paragraph already gives this normalization. It is not separately checked in the literature here.
  - But DLIN ⊆ DTISP_G(n, O(n)) trivially, so the bound is tight and the space route ends. In bit units the same bound leaves the log-factor gap the journal records.

## 4. The compiler criterion at packed-scan SAT time

The cap in the compiler-criterion note is h = K((u+1)L^b + (1+M/log(2+M))L^a), stated for a, β ≥ 0. Read term by term at a = −1 (SAT in O(N/log N)): [Compiler criterion](compact-compilers-and-linear-sat-time.md)
- **Solver term.** The solver runs O(W/log W) steps on the W-bit failure test, with W = Θ(n + M/log M).
- **Guessing the assignment.** W bits take W/w word guesses.
- **Building the failure test.** The note prices this at "O(W) encoded bits and word steps" (its §1 last paragraph). With that pricing the verifier alone costs Θ(M/log M), so halving needs M = o(s log s): the threshold stays at s log s.
- **A packed emitter would lower it.** If the verifier can emit the failure test in O(W/log W) word steps, the dominant cap is K·M/log² M and halving needs only M = o(s log² s). This is the reading under which the criterion reaches packed-scan SAT time.
  - Each chunk clause and each decoder gate has O(1) names of O(log W) decimal digits, so O(1) words each.
  - Decimal names and data digits can come from tables built in o(W) time.
  - Such an emitter plausibly exists, but it has not been written.
- **Emitter word-step count (sketch).** Items follow the compiler note's construction. Fix b = c·log W with c small, so a clause of O(log W) decimal bytes fits in O(1) words; tokens are ORed into a packed output buffer at O(1) each.
  - **Chunk clauses.** There are W/b = O(W/log W) of them. Each takes O(1) word steps: the chunk's data digits come from a table mapping (b/4)-bit pieces to ASCII digit strings, which has 2^{b/4} entries and is built in o(W).
  - **Decoder gates.** Their number is linear in the number of chunks, summed over the O(log W) position tables: O(W/log W) gates. Each is O(1) clauses with O(1) names. A name is the decimal form of an integer below W^{O(1)}, obtained in O(1) steps by division by a fixed power of ten plus a table for integers below W^{1/4}.
  - **Library.** O(b·2^b) clauses at O(1) steps each, which is o(W/log W) once 2^b ≤ W^{1/2}.
  - **Source multiplexing and polylogarithmic checks.** O(n·polylog T) steps, which is o(t) while t > n^{3/2}.
  - **Header and pins.** O(1) per clause and O(1) for the header.
  - **Total.** O(W/log W + n·polylog T) word steps. This is a count, not code. The SAT solver also needs the formula physically contiguous, which the buffer provides.
- **Threshold arithmetic.** `python3 compiler_criterion_packed_threshold.py` computes only this, not the emitter. Key lines: [compiler_criterion_packed_threshold.py](../audits/compiler_criterion_packed_threshold.py)
  - `a=-1 beta=1.9  e=20,40,64,128,512 : 0.500 0.539 0.560 0.558 0.519`: h/t at s = 2^e, with c = K = 1. Halving is not yet achieved at e = 512.
  - `a=-1 beta=2.0  e=20,40,64,128,512 : 0.665 0.771 0.842 0.901 0.966` and `e=1000000  ratio/K = 1.0000`: at β = 2 the ratio tends to K·c. Halving would need K·c < 1/2, but K contains the hypothetical solver's constant, so M = o(s log² s) is genuinely needed.
  - `a=-1 beta=1.9 : K=1: 1.02e+03 K=4: 1.07e+09 K=16: 1.13e+15`: the eventual log2(s) thresholds, which are identical to those for a = 0, β = 0.9. Only β + a matters.
- **What a = −1 would exclude.** It would exclude only SAT ∈ DTIME_B[N/log N]. It does not reach O(N).
  - **It would also give G directly.** Under NLIN = DLIN, SAT ∈ DLIN with one register per literal. So the verifier can emit each failure test as Grandjean's integer list, with O(W/log W) entries by the count above, and run the DLIN algorithm on it in O(W/log W) steps.
  - **The general implication is not established.** "SAT ∉ DTIME_B[N/log N] ⇒ SAT ∉ DLIN" fails to follow: on DIMACS files with Θ(N) short literal occurrences, a DLIN algorithm takes Θ(N) steps.
- **Coincidence with the count-preserving bound.** The o(s log² s) threshold is exactly the note's own Ω(s log² s) lower bound for count-preserving compilers. So a qualifying compiler cannot make the model count a positive multiple of the accepting-branch count on the compiler note's OR-of-guesses family. This parallels, in bit units, Grandjean's witness-length reason for doubting that SAT is NLIN-complete.
- **Robson 1991.** "An O(T log T) reduction from RAM computations to satisfiability" (title only). If its O(T log T) counts literal occurrences for log-word RAMs, it sits at Θ(s log² s) bits, at this threshold up to the o(·). This was not checked.

## 5. Exact obstruction and next step

**Obstruction.** In Grandjean units G = NLIN ≠ DLIN asks for an ω(N_G) lower bound, i.e. one beyond packed-scan time on structures and packed words. That is exactly where the journal's barriers sit (the packed-scan solvers of the recorded obstacle 2, and the oracle worlds (b) and (c) of the barrier note):
- The per-word cap is Θ(N_G).
- Every journal hard family has a packed-scan solver. That solver is a DLIN solver where it uses O(N_G) registers; this was not checked for every family.
- The multilinear-oracle collapse transfers.

The segregator obstruction ((f) of the barrier note) is, on this reading, what keeps the PPST/RISA Turing-machine proof off the RAM. That explanation is standard background plus the journal's barrier record, not taken from the sources read here. Moving the milestone to RISA renames the target and removes no barrier. By Lemma A (under H_N and H_D for the 1994 classes) it is implied by the journal's milestone; whether the two are equivalent is open. [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)

**Next lemmas, if this line is kept:**
1. **A downward translation**, "NTIME_B[N] = DTIME_B[N] ⇒ NLIN = DLIN". It would make the two milestones equivalent. No mechanism for it is known here.
2. **A RAM analogue of the PPST speedup at Grandjean scale**, DLIN ⊆ Σ_k-TIME_G(o(N_G)). This is route B/C of the barrier note in Grandjean units, and the segregator obstruction is unchanged.
3. **For the compiler criterion:** write the packed failure-test emitter (O(W/log W) word steps) and restate the criterion for a ∈ [−1, 0). That would show that an o(s log² s) local compiler gives SAT ∉ DTIME_B[N/log N]. It would also give NLIN ≠ DLIN directly, by running a DLIN SAT algorithm on failure tests emitted as integer lists (Section 4). This is a concrete, checkable step.

## 6. What is not proved

- Lemma A is a hand proof. It relies on the 2022 constant-time arithmetic and concatenation after preprocessing, and on a radix-sort step argued directly. It is not formalized.
- Lemma A's step "⇒ RISA ∉ DLIN" also rests on H_N and H_D: the 1994 NLINEAR contains the addition NRAM with one-register guesses, and 1994 DLINEAR machines run in linear time on the journal's RAM. Grandjean–Jachiet 2022, p. 55, supports both in part. Neither is verified.
- The converse of Lemma A is open, not refuted.
- The exact 1994 completeness theorem (model, I/O convention, reduction class) is not verified: abstract only.
- The 1990 and 1996 papers are not read. Grandjean's "bottom of NP-complete problems" claim and Creignou's restricted-RISA results are unverified.
- The oracle transfer in Section 3(c) rests on reading the wrapper's cost, not on a new proof.
- The packed failure-test emitter in Section 4 is a sketch. So the s log² s threshold at a = −1 is conditional.
- No statement here bounds SAT or RISA on any RAM beyond the trivial Ω(N_G).

## Reproducing the check

Run `python3 compiler_criterion_packed_threshold.py` from `audits/`; it prints the threshold arithmetic of Section 4 in well under a second. The text-extraction tools used to read the arXiv PDFs are not part of the journal.
