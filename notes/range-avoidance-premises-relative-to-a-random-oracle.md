# Relative to a random oracle the Li–Tell avoidance premise fails and the one-index premise holds

With probability 1 relative to a random oracle, Li and Tell's average-case range-avoidance premise (their Assumption 1.1, and with it the premise of their Theorem 1.3) is false, and the journal's one-index range-hitting premise is true. Both statements are proved under a standard convention for space-bounded oracle machines (Ladner–Lynch style; the source was not re-read), in which the query tape is write-only, is not charged to space, and is erased at each query; they depend on that convention. They are statements about the premises only. The proof of the journal's conditional SAT implication does not carry over to this oracle model, the implication is not claimed to relativize, and nothing here gives an unconditional or a relativized SAT bound. The linear, quadratic and cubic questions remain open.

With probability 1 over a random oracle O:

- (i) Li–Tell's Assumption 1.1 is false relative to O. So is the stronger premise of their Theorem 1.3. A two-level printer refutes both: its single intermediate label is longer than the evaluator's workspace plus seed, which makes it a one-pebble instance.
- (ii) The journal's one-index-per-length premise holds relative to O. One universal family, fixed before the avoider, hits every avoider that runs in time at most 2^{s(n)-1}, at every sufficiently large length.

Section 4 restates the conditional headline on the one-index premise, with exact quantifiers. That restatement is not new mathematics: the paragraph "How much hardness would suffice?" of the uniform-avoidance note already states the one-index premise as sufficient, and so does the steering entry of 26 November on the revised range-avoidance premise. The new content of this note is the pair of oracle statements. [Uniform avoidance proof](near-linear-sat-and-uniform-low-space-range-avoidance.md) · [Steering entry](../research-steering.md)

The chain to an unconditional SAT bound still needs the one-index premise without an oracle. That premise implies P ≠ PSPACE (journal).

Li and Tell fix no oracle model, so the convention is this note's choice. Under it, the universal family U of (ii) is eligible only because the uncharged tape lets an O(log n)-space evaluator write Θ(n)-bit queries. The proof of the journal's SAT implication does not carry over under it, because the Nepomnjaščii step cannot write the long queries (Section 5). The implication itself is not claimed to relativize. So (ii) yields no relativized SAT bound and is not evidence for an unconditional one.

Write *the Li–Tell avoidance premise* for Assumption 1.1 with p = n^{-ω(1)}, together with the simultaneous-time requirement of Theorem 1.3. Relative to Q = TQBF, under the same convention, the Li–Tell avoidance premise and the one-index premise are both true (Section 5). The circuit-hardness conjunct of Theorem 1.3 is not examined relative to Q.
- **The avoidance premise.** It is false relative to a random oracle and true relative to Q. So under this convention it can be neither proved nor refuted by a relativizing argument.
- **The one-index premise.** It is true relative to both oracles, so no relativizing argument can refute it. No oracle here falsifies it.

If the convention charges the query tape to the space bound, (i) becomes trivial and (ii) is **not** proved here.

## Sources

- Z. Li, R. Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, ECCC TR26-233 revision 1, 26 Nov 2026, https://eccc.weizmann.ac.il/report/2026/233/revision/1/download/. I downloaded the PDF and extracted its text with pypdf.
  - **Read in part.** Read: the abstract; all of Section 1 (Assumption 1.1, Theorems 1.2–1.8, Section 1.5, footnotes 5, 7, 11); Section 2.1 and the start of 2.2; from Section 3, Definitions 3.1–3.3 and 3.11–3.12 and Theorems 3.8, 3.13 and 3.14; Theorem 5.4, Remark 5.5, Theorem 5.6, Corollary 5.7, and Theorems 5.8–5.9 with their proofs; Definition 5.13 and Theorem 5.14 with its proof; Section 6.4 (Theorems 6.12–6.13 with the proof).
  - Not read: Section 4 (the PCP), Section 5.1 before Theorem 5.4, Theorem 5.12, Sections 6.1–6.3, Section 7, and the appendix.
  - Theorem 5.12 is cited in Section 3 only for its role in the direction (2)⇒(1) of Theorem 5.14. That role is taken from the proof of Theorem 5.14, which invokes it; the statement of Theorem 5.12 itself was not read for this note.
- Bennett–Gill 1981 (P^A ≠ NP^A for a random oracle A): not accessed. Used only as context in Section 5.
- Ladner–Lynch 1976 (relativized space convention): not accessed. Section 2 states the convention explicitly, so nothing depends on the citation.
- Random-oracle pebbling theorems (Dwork–Naor–Wee 2005; Dziembowski–Kazana–Wichs 2011; Alwen–Serbinenko 2015): not accessed. They are cited only in a remark and are not used in any proof.
- Journal, read: [Uniform avoidance proof](near-linear-sat-and-uniform-low-space-range-avoidance.md) · [Unread words](unread-words-in-a-range-avoidance-index.md) · [Linear evaluator space](near-linear-avoidance-with-linear-evaluator-space.md) · [Relativized clock](relativized-clock.md) (first part). Also the results entry "Conditional unrestricted RAM bound from uniform range avoidance" and the three steering paragraphs that cite Li and Tell: the 26 November entry on the revised premise, the paragraph on their October version, and the paragraph on their footnote 1. The README does not cite them. [Results entry](../RESULTS.md#result--a-superlinear-boolean-circuit-lower-bound-for-3-sat) · [Steering](../research-steering.md)

## 1. The premise as stated in the primary text

**Assumption 1.1 (Li–Tell, p. 3).** Let p: N → (0,1). For every sufficiently small constant ε > 0 and every deterministic polynomial-time algorithm A, there is a family of Avoid instances C = {C_x} with the following properties:
- C stretches |x|^{ε²} bits to |x|^ε bits;
- C is evaluable in space |x|^{ε²};
- for every sufficiently large n, Pr_{x∈{0,1}^n}[A(x) solves Avoid(C_x)] ≤ p(n).

**Theorem 1.3 (Li–Tell, p. 4).** Assume three things:
- DSPACE[O(n)] ⊄ i.o.SIZE^SAT[2^{δn}] for some δ > 0;
- Assumption 1.1 holds with p(n) = n^{-ω(1)};
- for each sufficiently small ε > 0 and each deterministic polynomial-time A, the family witnessing the assumption for ε and A is evaluable in simultaneous time poly(n) and space n^{ε²}.

Then for every L ∈ P there are a constant k = k_L and a linear-time Σ_k machine that decides L correctly on at least a 1 − n^{-ω(1)} fraction of the n-bit inputs. Theorem 5.9 restates this with the fraction 1 − 3(p(n^{O(1)}) + 2^{-polylog n}).

"A(x) solves Avoid(C_x)" means A(x) ∉ Range(C_x) (Definitions 3.11–3.12). In "evaluable" (Definitions 3.2–3.3), a Turing machine M gets (x, y, i) and prints bit i of C_x(y) within the stated bound. So the premise says this: for every polynomial-time printer A, some low-space evaluator reproduces A(x) from some seed on all but an n^{-ω(1)} fraction of indices, at every large length. In Theorem 1.3 that evaluator must also run in polynomial time. The family is chosen after A.

## 2. Oracle model

- **Oracle.** O: {0,1}* → {0,1}, with independent uniform bits. "With probability 1" refers to this product measure.
- **Convention LL (used for Theorems A and B).** A deterministic oracle Turing machine has:
  - a read-only input tape;
  - binary work tapes, which are charged to space;
  - one write-only oracle tape, which is not charged.

  Entering the query state with q on the oracle tape returns O(q) and erases the tape.
- **Convention CH.** As LL, except that the oracle tape is charged to space.
- **Encoding.** Oracle points are encoded with a prefix-free tuple code ⟨·⟩, so that a string decodes to at most one tuple. Leading tags 0, 1, 2, 3 keep the domains disjoint.
- **Configurations.** Take a machine with space bound S on inputs of length N. Its configurations with an empty oracle tape (state, head positions, work contents) number at most 2^{S'}, where S' = O_M(S + log N).

**Lemma 0 (LL).** Consider the string a machine writes on the oracle tape between two consecutive queries, or before the first query. It is a function of the input and of the configuration right after the preceding answer (or at the start), and it does not depend on O.
*Proof.* No answer arrives while the string is being written, and the machine is deterministic. ∎

## 3. The two oracle theorems

Fix a rational ε ∈ (0,1). Write s = s(n) = ⌊n^{ε²}⌋ and m = m(n) = ⌊n^ε⌋.

### Theorem A (part (i): the average-case premise fails relative to O)

**The printer.** On x ∈ {0,1}^n, A^O computes two things:
- the label ℓ(x) = (O⟨0,x,1⟩, …, O⟨0,x,n⟩) ∈ {0,1}^n, which takes n queries;
- the output A^O(x) = (O⟨1,ℓ(x),1⟩, …, O⟨1,ℓ(x),m⟩), which takes m queries, each writing ℓ(x) from the work tape.

So A^O runs in polynomial time and uses O(n) space.

**Capped families.** For an oracle machine M and a constant c, let C^{M,c} be the family with C_x(u)_i equal to the output of M^O(x,u,i) if that run halts within c·n^{ε²} work cells, and 0 otherwise. Every family that is evaluable in space O(n^{ε²}) relative to O equals some C^{M,c}. No running time is imposed.

**Claim.** With probability 1 over O, for every M and c and all sufficiently large n,

  Pr_{x∈{0,1}^n}[A^O(x) ∈ Range(C^{M,c}_x)] ≤ 2^{-n^ε/4}.

So relative to O, A^O solves Avoid(C_x) on all but a 2^{-n^ε/4} fraction of indices, for every family that is evaluable in space O(n^{ε²}). Hence, for every rational ε ∈ (0,1) and every p with p(n) < 1 − 2^{-n^ε/4} for infinitely many n, the instance of Assumption 1.1 at that ε fails relative to O, even with no time bound on the family.

Assumption 1.1 quantifies over all sufficiently small ε. Refuting it therefore needs failure at arbitrarily small ε, where the condition on p is strictest. So Assumption 1.1 itself fails relative to O for every p such that, for some constant c, p(n) ≤ 1 − n^{-c} for infinitely many n. In particular it fails for p = n^{-ω(1)} and for p = 1/2.

Since Assumption 1.1 fails, the stronger premise of Theorem 1.3 fails as well.

**Proof.** Fix M, c, n and x. Put S = c·n^{ε²} and N = |(x,u,i)| = O(n), so that S' = O(n^{ε²}).

(a) **The writable-string set.** Let Q_x be the set of strings that M, on some input (x, u, i), can write within the space cap starting from some configuration with an empty oracle tape. By Lemma 0, |Q_x| ≤ 2^s · m · 2^{S'}, and Q_x does not depend on O.

Let W_x be the event that some capped run M^O(x,u,i), for any u and i, submits a query ⟨1, ℓ(x), j⟩. Under W_x, ℓ(x) is the second component of some string in Q_x. But ℓ(x) consists of the n oracle bits at the tag-0 points of x, so it is uniform on {0,1}^n. Hence

  Pr[W_x] ≤ |Q_x| · 2^{-n} ≤ m · 2^{s+S'-n}.

(b) **Conditioning outside B_x.** Let B_x = {⟨1,ℓ(x),j⟩ : j ∈ [m]}. Condition on every oracle value except those on B_x. This fixes ℓ(x), and hence B_x, because the tag-0 points lie outside B_x. Two facts follow:
- **¬W_x is determined.** Simulate every run. A run that never queries B_x is fully determined, and W_x holds exactly when some run reaches a query in B_x.
- **The range is fixed on ¬W_x.** Every run is then determined, so Range(C_x) is a fixed set of at most 2^s strings.

Meanwhile A^O(x) = O|_{B_x} is uniform on {0,1}^m. Hence Pr[¬W_x ∧ A^O(x) ∈ Range(C_x)] ≤ 2^{s-m}.

(c) **Summing up.** From (a) and (b), Pr_O[A^O(x) ∈ Range(C_x)] ≤ m·2^{s+S'-n} + 2^{s-m}. For large n this is at most 2^{2-n^ε/2}. The first term is at most 2^{-n/2}, because s + S' + log m = O(n^{ε²}) = o(n). The second is at most 2^{1/2-n^ε/2}, because s ≤ m/2 eventually and m ≥ n^ε − 1.

Let F_n be the fraction of x ∈ {0,1}^n that are hit, so E F_n ≤ 2^{2-n^ε/2}. By Markov's inequality, Pr[F_n > 2^{-n^ε/4}] ≤ 2^{2-n^ε/4}, which is summable in n. By Borel–Cantelli, almost surely F_n ≤ 2^{-n^ε/4} for all large n. A countable union over the pairs (M, c) completes the proof. ∎

**Remarks on Theorem A.**
- **Pebbling.** The printer's dependency graph has one intermediate node. Its label has n bits, while the workspace plus seed has O(n^{ε²}) bits. So this is a one-pebble instance with an over-long label.
  - **Under LL a one-level printer does not work.** For A(x) = (O⟨x,1⟩, …, O⟨x,m⟩), an evaluator copies x and i onto the query tape in O(log n) space and reproduces A(x) exactly, for every seed. The sanity script illustrates this (Section 9).
  - **Other conventions.** Suppose the model allowed two uncharged oracle tapes. Then ℓ(x) could be streamed onto the second tape bit by bit while the first tape asks for its bits, and the two-level printer would be computable in O(log n) space. One would then need a DAG whose labels are shorter than the space and whose pebbling number grows faster than (space + seed)/(label length). The random-oracle pebbling theorems listed under Sources are the relevant tools. That case is **not proved here**.
- **Under CH.** The one-level printer already works: the evaluator cannot write queries of length above c·n^{ε²}, so step (b) applies directly with W_x empty.
- **Consistency with Li–Tell.**
  - **Their Theorem 5.14 relativizes in one direction.** The chain (1)⇒(3)⇒(2) is elementary (a universal simulation and truncation) and relativizes under LL. So relative to O, its item (1) must fail: low-space average-case simulation of FP. It does fail. The same proof with s = 0 shows that no space-O(n^{ε²}) machine M agrees with A^O on more than a 2^{-n^ε/4} fraction of inputs. The per-input bound is m·2^{S'-n} + 2^{-m}.
  - **Theorem 1.3 is not contradicted.** Relative to O, the premise of Theorem 1.3 and item (2) of Theorem 5.14 are false. So Theorem 1.3 and the direction (2)⇒(1) are vacuous there and cannot be contradicted, whether or not their proofs relativize. Theorem 1.3 goes through Theorems 5.4, 5.1 and 4.1; (2)⇒(1) goes through Theorems 5.12 and 4.1. The relativized failure shows only that no relativizing argument can prove the premise.
  - **An unrelativized cousin: Li–Tell's Theorem 6.12.** It assumes a circuit lower bound for E. Then for each fixed P-evaluable family it gives a deterministic polynomial-time algorithm that avoids the family's range on all but a 2^{ℓ−m} + n^{−k} fraction of indices. That algorithm depends on the family and runs longer than the family's evaluator. Theorem A is a random-oracle analogue in which one printer works against every low-space family at once, with no time bound on the family.
  - **It matches the authors' heuristic.** Section 1.5 says an algorithm for low-space Avoid is at least as hard as computing a function that is hard for low space. Relative to O such a function exists in FP^O.

### Theorem B (part (ii): the one-index premise holds relative to O)

**The universal family.** For x ∈ {0,1}^n and u ∈ {0,1}^s, define U^O_x(u) = (O⟨2,x,u,1⟩, …, O⟨2,x,u,m⟩). Under LL its bit evaluator copies (x, u, i) onto the oracle tape and makes one query. That takes time O(n) and work space O(log n). So U is eligible: simultaneous polynomial time and O(n^{ε²}) space.

**Claim.** With probability 1 over O, the following holds for every deterministic oracle Turing machine A that has an explicit clock t(n) ≤ 2^{s(n)-1} and outputs m(n) bits: for all sufficiently large n, some x ∈ {0,1}^n has A^O(x) ∈ Range(U^O_x).

In particular, the journal's one-index premise WP(ε) of Section 4 holds relative to O, in a strong form:
- the family does not depend on A;
- the hits occur at all large lengths, not just infinitely many;
- the hit avoiders include all those with running time up to 2^{s-1}, for example 2^{n^{ε²}/2}, not only polynomial-time ones.

**Proof.** Fix A and n, and put t = t(n) and K = 2^n. List {0,1}^n as x_1, …, x_K in lexicographic order. Sample the oracle lazily, drawing each value when it is first needed. Step j consists of three parts:
1. Run A on x_j, drawing values at newly queried points.
2. Let τ_j be the number of points of block x_j (the points ⟨2,x_j,·,·⟩) drawn so far.
3. Draw all remaining points of block x_j, and let H_j be the event A^O(x_j) ∈ Range(U_{x_j}).

Let G_j be the information drawn before part 3 of step j.

- **Fresh seeds.** A seed u is fresh at step j if none of its m points has been drawn. At least f_j := max(0, 2^s − τ_j) seeds are fresh.
- **Fresh seeds are untouched.** G_j fixes A^O(x_j), because the run is complete. G_j does not involve the fresh points: block x_j was not completed at any earlier step, since the indices are distinct, and no run so far queried them.
- **Per-step bound.** The fresh strings U_{x_j}(u) are independent and uniform on {0,1}^m, and ¬H_j requires each of them to differ from A^O(x_j). Hence Pr[¬H_j | G_j] ≤ (1 − 2^{-m})^{f_j} ≤ exp(−2^{-m} f_j).
- **Budget.** Σ_j τ_j ≤ K·t. Each drawn point lies in at most one block. A point counted in τ_j was queried by some run, because blocks are completed only at their own step and never counted again. So Σ_j f_j ≥ K(2^s − t).
- **Supermartingale.** Let Y_k = 1[¬H_1 ∩ … ∩ ¬H_k] · exp(2^{-m} Σ_{j≤k} f_j). Both Y_{k-1} and f_k are determined by G_k, so E[Y_k | G_k] = Y_{k-1} · e^{2^{-m} f_k} · Pr[¬H_k | G_k] ≤ Y_{k-1}. Hence E Y_K ≤ 1.
- **Conclusion at length n.** On the no-hit event, Y_K ≥ exp(2^{-m} K (2^s − t)). Therefore

  Pr[no x ∈ {0,1}^n is hit] ≤ exp(−2^{n+s-m}(1 − t·2^{-s})) ≤ exp(−2^{n+s-m-1}).

Since n + s − m ≥ n − n^ε → ∞, these bounds are summable over n. By Borel–Cantelli, almost surely A is hit at all but finitely many lengths. There are countably many clocked machines, so almost surely all of them are hit simultaneously. ∎

**Remarks on Theorem B.**
- **Where "outputs shorter than indices" enters.** The expected number of hits at length n is about 2^{n+s-m}. It diverges because m = n^ε < n.
- **The hit fraction depends on the printer.**
  - A printer that does not query block x is hit by U on only about a 2^{s-m} fraction of indices. Examples are the constant printer and the printer of Theorem A. That fraction is far below the 1 − n^{-ω(1)} that Assumption 1.1 demands.
  - A printer that outputs U_x(0^s) is hit on every index.
- **Why the family can come before A.** Relative to O, A sees at most t of the 2^s strings in its own block. Even knowing U, it cannot steer around the rest.
- **Under CH this proof fails.** U is not eligible under CH, because its queries are longer than n. Consider the CH analogue U′_x(u) = (O⟨3,n,u,1⟩, …, O⟨3,n,u,m⟩), with n in binary, whose queries have length O(n^{ε²}). Its rows at length n are 2^s uniform strings, the same for every x. So the constant printer 1^m escapes it at all but finitely many lengths almost surely, since Σ_n 2^{s-m} < ∞. (The specification matters. If each (x,u,i) could select its own short point, there could be up to 2^{n+s} distinct rows, and this union bound would fail.) This does not mean the constant printer escapes every CH family: C ≡ 1^m hits it. Whether WP(ε) holds relative to a random oracle under CH, with families tailored to A, is **not settled here**.

## 4. The restated headline with exact quantifiers

**Eligible family.** Fix a rational ε ∈ (0,1), with s(n) = ⌊n^{ε²}⌋ and m(n) = ⌊n^ε⌋. An eligible family is C = {C_x} with C_x: {0,1}^{s(|x|)} → {0,1}^{m(|x|)}, together with a multitape Turing machine M and a constant c, such that for every x, u and i, M on input (x, u, i) prints bit i of C_x(u) within c·|x|^c steps and c·|x|^{ε²} work cells.

**WP(ε), the one-index premise.** For every deterministic polynomial-time multitape Turing machine A that prints m(|x|) bits on input x, there are an eligible family C and infinitely many n such that, for each of those n, some x ∈ {0,1}^n has A(x) ∈ Range(C_x). In symbols: ∀A ∃C ∃^∞n ∃x∈{0,1}^n ∃u∈{0,1}^{s(n)}: C_x(u) = A(x).

**Restated headline.** If WP(ε) holds for some rational ε ∈ (0,1), then there is an η > 0 such that no deterministic logarithmic-word RAM with unrestricted workspace decides explicit 3-SAT (DIMACS, with N encoded bits) in worst-case time O(N^{1+η}).

The value of η is not specified. The proof in the uniform-avoidance note refutes only the statement "for every η > 0 there is such a RAM", where each η may use its own program. [Uniform avoidance proof](near-linear-sat-and-uniform-low-space-range-avoidance.md)

**The restatement is not new mathematics.** That note's paragraph "How much hardness would suffice?" already states WP(ε) as sufficient, and the steering entry of 26 November on the revised premise states it too. The results entry "Conditional unrestricted RAM bound from uniform range avoidance" is phrased with the stronger Li–Tell premise; the restated headline is the same implication from the weaker premise. [Results entry](../RESULTS.md#result--a-superlinear-boolean-circuit-lower-bound-for-3-sat)

**How WP(ε) is weaker than the Li–Tell premise of Theorem 1.3.**

| | WP(ε) | Li–Tell premise |
|---|---|---|
| Hit indices | one index per length | all but an n^{-ω(1)} fraction |
| Lengths | infinitely many | all sufficiently large |
| ε | one rational ε | every sufficiently small ε |
| Circuit premise DSPACE[O(n)] ⊄ i.o.SIZE^SAT[2^{δn}] | none | required (but not used by the journal's implication) |

Both premises choose the family after A (∀A ∃C). They use the same eligibility up to the space constant: simultaneous polynomial time and space n^{ε²} (Li–Tell) or c·n^{ε²} (WP(ε), which only weakens it). The Li–Tell premise implies WP(ε) for every sufficiently small rational ε, because a success probability below 1 at all large n leaves at least one hit index at each such n. It does not imply WP(ε) for a fixed larger ε.

**Linear endpoint.** The linear-evaluator-space note already states its premise in one-index form: "every printer running in the displayed n2^{O(H)} time has one polynomial-time, linear-workspace evaluator that reproduces its output with one seed on some index at infinitely many lengths". That premise is sufficient for excluding O(N) SAT, but the note does not prove it. Theorem B applies to it verbatim relative to a random oracle under LL, for three reasons: [Linear evaluator space](near-linear-avoidance-with-linear-evaluator-space.md)
- U uses O(log n) work space, which is within linear workspace.
- The seed and output lengths are the same, ⌊n^{ε²}⌋ and ⌊n^ε⌋.
- Printers running in time n·2^{O(H)} = n^{1+o(1)} are within the clock bound 2^{s-1}.

So that one-index premise also holds relative to a random oracle. This transfer is a direct reading of Theorem B; it is not written out separately.

## 5. The relativization picture, and the exact obstruction

- **Random O (LL).** The Li–Tell avoidance premise is false (Theorem A), and WP(ε) is true (Theorem B).
- **PSPACE-complete oracle Q = TQBF (LL): the Li–Tell avoidance premise and WP(ε) are both true.**
  - Take any P^Q printer A. Its bit language {(x,u,i) : A^Q(x)_i = 1} is in P^{TQBF} = PSPACE, so it log-space reduces to Q.
  - An LL evaluator streams that reduction onto the uncharged query tape and makes one query. This takes polynomial time and O(log n) work space.
  - So C_x(u) := A^Q(x) is eligible and hits A on **every** index at every length.

  Hence, relative to Q = TQBF under LL, the Li–Tell avoidance premise and WP(ε) are both true. The circuit-hardness conjunct of Theorem 1.3 is not examined relative to Q. An unchecked sketch suggests it plausibly holds too: under LL a linear-space Q-machine can stream a 2^{O(n)}-long TQBF instance. So DSPACE^Q[O(n)] contains a SPACE(2^{O(n)}) language that diagonalizes against SIZE^{SAT^Q}[2^{δn}].

  Whether the journal's obstruction relativizes depends on how PSPACE^Q is defined. The obstruction is "if P = PSPACE, one polynomial-time algorithm eventually avoids every simultaneous evaluator".
  - **PSPACE^Q with polynomially bounded queries.** Then P^Q = PSPACE^Q, yet WP(ε) holds relative to Q for LL evaluators. So the obstruction does not relativize in this mixed setting. Its proof needs a common resource cap on the evaluators. Under LL a space cap does not bound query length, and the polynomial clocks have exponents chosen after A.
  - **PSPACE^Q under LL as well.** Then PSPACE^Q contains EXPSPACE, because a polynomial-space machine can stream an exponentially long TQBF instance. So P^Q ≠ PSPACE^Q, and the obstruction is vacuous relative to Q.
- **The results are convention-sensitive.** Under LL, L^{TQBF} already contains PSPACE, because log-space reductions stream onto the uncharged tape. So all of these oracle statements depend on the convention.
- **Consequence under LL.**
  - The Li–Tell avoidance premise is false relative to a random oracle and true relative to Q. So neither a proof nor a refutation of it relativizes. The avoidance premise already fails relative to the random oracle, so this conclusion does not depend on the circuit conjunct.
  - WP(ε) is true relative to both oracles. No oracle here falsifies it, so nothing here shows that a proof of WP(ε) must be non-relativizing. Conversely, under LL no relativizing argument can refute WP(ε).
- **Under CH.** Queries have at most c·n^{ε²} bits, so the common space cap n² also bounds query length. The journal's obstruction should then relativize to Q and make WP(ε) false relative to Q (unchecked sketch). But Theorem B is not proved under CH. Neither convention gives WP(ε) a true/false pair of oracles.
- **The proof of the journal's SAT implication does not carry over under LL, and the implication is not claimed to relativize.** Its Nepomnjaščii step fails for a low-space, polynomial-time oracle evaluator whose queries are longer than linear, because a linear-time Σ_k machine cannot write them. No oracle is shown where WP(ε) and fast SAT both hold. Moreover P^O ≠ NP^O for a random O (Bennett–Gill), so fast SAT^O is false there anyway. Theorem B is therefore evidence about the premise only and yields no relativized SAT bound. Since the random-oracle hypothesis is false in general, Theorem B is not evidence that WP(ε) holds without an oracle.

**Exact obstruction.** The missing step is WP(ε) without an oracle, for one rational ε. The counting proof of Theorem B uses exactly one property of O: an avoider running in time t sees at most t of the 2^s range strings at its own index, and the rest are uniform and independent of its view. Without an oracle there is no such randomness. The analogue of Theorem B would need an explicit low-space family whose range, at some index of infinitely many lengths, cannot be avoided by any polynomial-time algorithm. That is a hardness statement against P that implies P ≠ PSPACE (journal), so counting cannot supply it.

## 6. The three standard tests

- **(a) Does the hard family have a fast globally correct solver?** No unrelativized lower bound is claimed here. Theorems A and B are statements in the random-oracle world. There, Theorem B says that no avoider running in time up to 2^{s-1} escapes U at all large lengths. Nothing transfers to explicit families; the journal's Vandermonde family already has a packed-XOR avoider. [Unread words](unread-words-in-a-range-avoidance-index.md)
- **(b) Does the same argument give the same bound for 2-SAT?** No. The conditional headline uses that fast SAT gives P = NP and removes alternations. A linear-time 2-SAT algorithm gives neither, so the argument yields no 2-SAT bound. Theorems A and B do not mention SAT.
- **(c) Does it survive the oracle of the relativized-clock note?** In that note's p = 1 world, linear SAT^A holds. If the journal's implication relativized to that oracle, WP(ε) would have to fail relative to it. No one claims WP(ε) relative to that oracle, so there is no contradiction. The conditional headline survives because it stays conditional. The implication's proof does not carry over under LL, and the implication is not claimed to relativize (Section 5). [Relativized clock](relativized-clock.md)

## 7. What is not proved

- WP(ε) without an oracle, which is the step the SAT chain needs.
- Theorem B under convention CH.
- The genuine pebbling version of Theorem A, with labels shorter than the space, in a model with two uncharged oracle tapes. It is cited, not proved.
- Any oracle relative to which WP(ε) is false under LL. None is known here: WP(ε) holds relative to both a random oracle and TQBF.
- The CH claim that WP(ε) is false relative to TQBF (an unchecked sketch).
- The circuit-hardness conjunct of Theorem 1.3 relative to TQBF under LL (an unchecked sketch in Section 5).
- That the journal's SAT implication relativizes. It is not claimed. Its proof does not carry over under LL, because the Nepomnjaščii step cannot write the long queries. No oracle is shown where WP(ε) and fast SAT both hold.
- The transfer of Theorem B to the O(n)-space endpoint, which is only read off in Section 4. An analogue of Theorem A at that endpoint was not attempted; the linear-endpoint premise is already one-index.
- Bennett–Gill and Ladner–Lynch were not re-read.

## 8. Next lemma

Two candidates, neither attempted:
1. **Theorem B under CH.** An evaluator that cannot write long oracle-derived strings is closer to an explicit low-space family. The family would have to be tailored to A, because the constant printer escapes the CH analogue U′ of Section 3.
2. **An explicit one-index hitting statement for a restricted class of avoiders.** For example, avoiders that read fewer than L − k + 1 input words, building on the unread-words note. Any statement covering all polynomial-time avoiders implies P ≠ PSPACE (journal), so counting alone will not give it. [Unread words](unread-words-in-a-range-avoidance-index.md)

## 9. Finite sanity checks

Run `OPENBLAS_NUM_THREADS=1 python3 random_oracle_range_hitting_sanity.py`. It takes a few seconds and prints the lines below. Everything here is checked at finite size only; none of it is a proof. [Sanity script](../audits/random_oracle_range_hitting_sanity.py)

```
Part B: n=10 (K=1024 indices), s=4 (16 seeds), m=12 (4096 outputs), 2^(n+s-m)=4, trials=10000
  S1 constant 0^m (t=0,k=0)                                                Pr[no hit]~0.0198 (+-0.0014)  seed-bound 0.0183  point-bound 0.0183  OK
  S2 learn own seed 0, avoid it (t=m,k=1)                                  Pr[no hit]~0.0240 (+-0.0015)  seed-bound 0.0235  point-bound 0.3679  OK
  S3 learn own seed 0 + partner seed 0, avoid both (t=2m,k=2)              Pr[no hit]~0.0237 (+-0.0015)  seed-bound 0.0302  point-bound 1.0000  OK
  S4 output partner's seed-0 string (t=m,k=1)                              Pr[no hit]~0.0174 (+-0.0013)  seed-bound 0.0235  point-bound 0.3679  OK
  S5 learn own seeds 0..3, avoid them (t=4m,k=4)                           Pr[no hit]~0.0523 (+-0.0022)  seed-bound 0.0498  point-bound 1.0000  OK
  S6 learn partner seeds 0..3, output smallest value avoiding them (t=4m,k=4) Pr[no hit]~0.0184 (+-0.0013)  seed-bound 0.0498  point-bound 1.0000  OK
  exact S1 = (1-2^-m)^(2^s*2^n)     = 0.0183
  exact S2 = (1-2^-m)^((2^s-1)*2^n) = 0.0235
  exact S5 = (1-2^-m)^((2^s-4)*2^n) = 0.0498

Part A: n=12 (4096 indices), m=16, seed s=3, stored label bits S=3, trials=20
  one-level printer, copy-x evaluator: mean hit fraction 1.0000
  two-level printer, lam= 4: mean hit fraction 1.0000   heuristic 2^(S+s-lam)+2^(s-m) = 1.0000   Theorem-A-style bound m*2^(s+S-lam)+2^(s-m) = 1.0000
  two-level printer, lam= 6: mean hit fraction 1.0000   heuristic 2^(S+s-lam)+2^(s-m) = 1.0000   Theorem-A-style bound m*2^(s+S-lam)+2^(s-m) = 1.0000
  two-level printer, lam= 8: mean hit fraction 0.2517   heuristic 2^(S+s-lam)+2^(s-m) = 0.2501   Theorem-A-style bound m*2^(s+S-lam)+2^(s-m) = 1.0000
  two-level printer, lam=10: mean hit fraction 0.0626   heuristic 2^(S+s-lam)+2^(s-m) = 0.0626   Theorem-A-style bound m*2^(s+S-lam)+2^(s-m) = 1.0000
  two-level printer, lam=12: mean hit fraction 0.0159   heuristic 2^(S+s-lam)+2^(s-m) = 0.0157   Theorem-A-style bound m*2^(s+S-lam)+2^(s-m) = 0.2501
  two-level printer, lam=14: mean hit fraction 0.0042   heuristic 2^(S+s-lam)+2^(s-m) = 0.0040   Theorem-A-style bound m*2^(s+S-lam)+2^(s-m) = 0.0626
```

**Part B: the universal family U against six avoiders.** Parameters: n = 10 (1024 indices), s = 4, m = 12, so 2^{n+s-m} = 4, with 10000 trials per avoider. The avoiders spend their queries on their own block and/or on a partner index's block.

- **The two bounds.** The "point-bound" is Theorem B's exp(−2^{n+s-m}(1 − t/2^s)), with t point queries per run. The "seed-bound" is exp(−2^{n+s-m}(1 − k/2^s)), with k distinct (block, seed) pairs touched per run. The proof of Theorem B gives the seed-bound unchanged if τ_j counts touched seeds of block x_j instead of points, because Σ_j τ_j ≤ K·k.
- **The seed-bound is nearly attained.** For S1, S2 and S5 the exact closed form (1 − 2^{-m})^{(2^s − k)2^n} lies just below the seed-bound and agrees with it to four decimals. The ratios are 0.99951, 0.99954 and 0.99963 for k = 0, 1, 4. The bound uses 1 − y ≤ e^{−y}.
- **No estimate exceeds the seed-bound by more than 3 standard errors.** The S1 and S5 estimates lie about 1.1 standard errors above the exact values, which is sampling noise.
- **Spending queries on other blocks did not help the avoider.** Avoiders that spend queries on other indices' blocks (S3, S4, S6) do no better than the bound.

**Part A: one-level versus two-level printer against a small-memory evaluator.** Parameters: n = 12, m = 16, seed s = 3, and S = 3 stored label bits. The evaluator stores the top S bits of ℓ(x) and takes the next s bits of its guess from the seed. This is one specific strategy, not the worst case.

- **One-level printer.** Under LL it is reproduced exactly, on every index. (The script line restates this by construction; it does not test it.)
- **Two-level printer.** It is reproduced on every index while the label length λ ≤ S + s. Beyond that, the hit fraction falls like 2^{S+s-λ}.
- **Bound check.** The Theorem-A-style bound m·2^{s+S-λ} + 2^{s-m} is above every observed value.
