# A T-step SAT algorithm gives unique-witness verifiers of size O(T log² N) for both verdicts, and the quadratic network ceiling does not cap that size

The journal's deterministic RAM-trace simulation is unambiguous, and it is also total: on every input it accepts exactly one witness, whose output is the verdict. So a deterministic RAM program that decides SAT within worst-case time T(N) on every N-bit input, with N ≤ T(N) ≤ poly(N), gives unique-witness verifiers for SAT and for UNSAT of size O(T log² N). The journal's quadratic exact-network construction loses uniqueness. Over F₂, its witness count on well-formed inputs is the parity-OR count 1 + ∏(1 + c_j) described by Dell, Kabanets, van Melkebeek and Watanabe. So its O(N²) ceiling caps finite-field volume and parity size, but not the unique-witness size U(SAT). U(SAT) has no known polynomial cap; a polynomial cap is equivalent to NP ⊆ UP/poly in circuit form. U(UNSAT), the nondeterministic size of UNSAT and the total size TU(SAT) have no polynomial cap unless coNP ⊆ NP/poly. The absence of a known cap is not evidence for a lower bound. A unique-witness verifier is an exact network over every field, of volume O(size + N), so the journal's existing network lower bounds already apply to it. A standard cut-rank lemma for unambiguous verifiers detects uniqueness. But its per-cut bounds cap at N/2 and do not add up over nested prefix cuts, and on SAT's clause-split face uniqueness adds nothing. The named next step is whether ℚ has no ports, since the upstream routing lemma already holds in every field without ports. With two further unchecked dependencies, that would give a characteristic-zero network bound, but for a family that RAMs solve quickly. The question was raised by an external review. Nothing changes for the linear milestone, and nothing here is a lower bound; the linear, quadratic and cubic questions remain open. [Simulation threshold](simulating-a-ram-step-by-exact-networks.md) · [Quadratic network ceiling](exact-network-ceiling-for-ordinary-sat.md) · [Multiplicity and size of RAM verifiers](multiplicity-and-size-of-fixed-ram-verifiers.md) · [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)

## Measures

SAT_N is the verdict on N-bit DIMACS files; malformed files count as unsatisfiable, and UNSAT_N is its negation. For f : {0,1}^N → {0,1}:
- **U(f)** is the least number of fan-in-2 gates, in any 2-input basis with free fanout, of a circuit V(x, y) with #{y : V(x, y) = 1} = f(x) for every x. Write U(SAT) and U(UNSAT) for U(SAT_N) and U(UNSAT_N).
- **TU(f)** is the least size of a circuit V(x, y) with **exactly one** accepted y on **every** x, together with an output gate equal to f(x) on that y. Then TU(f) ≤ O(U(f) + U(¬f)) + O(1), and U(f), U(¬f) ≤ TU(f) + O(1).
  - For the first, guess a bit b and run the verifier for f or for ¬f, pinning the other verifier's witness to zero.
  - For the second, add a test that the output is 1, or 0.
- **nondet(f)** is ordinary nondeterministic circuit size, **⊕(f)** is parity circuit size (acceptance is the witness count mod 2), **D(f)** is deterministic circuit size, and **vol_k(f)** is exact binary-wire network volume over the field k, in the journal's convention.

An unambiguous circuit is a 0/1-table network whose contraction equals f over **every** field, ℚ included (Section 4). So vol_k(f) ≤ C·(U(f) + N) for an absolute constant C. Hence D(f) + O(1) ≥ TU(f) ≥ U(f) − O(1), and U(f) ≥ max{nondet(f), vol_k(f)/C − N for every field k}.

## 1. The RAM-trace simulation is unambiguous and total

The simulation note's threshold statement already gives, for a fixed program deciding SAT in T(N) steps with N ≤ T(N) ≤ poly(N) and w = Θ(log N), an unambiguous circuit of volume O(T(N)·log²N). This section checks it in exactly U's sense and adds the total form.
- **Witness.** The witness is the whole trace: control state and registers per step, plus one memory record per access and per input word. Every field that could be free is pinned: idle steps after halting, quotient and remainder fields on non-division steps, dummy records and unused fields. Each free field would otherwise double the count. The pinning that makes the F₂ contraction exact is exactly what makes the count 0 or 1.
- **Memory consistency.** It is checked after a **deterministic** sort (AKS), whose swap decisions are computed from the trace, not guessed. The packed-band variant with guessed Beneš switches is **not** unambiguous; the simulation note says so ("Those switch settings are not unique"). So the bound uses the AKS version, or the hidden-order version with its gather also built without cancellation, for example by deterministic sorting.
- **Acceptance.** Accepting iff the trace is valid and the final state accepts gives 0 witnesses on a rejecting run and exactly 1 on an accepting run. Accepting every valid trace and outputting the verdict gives exactly one accepted witness on **every** input. So the simulation bounds TU(SAT), and with it U(SAT) and U(UNSAT), by O(T(N)·log²N). This needs T(N) to bound the running time on every N-bit input, malformed files included.

The journal's audit of the simulation counts every valid witness of a toy RAM with indirect loads and stores, with no acceptance test, so it checks totality at toy sizes. A rerun gives, for instance,
```
  A=3 V=3 K=2 (T=5 events): inputs=27 witness_checks=2278125 inputs_without_exactly_one_correct_witness=0
```
and the other three lines of that check also report 0. The uniform analogue, in which a deterministic solver gives both verdicts a verifier with exactly one passing certificate for the true verdict and none for the other, is in [verifying a RAM run with one-way guesses](verifying-a-ram-run-with-fresh-marks-and-sorted-positive-reads.md). [Uniqueness audit](../audits/ram_trace_unique_witness_check.py)

## 2. Where the quadratic construction loses uniqueness

The preprocessing of the [quadratic construction](exact-network-ceiling-for-ordinary-sat.md) is deterministic: parsing, ranking and the sorting networks compute every swap decision from the input. It keeps uniqueness. Three later steps lose it.
1. **The per-trial sum over all models** (section "One prime-field scalar in linear volume"). A trial guesses one bit per retained occurrence. The consistent patterns are in bijection with the satisfying assignments, so the trial's witness set is the whole model set. Each model a gets a weight w(a) ∈ F_p, and the trial value is z = Σ_{a⊨φ} w(a), which can cancel to zero on a satisfiable input. The variant that isolates a unique minimum model uses the minimum only to show that a polynomial is nonzero, "without requiring that the final accepting configurations themselves be unique". A unique witness would need a certificate that no lighter model exists, and that certificate is co-nondeterministic.
2. **The Fermat power** z^{p−1}, realised by p − 1 copies of a trial (section "Simultaneous fixing and exact output"). It is a sum over tuples of models, and it is vacuous over F₂.
3. **The summed tag** that realises each difference 1 − Z in the exact OR 1 − ∏_j(1 − z_j^{p−1}), the final difference included. The constant branch gives +1 and the other branch −Z.

In characteristic 2 the network is a 0/1 network, that is, a nondeterministic circuit. On a well-formed input its accepting count is

  count(x) = 1 + ∏_{j=1}^{r} (1 + c_j(x)),  where c_j(x) = #{models a : w_j(a) = 1}.

So every well-formed unsatisfiable input has count 2, and read as an existential verifier the network accepts every well-formed input; malformed inputs are zeroed by the input-validity bit. This is exactly the parity-OR operation that Dell et al. describe in §1.3: add one satisfying assignment to each circuit, take the product, and add one more. They credit the underlying observation to, among others, Naik, Regan and Sivakumar, whose paper was not accessed here. An OR of uniquely satisfiable circuits has one witness per satisfied disjunct instead, and no unambiguous replacement for this step is known.

**Checks** (Parts 1 and 1b of [the checks](../audits/unique_witness_verifier_checks.py)).
- Part 1 evaluates the count formula on every model set of v ≤ 3 variables, with the construction's own fingerprints. Over F₂ the empty model set, the unsatisfiable case, has count 2, and nonempty ones have counts from 5 to 157,501 at v = 3, never 1. Read over ℤ with the −1 tag weights, the same network takes 18 different values on satisfiable inputs at v = 3, so it is not a ℚ-network for SAT. The F₃ version decides correctly modulo 3 and is not 0/1 over ℤ.
- Part 1b builds the tagged F₂ network explicitly for v ≤ 2 and counts its accepting configurations by brute force. It matches the formula on every input, with count 2 on unsatisfiable inputs and counts from 5 to 145 on satisfiable ones at v = 2.
- Both parts are idealised: a trial guesses the model directly. The journal's network guesses one bit per occurrence and relies on the bijection between consistent patterns and models stated in the ceiling note, which was not re-simulated here.

## 3. Known caps, measure by measure

- **Finite-field volume.** vol_{F_p}(SAT_N) = O(N²) for every prime p (the ceiling note).
- **Parity size.** ⊕(SAT_N) = O(N²). This is inferred here: over F₂ with binary wires every table is 0/1, so guessing all internal wires and checking each table gives a parity verifier of size linear in the volume. As noted during review, this does not conflict with the simulation note's remark that no converse conversion with linear overhead is known, which concerns networks in general rather than binary-wire networks over F₂.
- **Nondeterministic size.** nondet(SAT_N) is N·polylog N, by guessing one bit per occurrence and checking consistency by sorting (a standard remark made during review).
- **Unique-witness size.** U(SAT) has no known polynomial cap. U(SAT) ≤ poly(N) is equivalent to NP ⊆ UP/poly in its circuit form (compose a P/poly reduction with the verifier; uniqueness survives), that is, to a P/poly-computable deterministic general disambiguation. Dell et al. (§2.2) state the uniform version: "the UP = NP question is equivalent to the existence of a polynomial-time transformation" of a deterministic circuit into one that has a unique satisfying assignment exactly when the first is satisfiable. No such bound is known, and refuting it would give NP ⊄ P/poly, since P/poly ⊆ UP/poly. Dell et al. leave open whether NP = UP has unexpected consequences: "It remains an open question whether the assumption NP = UP yields any unexpected consequences". No source addressing NP ⊆ UP/poly was found, and the term does not occur in their paper. The upper bounds actually known are U(SAT) ≤ 2^{O(N/log N)} and U(SAT) ≤ O(T log² N) for any SAT RAM running in time T.
- **The UNSAT side.** nondet(UNSAT) ≤ U(UNSAT) ≤ TU(SAT) + O(1), and a polynomial nondet(UNSAT) would mean coNP ⊆ NP/poly. So U(UNSAT), nondet(UNSAT) and TU(SAT) have no polynomial cap unless coNP ⊆ NP/poly.

The absence of a known cap is not evidence for a lower bound. What Dell et al. prove concerns more restricted transformations. Isolation computable in P/poly, with the same variables and only satisfying assignments removed, is equivalent to NP ⊆ P/poly (Theorem 3.3), both for deterministic minimal-witness isolation and for randomized isolation with success probability above 2/3 + 1/poly(ℓ). Randomized witness-recoverable disambiguation of deterministic circuits in P/poly with that success probability implies coNP ⊆ NP/poly (Theorem 3.7). General disambiguation, with auxiliary variables and no relation between the witnesses, is exactly U's model, and they prove no collapse for it. In logspace the analogous step works because inductive counting certifies non-reachability (Reinhardt–Allender, NL/poly = UL/poly, cited from memory). For NP the natural certificate, that no lighter model exists, is co-nondeterministic, and no analogue is known.

**What bounds would imply.**
- U(SAT) ≥ ω(N^k log² N) would exclude an O(N^k)-time RAM program for SAT, by Section 1. For k = 1 an exact-network bound over a finite field would also suffice. For k ≥ 2 finite-field networks cannot help, since vol_{F_p}(SAT) = O(N²), while U is not ruled out because it has no known cap.
- A superpolynomial bound on U(SAT) would give NP ⊄ UP/poly and so NP ⊄ P/poly, which is out of reach. The realistic targets are N^{1+ε} and N^{2+ε}. An N^{2+ε} bound would separate unambiguous from parity circuits explicitly for an NP function.
- By totality, a bound on U(UNSAT), or on nondet(UNSAT), also suffices. A bound on nondet(UNSAT) implies the same bound on U(UNSAT) and TU(SAT), so it is the strongest of these targets and the hardest to prove; it differs only in that its argument need not use uniqueness. Superlinear nondeterministic circuit lower bounds are not known (see [black-box routes through the diagonal compile](black-box-routes-through-the-diagonal-compile.md)).

## 4. Unique-witness verifiers are exact networks over every field

Take V(x, y) with s fan-in-2 gates. Turn each gate into a 0/1 table of arity 3, [g = op(a, b)], give each wire a copy tree of degree-3 equality tensors whose size is linear in its fanout, and add a unary table [out = 1]. The contraction at x is #{y : V(x, y) = 1} ∈ {0, 1}, so it equals f(x) over **every** field, finite or ℚ, and the volume is at most C·(s + N). An unambiguous verifier of a function that is not identically zero has no unused witness bits, since each would double the count on positive inputs. The simulation note already states this conversion, with linear overhead over every field, and Proposition C(ii) of the black-box routes note makes the same argument for clauses instead of gates.

So the journal's network lower bounds apply to U directly. The [multiplicity note](multiplicity-and-size-of-fixed-ram-verifiers.md), in its section "An unambiguous verifier lower bound for ordinary 3-SAT", already states that every unambiguous circuit for ordinary 3-SAT at encoded length N needs Ω(N(log N)^σ) gates, through the list theorem with σ > 0 unspecified. Since 3-SAT files of length N are a projection of SAT_N, U(SAT) ≥ c·N(log N)^σ. The cut lemma below adds nothing to this number.

Whether U can exceed network volume has two layers, since U(SAT) ≥ sup_k vol_k(SAT_N)/C − N.
- **Finite fields.** Exceeding max_p vol_{F_p}(SAT_N) = O(N²) is exactly what the quadratic and cubic targets need, so a lower-bound argument for them must fail for F_p-networks for every prime p.
- **Characteristic zero.** No polynomial upper bound on vol_ℚ(SAT_N) is known, so U(SAT) might exceed every finite-field volume and still equal vol_ℚ up to constants. A characteristic-zero network bound would then suffice.
- **The linear milestone** needs neither layer, since ω(N log² N) lies below the N² cap. There U adds nothing to the existing circuit route, except that U ≥ vol makes the target formally weaker.

## 5. A cut-rank lemma for unambiguous verifiers (standard)

**Lemma (positive cut factorisation).** Let V be a Boolean constraint network with input variables x ∈ {0,1}^N and any number of auxiliary variables z, each constraint a 0/1 table on its scope; this covers circuits with any 2-input gates and any fanout, a gate being a constraint g = op(u, w). Suppose count(x) = #{z : all constraints hold} satisfies count(x) ≤ K and f(x) = [count(x) ≥ 1] for every x. Take a partition (A, B) of the input coordinates and place each auxiliary variable and each constraint on side A or side B; let c be the number of variables that occur in a constraint placed on the other side. Then:
1. count(x) = Σ_{σ∈{0,1}^c} α_σ(x_A)·β_σ(x_B) with nonnegative integers α, β.
2. If K = 1, then f^{−1}(1) is the **disjoint** union of the at most 2^c rectangles {α_σ ≥ 1} × {β_σ ≥ 1}, and α_σ, β_σ ∈ {0, 1} on them. So the rank of the communication matrix of f across (A, B) is at most 2^c over **every** field, and so is its nonnegative rank.
3. For general K, its rank over ℚ is at most C(2^c + K, K).
4. A parity verifier or an F_p-network gives only rank_{F₂} ≤ 2^c, respectively rank_{F_p} ≤ 2^c, and a nondeterministic verifier gives only the Boolean cover bound.

*Proof.* With the crossing values σ fixed, each remaining variable occurs only in constraints on its own side, so the sum over z factorises. A sum of nonnegative integers equal to f(x) ≤ 1 has at most one nonzero term, which is 1·1. For general K, apply q(z) = 1 − ∏_{j=1}^{K}(1 − z/j) entrywise to the count matrix, whose rank is at most W = 2^c; the d-th Hadamard power has rank at most C(W + d − 1, d), and summing over d ≤ K gives C(W + K, K). ∎

This is the standard circuit-to-protocol argument, and the journal has it for ordered branching programs and streaming verifiers ([read-once sizes](read-once-size-of-sat-and-unsat.md)). It is recorded here in exactly U's model and is not new. The checks run as follows.
- **Compact deterministic computations (Part 2).** 200 random circuits on 8 inputs with 10 arbitrary 2-input gates were turned into "guess every gate value and check locally" verifiers, the template of the RAM-trace verifier. Each got a random input bipartition, with every auxiliary variable and constraint placed by local search to make c small. The count identity and the disjointness of the rectangles hold on all 200, the rank bound is never violated, and 20 verifiers were checked unambiguous by brute force. As a test of the rank bound this is weak. The matrices are 16×16, so the 174 cases with c ≥ 4 satisfy it automatically (the script prints the histogram of c), and the other 26 cases, with c ∈ {2, 3}, have rank over ℚ at most 2, as found during review.
- **Sensitivity to uniqueness (Part 3).** Take one F₂ trial of the quadratic construction at the clause-split cut, with the guessed model on one side, so c = v. With all-ones weights at v = 3 the count identity holds and the F₂ bound is tight at 8 = 2^c, but the rank over ℚ is at least 255, because the rectangles overlap, up to 8 per input. So no unambiguous verifier computes that trial's parity function with crossing 3 at this cut; it needs crossing 8 or more. With the construction's own fingerprint the F₂ rank is 4 and the ℚ rank at least 15, which forces crossing 4. This holds only at this cut and for the trial's parity function, not for SAT.
- **SAT at the clause-split cut (Part 4).** There the matrix is [S_A ∩ S_B ≠ ∅] on model sets, with rank 15 at v = 2 and 255 at v = 3 over both F₂ and ℚ. In general it is 2^{2^v} − 1 over every field, because DISJ = ⊗[[1,1],[1,0]] has determinant ±1 and the row of ∅ is zero. During review its 1-partition number was also shown, on paper, to be 2^n − 1 for n = 2^v. So on this face the lemma for unambiguous verifiers says nothing beyond the F₂ bound, to which every F₂-network for SAT, the quadratic one included, is already subject.
- **No additivity over nested cuts (Part 5).** For inner product mod 2 on n = 8 pairs with the prefix cuts, the ranks over ℚ are 2, 4, …, 128 and 255, and their logarithms sum to 35.99, against 15 gates for a deterministic circuit:
  ```
     {'n': 8, 'rank_Q_lower_by_cut': [(1, 2), (2, 4), (3, 8), (4, 16), (5, 32), (6, 64), (7, 128), (8, 255)], 'sum_log2_rank': 35.99, 'deterministic_gates': 15}
  ```
  Deterministic circuits are unambiguous, so no inequality of the form size ≥ Σ_t log₂ rank_ℚ(M^{(t)})/polylog over the nested prefix cuts holds for unambiguous verifiers.

The ranks over ℚ of the 256×256 matrices are lower bounds computed modulo 2³¹ − 1, made exact where needed by the upper bound from a zero row.

## 6. What a bound on U must get past, and the next step

- **Per-cut cap.** Placing everything on side B gives c ≤ |A|, so the lemma never forces more than min(|A|, |B|) ≤ N/2 gates.
- **No additive aggregation over nested cuts.** Part 5 refutes summing the lemma over the N nested prefix cuts with polylogarithmic loss, even for deterministic linear-size circuits. Other cut families were not tested. During review it was noted, on paper, that inner product under a random pairing of the variables should extend this to any fixed family of 2^{o(N)} balanced cuts.
- **SAT-blindness at the clause-split face.** There the rank over ℚ equals the rank over F₂, so the extra power of uniqueness shows only on intermediate parity-type functions, which an unambiguous verifier for SAT need not compute. Only this face was examined, with each side ranging over all subsets of the full-width clauses on v variables; the rank equality there is proved for all v. Cuts that split names, signs or clauses of the DIMACS bits were not examined. A cut of SAT_N whose ℚ rank far exceeds its F₂ rank may exist, but it too would be capped by N/2.
- **Arguments valid for finite-field networks.** Any argument that also bounds F_p-networks is capped on SAT at O(N²) by the ceiling note, as the barrier note already says for volume-based bounds. So excluding quadratic time needs an aggregation that is false for F_p-networks for every prime p, that is, one that uses nonnegativity or characteristic zero *inside* the aggregation.

**Next step (not a new lemma).** The upstream routing lemma, the uniform-destinations lemma `lem:uniform-demand` of the matrix-multiplication preprint's `list.tex`, holds in every field without ports, and the journal already uses it in that form ([technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md), and §2.4 of the simulation note). During review its statement at the pinned commit was found to carry no finiteness hypothesis and its proof no finite-field counting, with lines 161–205 of the file unread; the reduction from D_w to the tagged problem is stated for every characteristic. So a characteristic-zero bound vol_ℚ(D_w) = Ω(n_w√w) would need three things, none checked here:
1. that ℚ has no ports. By the tape preprint's `thm:noports`, the alternative gives a deterministic 2^{O(v^{1−δ})} algorithm for 3-SAT, so this is a dichotomy;
2. that the external price and entropy results the lemma uses hold over ℚ;
3. the list theorem `thm:many` itself, which the journal records as stated only for finite fields.

D_w has O(N/log N)-time RAM solvers, so such a bound would be no step toward a RAM bound. It would be a characteristic-zero network bound, of the kind described in Section 4. This list of three dependencies is offered, unconfirmed, as a refinement of the simulation note's remark that a characteristic-zero route "would need Lemma `uniform-demand` over ℚ". A RAM bound needs a SAT family **without** a fast RAM solver and an aggregation of the last kind above, and no such lemma is known.

**Alternative target.** By totality one may target nondet(UNSAT), with a co-nondeterministic aggregation in place of a uniqueness-sensitive one. As Section 3 says, that target is harder, not easier, and the first two obstructions apply to it too: the cover number 2^n of disjointness gives crossing n only.

## 7. What is new and what is not

- **New, though elementary.** The total form of the circuit simulation: it bounds TU(SAT), so bounds on U(UNSAT) or nondet(UNSAT) also suffice. The status of the cap for each measure. The identification of the quadratic network's F₂ count with the parity-OR count. The SAT-blindness of the clause-split face.
- **Not new.** The unambiguous form of the simulation, which is the simulation note's threshold statement. The conversion to exact networks over every field, which the simulation note states, and U(SAT) ≥ c·N(log N)^σ, which is in the multiplicity note. That the uniform-destinations lemma holds in every field without ports, which the journal already uses. The cut lemma, which is standard and in the journal for read-once and streaming verifiers. The per-cut cap. The cap on arguments valid for finite-field networks, which is in the barrier note.

## 8. The three standard tests

The only lower bound claimed is the lemma's per-cut bound c ≥ log₂ rank.
- **(a) Fast solver on the hard family.** Yes. The clause-split faces have v variables and are solved by brute force over 2^v assignments. The lemma forces crossing about 2^v there, which is linear in the face's input length, and it claims no time bound.
- **(b) 2-SAT.** For v = 2 binary clauses already realise every model set, since each excludes one point, so 2-SAT's clause-split matrix is the same rank-15 matrix and the lemma gives the same bound. This is consistent: the bound is at most linear, and 2-SAT has U ≤ O(N log² N) through its linear-time RAM algorithm. Any superlinear version must fail here.
- **(c) The oracle of [the relativized clock](relativized-clock.md).** The lemma is a statement about networks. The step from RAM time to U uses the fact that one instruction reads O(w) bits; an instruction that reads Θ(n log n) bits breaks the O(T log² N) simulation, so the route does not relativize, as it must not. The lemma alone implies nothing about RAM time.

## 9. What is not proved

- Any lower bound on U(SAT) beyond the journal's Ω(N(log N)^σ), which comes from F₂-networks and is not sensitive to uniqueness. Any RAM-time lower bound.
- NP ⊄ UP/poly, or any quantitative form of it. That NP ⊆ UP/poly has no known collapse consequence is sourced only for uniform NP = UP.
- That the hidden-order version of the simulation stays unambiguous at the claimed volume; its gather must be built without cancellation, and this was not checked.
- That the journal's per-occurrence trial network has the same counts as the idealised trials of Parts 1b and 3. This rests on the bijection stated in the ceiling note, which was not re-simulated.
- Any characteristic-zero network lower bound, and the three dependencies listed in Section 6.
- The lemma is proved on paper and checked only at the sizes listed (v ≤ 3; circuits with 8 inputs and 10 gates).
- The theorems of Dell et al. are quoted from their statements; their proofs were not read. Naik–Regan–Sivakumar, Valiant–Vazirani, Mulmuley–Vazirani–Vazirani, Reinhardt–Allender and Yap were not accessed.

**Sources.** Dell, Kabanets, van Melkebeek and Watanabe, *Is Valiant–Vazirani's isolation probability improvable?*, ECCC TR11-151, revision 1, https://eccc.weizmann.ac.il/report/2011/151/revision/1/download/. Read in part: the abstract, §1, §2.1–2.2, the statements of Theorems 3.3 and 3.7, and §5. The quotations and theorem items were checked against the text during review.

## Reproducing the checks

Run from the audits directory:
```
python3 -B unique_witness_verifier_checks.py
python3 -B ram_trace_unique_witness_check.py
```
The first runs Parts 1, 1b and 2–5 in about 20 seconds and needs numpy. The second is the journal's existing audit of the simulation and takes about a second. [Unique-witness checks](../audits/unique_witness_verifier_checks.py) · [Uniqueness audit](../audits/ram_trace_unique_witness_check.py)
