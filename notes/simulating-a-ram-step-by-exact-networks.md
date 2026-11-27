# Simulating a RAM step by exact networks costs between (log T)^{1+σ_k} and (log T)^2, so an exact-network SAT bound above N log² N would exclude linear time

This note fixes the simulation threshold of the circuit route (route A of the barrier note). It concerns circuit and tensor-network simulations of the word RAM, not RAM time, and proves no lower bound for SAT. Two exponents are involved. The per-step exponent c*, over all programs, satisfies 1+σ_k ≤ c* ≤ 2 for exact tensor networks over a finite field k, where σ_k > 0 is the unspecified exponent of the list theorem. The run exponent c_lin, for an N-step run on N bits, is what the circuit route needs, and it is known only to lie in [σ_k, 2]. With the known simulation, an exact-network (or unambiguous-circuit) bound for SAT that is unbounded relative to N log² N would exclude deterministic linear RAM time; the best SAT bound known is N(log N)^{σ_k}. The companion note shows that the list-distinctness technique behind σ_k cannot certify more than O(n log n), so reaching the threshold needs a new technique. The linear, quadratic and cubic questions remain open. [Barrier note, route A](what-any-proof-of-superlinear-sat-time-must-get-past.md) · [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)

**Per-step exponent c*.**
- For exact tensor networks over a finite field k: 1+σ_k ≤ c* ≤ 2.
- For circuits with exactly one witness: c* ≥ 1+σ_k for every finite field k, and c* ≤ 2. They convert to networks over every field.
- For parity circuits: 1+σ_{F_2} ≤ c* ≤ 2. They convert only to networks over fields of characteristic 2.
- Over infinite fields only c* ≤ 2 is known.
- No converse conversion with linear overhead is known.

**Run exponent c_lin.** The circuit route is governed by c_lin, which is known only to lie in [σ_k, 2].

**Exact form.** For networks over a finite field k, c*_net(k) = 1+γ_k, where γ_k is the network exponent of one batched read-only word gather. This is an immediate corollary of the equivalence stated in the batched-last-writers note, together with the per-step local checks. That equivalence is a manuscript proof, not Lean-checked; Check A covers it only at toy sizes. [Batched last writers](batched-last-writers-and-public-forward-probes.md)

**The first lemma.** Alternative (i), a T·(log T)^{1+o(1)} simulation, is **false**: the list theorem refutes it for finite-field networks and for every model that converts to them. Alternative (ii), an explicit RAM computation needing T·log²T/poly(log* T) gates, is available only conditionally. It needs the Li–Li network coding conjecture and applies to multi-output Boolean circuits. It does not transfer to the single-output network threshold that the circuit route needs.

**Missing steps.** For deterministic Boolean circuits no T·polylog T simulation of general RAMs was found. The missing ingredient there is a deterministic way to produce each data-dependent read; the guessed-trace method avoids it by summing over the trace. Separately, pinning c* for networks needs one of two results:
- a decision-gather network of volume m·w^{2−ε} (a simulation below exponent 2); or
- a gather lower bound of m·w^{2−o(1)} (alternative (ii) for decisions).

## 1. Definitions

Fix a word RAM program P: a finite instruction list over a fixed number of registers, with indirect load/store, the standard word operations including multiplication, division and shifts, word width w = Θ(log n) on n-bit inputs, and run time T = T_P(n) ≥ n/w. Define the simulation exponent for a model M by

c*_M = inf { c : for every such P there are M-devices of size O(T(log T)^c + n) computing P's output at length n }.

Write c_lin for the same infimum over programs with n ≤ T = O(n). Then c_lin ≤ c*_M. The D_w family padded to n steps gives only c_lin ≥ σ_k, or c_lin ≥ 1/2 in a characteristic without ports. The circuit route is governed by c_lin, which is known only to lie in [σ_k, 2].

There are two models.

- **M = net_k**: exact trivalent tensor networks over a field k (summing over internal wires). Nondeterministic Boolean circuits with exactly one accepting witness convert into such networks, over every field, with linear overhead. Parity circuits convert into networks over fields of characteristic 2. No converse conversion with linear overhead is known. The lower bounds below need k finite: the list theorem is stated only for finite fields. The identity of 2.3 is stated for k-networks with k finite.
- **M = det**: ordinary deterministic Boolean circuits.

The first lemma one would want, in two alternatives:

- (i) for **every** P, c*_M ≤ 1 + o(1); or
- (ii) **there exists** an explicit P with T steps such that every M-device for it has size ≥ T log²T / poly(log* T).

## 2. Bounds

### 2.1 Upper bound c*_net ≤ 2 (known; assembled from the journal and the literature)

1. Guess the whole trace: control state and registers per step, plus one memory record (bank, address, time, op, value) per access and per input word.
2. Check each transition locally. Multiplication costs O(w²) gates schoolbook or w^{1+o(1)} with Schönhage–Strassen. A barrel shift costs O(w log w).

   Division uses a guessed quotient and remainder, unique for a nonzero divisor, checked with one product. Exactness over F_2 needs every free field pinned, otherwise the extra witnesses cancel in the contraction:
   - A zero divisor takes the program's fixed exceptional result.
   - The quotient and remainder fields are pinned to zero on every step that is not a division.
   - Idle steps after halting, dummy records and every unused field are pinned to canonical values, as in the delayed-forecast note ("Make idle steps and dummies canonical"). [Delayed forecast](locally-indexed-formulas-for-the-delayed-forecast.md)

   Alternatively, compute the quotient deterministically with O(w²) gates.
3. Sort the T + n/w records by (bank, address, time) with a **deterministic** sorting network and check last-writer consistency along each address run. AKS uses O(T log T) comparators on O(w)-bit records, so O(T·w·log T) gates.

With those fields pinned, a deterministic run has exactly one valid trace and every gate then has one consistent value. Contracting the network over any field therefore gives the decision exactly.

The total volume is O((T + n/w)·w·log(T+n) + T·w^{1+o(1)} + n) = **O(T log² n)** for n/w ≤ T ≤ poly(n).

This section restates the journal. The construction appears in the list-and-matrix-costs note under "What a polynomial binary-product bound would imply", and in the delayed-forecast note (deterministic sorting for a unique witness, canonical pinning). The packed-band transfer uses existentially guessed Beneš switches instead. Those switch settings are not unique, so that version gives a satisfiability reduction, not an exact network. The exponent 2 is an asymptotic bound for AKS only: Batcher costs one more logarithm (Check C below). [List and matrix costs](list-and-matrix-costs-for-ram-and-tapes.md) · [Packed band transfer](packed-band-transfer.md)

### 2.2 Lower bound c*_net(k) ≥ 1+σ_k, and c*_det ≥ 1+σ_k: alternative (i) is false

- The list D_w has N = 2^w records of 2w bits, so n_w = 2wN input bits.
- A RAM decides distinctness in O(N) = O(n_w/w) steps (two radix passes).
- The list theorem (Theorem 2.2 = `thm:many` of the 24 November matrix-multiplication preprint, Lean-checked as recorded in the circuit-bound note) gives vol_k(D_w) > n_w·w^{σ_k} for every finite field k. [Circuit bound for 3-SAT](checking-the-sat-circuit-bound.md) · [Upstream Theorem 2.2](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/obstruction.tex#L40-L79)
- So the cost per step on this family is at least w^{1+σ_k}. This is the aggregate recorded in the results index ("aggregate Ω((log n)^{1+σ}) gates per executed word step") and in the opening paragraphs of the list-and-matrix-costs note. [Results index](../RESULTS.md#result--a-superlinear-boolean-circuit-lower-bound-for-3-sat)
- A simulation of size T(log T)^{1+o(1)} would give D_w a network of volume n_w·w^{o(1)} < n_w·w^{σ_k} for large w, a contradiction.
- Boolean circuits and unambiguous circuits convert to networks over every finite field with linear overhead, so the same holds for them. Parity circuits convert to networks over F_2, which gives 1+σ_{F_2}.
- This section restates the journal. The new content is only the reading as a refutation of alternative (i).

**Steps versus bits.** This family runs T = n/w steps. For the run exponent, padding D_w to n steps shows only c_lin ≥ σ_k: an n-step run on n bits cannot cost less than n(log n)^{σ_k}. The family does not show n(log n)^{1+σ_k}.

### 2.3 Exact reformulation: c*_net(k) = 1 + γ_k (k finite; corollary of the journal)

Let G_w(X, I, Y) = ∏_j [X_{I_j} = Y_j], with m = 2^w table words, m queries and O(w)-bit payloads. Set γ_k = limsup over w of log_w( vol_k(G_w) / (m·w) ).

- **(a) A RAM history reduces to one gather.** The batched-last-writers note shows that verifying a T-step history in exact networks costs one constant-payload gather on T rows plus O(Tw), with a unique hidden order. Adding the per-step local checks at w^{1+o(1)} gives Sim(T) ≤ vol(gather on O(T) rows) + T·w^{1+o(1)}.
- **(b) The gather is a RAM computation.** A RAM checks G_w in O(m) steps, one load and one compare per query. So vol(G_w) ≤ Sim(O(m)).
- **Combining them.** The read-only lookup note gives γ_k ≥ σ_k > 0, so the w^{1+o(1)} arithmetic term is absorbed. Hence c*_net(k) = 1 + γ_k, with γ_k ∈ [σ_k, 1]; the upper end comes from sorting the tagged table and query records. [Read-only batched lookups](circuits-for-read-only-batched-word-lookups.md)

Pinning c* for networks is therefore **the same problem as pinning the network exponent of one batched word gather**. The identity is an immediate corollary of the equivalence stated in the batched-last-writers note ("This equivalence is for exact projected networks") together with the per-step local checks.

### 2.4 Sharpening per characteristic (conditional; a reading of preprints dated 24 November 2026)

`list.tex`, the "Fields without ports" case, proves vol(D_w) = Ω(n_w·√w) in a field without ports: Lemma `lem:uniform-demand` applied to Tag(h,h), then two D_w tests. Hence, for each prime p:

- **If characteristic p has no ports:** c*_net(F_p) ≥ 3/2, and so c*_det ≥ 3/2.
- **If characteristic p admits ports:** the finite-characteristic ports note gives modular counting and one-sided randomized 3-SAT in 2^{O(v^{1−δ_p})}. [Ports and weighted SAT](finite-characteristic-ports-and-weighted-sat.md)

**Under Weak ETH, no ℚ detour is needed.** Assume the one-sided randomized form of variable-count Weak ETH. Then the last paragraph of the ports note rules out ports in every positive characteristic. The finite-field case above already gives c*_net(F_p) ≥ 3/2 for every prime p, and c*_det ≥ 3/2. The run exponent then satisfies only c_lin ≥ 1/2.

A characteristic-zero route also exists but is not needed and **is not checked**. Theorem `thm:noports` of the tape preprint (`graphs.tex`) says that ports in characteristic zero imply a deterministic 2^{O(v^{1−δ})} algorithm for 3-SAT. Using it for c* would need Lemma `uniform-demand` over ℚ. `thm:many` and its Lean statement are stated only for finite fields.

The external results these proofs cite ([oaG], [oaP]) were not read. As written, the lemma yields at most √(log q) per bit, so that route cannot give σ > 1/2.

### 2.5 Alternative (ii) holds only conditionally, multi-output, Boolean circuits

Asharov, Lin and Shi (https://arxiv.org/abs/2010.09884) state: if the Li–Li network coding conjecture holds, their sorting upper bound (k+w)·O(nk)·poly(log*) is optimal for every k = O(log n). With k, w = Θ(log n), sorting n records then needs n·log²n / poly(log* n) gates. A RAM radix-sorts in O(n) steps. So under Li–Li, Boolean-circuit simulations of RAM **transducers** cost ≥ log²T / poly(log*T) per step: alternative (ii), conditionally.

Limits of this result:
- It concerns multi-output functions.
- Network coding constrains information flow to many outputs; a single decision bit has none, so it gives nothing for the decision threshold that the circuit route needs.
- Fan-out limits are immaterial up to a constant factor: copy trees convert a fan-in-2 circuit to fan-out 2 with O(s) overhead.
- The remaining caveats are the conjecture itself, the multi-output setting, and any further model restriction in the conditional lower bound. Only the abstract was read, so the last is not verified.

Farhadi, Hajiaghayi, Larsen and Shi (https://arxiv.org/abs/1811.01313, abstract only) add that Li–Li implies Ω(n log n) word steps for **oblivious** word-RAM sorting of Θ(log n)-bit keys. So fixed-access-pattern (oblivious) simulation of a RAM pays Ω(log T) extra word steps per step, conditionally.

### 2.6 Deterministic Boolean circuits: no polylog simulation found

Every construction retrieved guesses a trace and checks it:
- 2.1 above;
- the packed-band transfer;
- Ben-Sasson–Chiesa–Genkin–Tromer, ECCC TR12-125, whose circuit "captures acceptance";
- Robson 1991, not accessed.

arXiv:2502.17779 turned out, on fetching its abstract, to be Williams's "Simulating Time With Square-Root Space", a space simulation, so it is not cited for circuits. Heath et al. (https://arxiv.org/abs/2309.05133, search snippet only) get O(W log⁴ n) only with **cyclic** circuits, which are networks with one consistent fixed point.

The provable deterministic fallback is to keep the list of (address, value) pairs written so far and do an associative lookup at each step, for O(T·(T + n/w)·w) gates. So c*_det is bracketed only between 1+σ_k and a polynomial. The journal already notes that "computing the hidden order by an ordinary deterministic circuit incurs an additional cost".

## 3. Finite check

`python3 ram_trace_unique_witness_check.py` takes about a second. Output (abridged; the smaller instances of each check are omitted): [ram_trace_unique_witness_check.py](../audits/ram_trace_unique_witness_check.py)

```
Check A: memory histories, all hidden index sequences I in [T]^T
  T=4 A=2 V=2: histories=4096 legal=1296 witness_checks=1048576 mismatches=0
  T=3 A=3 V=2: histories=1728 legal=729 witness_checks=46656 mismatches=0
Check B: toy RAM with indirect load/store, full witness enumeration
  A=3 V=3 K=2 (T=5 events): inputs=27 witness_checks=2278125 inputs_without_exactly_one_correct_witness=0
  A=4 V=4 K=1 (T=3 events): inputs=256 witness_checks=110592 inputs_without_exactly_one_correct_witness=0
  A=4 V=2 K=2 (T=5 events): inputs=16 witness_checks=400000 inputs_without_exactly_one_correct_witness=0
Check C: Batcher odd-even mergesort comparators / (n*log2 n)
  k=20: comparators=100663295 ratio_to_nlogn=4.800 (k/4=5.00)
  k=40: comparators=429909046460415 ratio_to_nlogn=9.775 (k/4=10.00)
```

**Check A.** For every small memory history, the number of accepting hidden orders equals [history legal]. All index sequences, including non-permutations, were enumerated.

**Check B.** The toy RAM is `x=M[0]; repeat K: y=M[x]; M[(x+1)%A]=y; x=(y+1)%A`. The full witness is the claimed read values plus the hidden order. Every input has exactly one accepting witness, and its output equals the direct run. This is the property that makes the contraction in 2.1 exact, checked only at these toy sizes.

**Check C.** Batcher's sorter costs (k/4)·n·log n comparators, so a practical implementation sits at T·w³.

## 4. Consequence for the circuit route

**Threshold statement (proved from 2.1).** Let a fixed program decide DIMACS SAT in T(N) steps, with N ≤ T(N) ≤ poly(N) and w = Θ(log N). Then for every field k, SAT at length N has an exact k-network, and an unambiguous circuit, of volume O(T(N)·log²N). Consequently:

- If, for some fixed field k, vol_k(SAT_N)/(N log²N) is unbounded as N → ∞, then SAT is not in DTIME_RAM(O(N)). This holds even for programs of bounded size chosen per length.
- vol_k(SAT_N) ≥ N(log N)^{2+δ} forces T(N) = Ω(N(log N)^δ) infinitely often.
- vol_k(SAT_N) ≥ N^j·(log N)^{2+δ} excludes O(N^j).

Where this leaves things:

- **Current bound.** The SAT bound is N(log N)^{σ_k}, so the exponent of log N must rise from σ_k to 2+δ with the known simulation.
- **What a better simulation could do.** The circuit route is governed by the run exponent c_lin ∈ [σ_k, 2]. A better simulation could lower the threshold toward N(log N)^{c_lin}. The per-step bound c* ≥ 1+σ_k (≥ 3/2 in a port-free characteristic) is measured on a family with only T = N/log N steps. It does not bound c_lin above σ_k (≥ 1/2 without ports). For an N-step run on N bits the shown floor is only N(log N)^{σ_k}; the known ceiling is N log²N.
- **Model.** A deterministic-Boolean-circuit-only lower bound of ω(N log²N) is **not** shown to suffice (2.6). The bridge must be stated for networks, unambiguous circuits or parity circuits. The list-distinctness technique produces bounds in exactly those models.
- **Families.** A family on which SAT has RAM time T_F caps at T_F·log²N. The list, lookup and sorting-check families (T_F = O(N/log N)) therefore cap at N log N and can never bridge. The hard family must be one with no known linear-time RAM algorithm, such as the F_3 product check of the companion note. [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)

## 5. Three standard tests

- **(a) Fast solver on the hard family?** No RAM lower bound is claimed. The network bound used (D_w) holds on a family with an O(N/log N)-step RAM solver. That is consistent because it is a size bound, and Section 4 records that this family caps below the threshold.
- **(b) 2-SAT?** The simulation gives 2-SAT networks of O(N log²N), since 2-SAT is in linear RAM time. Any bound above the threshold must therefore fail for 2-SAT, as it should. The bracket in 2.2–2.3 concerns simulation and makes no claim about 2-SAT.
- **(c) Oracle of the relativized-clock note?** Only that note's machine definition was read: one query instruction submits an arbitrarily long packed string and receives a membership bit. Such an instruction breaks the w^{1+o(1)} per-step cost of 2.1. The threshold statement therefore uses that one instruction reads O(w) bits and does not relativize to that oracle, which is the property the barrier demands. It does not by itself supply a lower bound. [Relativized clock](relativized-clock.md)

## 6. Exact obstruction and next lemma

- **To lower the threshold:** an exact network for the decision gather G_w of volume m·w^{2−ε}, or any RAM simulation below exponent 2. The Fourier preprint attains exponent 1/2+ε for linear Fourier circuits. Whether the gather admits m·w^{3/2+ε} (so c* = 3/2) is open. Counting tables over a field gives only linear lower bounds on rearrangeable topologies, so nothing known here excludes it.
- **To prove alternative (ii) for decisions:** a single-output network lower bound of m·w^{2−o(1)} for G_w or D_w. The no-ports technique, as written, stops at √(log q) per bit.
- **For the circuit route itself:** a SAT-projectable decision problem with exact-network volume ω(N log²N) and no linear-time RAM algorithm. The companion note shows that the list-distinctness technique cannot supply it. [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)

## 7. What is not proved

- The exact values of c* and c_lin. What is proved: c* ∈ [1+σ_k, 2] for k finite, c_lin ∈ [σ_k, 2], and the identity c*_net(k) = 1+γ_k (from the batched-last-writers equivalence).
- Any T·polylog T deterministic-circuit simulation of RAMs.
- The ℚ form of 2.4. The positive-characteristic form under one-sided randomized Weak ETH rests on the preprints and the journal note.
- The Li–Li statements are conditional and taken from abstracts only.
- Everything in 2.2–2.4 rests on the 24 November 2026 preprints. The journal checked the list theorem in Lean; the ports dichotomy and the cited [oaG]/[oaP] results were not checked here.

## Sources and reading status

- The matrix-multiplication preprint of 24 November 2026 (upstream tree at the journal's pinned commit: https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026), read from a local copy of its sources whose revision was not compared with that commit: `obstruction.tex` and `list.tex` in full; `sorting.tex` lines 1–60 only. Its sorting theorem is conditional on ω < 9/4 and is vacuous.
- The tape-multiplication preprint of the same date (https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-logarithmic-exponent-of-integer-multiplication-on-tapes-November-24-2026), from a local copy: `intro.tex` in full; the statement of Theorem `thm:noports` in `graphs.tex`.
- The Fourier preprint of the same release: `intro.tex` in full.
- Asharov–Lin–Shi, https://arxiv.org/abs/2010.09884: abstract only.
- Farhadi–Hajiaghayi–Larsen–Shi, https://arxiv.org/abs/1811.01313: abstract only.
- Ben-Sasson–Chiesa–Genkin–Tromer, ECCC TR12-125 (https://eccc.weizmann.ac.il/report/2012/125/); Heath et al., https://arxiv.org/abs/2309.05133: search snippets only.
- arXiv:2502.17779 (Williams, square-root space): abstract read; not relevant, not cited.
- Robson, TCS 82 (1991) 141–149: not accessed (bibliographic record).
- AKS 1983, Pippenger–Fischer 1979, Schönhage–Strassen: not accessed (standard; cited via the journal).
- Journal notes read: the circuit-bound, list-and-matrix-costs, trace-multiplicity, packed-band-transfer, read-only-lookup and batched-last-writers notes; excerpts of the ports, tape-complement, fixed-verifier multiplicity, delayed-forecast and relativized-clock notes (machine definition only), and the results-index entry on the per-step aggregate. [Trace multiplicity](trace-multiplicity-and-list-volume.md) · [Tape time under complement](tape-time-under-complement.md) · [Fixed RAM verifiers](multiplicity-and-size-of-fixed-ram-verifiers.md)
