# The space route caps below N^{5/4} and its premise is harder than the original question

Space lower bounds for SAT can exclude RAM time only below N^{5/4} along this route, and the premise the route needs is harder than the original question. For a fixed program P, log-word RAM time t fits in O((t+N)^{4/5} log^{C(P)+1}(t+N)) work bits, by a quadratic one-tape scan followed by the unrefereed two-fifths-power preprint, so "SAT ∉ DSPACE(N^{4b/5} log^c N) for every fixed c" excludes RAM time O(N^b). Because SAT ∈ DSPACE(O(N/log N)) unconditionally, no b ≥ 5/4 can be excluded this way, let alone N^2 or N^3. The premise needed at linear time, SAT ∉ DSPACE(N^{4/5+ε}), implies both the target and NP ⊄ polyL (so NP ≠ L), which the target is not known to imply. Its premise is stated under hypothesis W (for every ε > 0, SAT ∉ DTIME(2^{N^{1−ε}})), which implies it and is consistent with the pinned preprint "The Exponential Time Hypothesis is False"; statements under ETH or SETH are vacuous inside the journal, because that preprint claims to refute both. The one unconditional by-product, DSPACE(n) ⊄ DTIME_RAM(n^{5/4−ε}), is the standard space-hierarchy corollary of the chain that the simultaneous-space note already instantiates; no novelty is claimed for it. The linear, quadratic and cubic questions remain open. [Simultaneous space](simultaneous-space.md)

Standing of the missing step, SAT ∉ DSPACE(N^{4/5+ε}):
- It implies NP ⊄ polyL, and so NP ≠ L.
- It is implied by hypothesis W of Section 4 (no 2^{N^{1−ε}}-time SAT algorithm), which is consistent with the October 2026 counting preprint. It is also implied by ETH, which that preprint claims to refute.
- With the current exponents (two-fifths plus a quadratic one-tape scan) the route can never exclude RAM time N^{5/4}. Reaching N^2 would need a one-tape space exponent below 1/4, or a subquadratic RAM-to-one-tape simulation.

A natural first step in the other direction, SAT in N^{1−ε} space, would refute W. It would put SAT in time 2^{O(N^{1−ε})}, polynomially below the exponent N/log^{3/2} N that the October 2026 counting preprint gives at bounded density, and it would give NTIME(n) ⊆ DTIME(2^{n^{1−ε'}}). The weaker target, o(N/log N) space, would only refute ETH, which that preprint already claims to refute (in polynomial space); so it is not a barrier, and whether SAT ∈ DSPACE(o(N/log N)) is open.

## 1. Statements

- **Lemma A (chain).** Take any fixed program P of the log-word unit-cost RAM. It has word width w = Θ(log N), unrestricted workspace, indirect loads and stores, and multiplication and division allowed. Then there is a fixed deterministic Turing machine M_P with an endmarked read-only input, with the following property. For every N-bit input x on which P halts within t steps, M_P(x) = P(x), and M_P uses O((t+N)^{4/5} log^{C+1}(t+N)) work bits. Here C = C(P) is the preprint's logarithmic exponent for the one-tape simulator of P. It is numerically unspecified, and the source allows it to depend on the simulated machine.
- **Implication B.** For every fixed b ≥ 1 and every a > 4b/5: SAT ∉ DSPACE(N^a) implies SAT ∉ DTIME_RAM(O(N^b)).
- **Question C (the converse direction).** Is SAT ∈ DSPACE(N^{1−ε}) for some fixed ε > 0?

## 2. The simulation chain

### Step 1: RAM to one writable tape in O(t^2 w^2 + tN) steps

*Status:* a manuscript proof, not formalized. The simultaneous-space note already records the same scan, at Õ((n+t)t), as "the familiar quadratic sequential-scan overhead", with a Cook–Reckhow link. Here it is re-proved with explicit costs. [Simultaneous space](simultaneous-space.md)

The quadratic RAM-to-Turing-machine bounds usually cited do not give this step. Pippenger–Fischer, which Williams cites for log-cost RAMs, lands on multitape machines. Converting multitape to one tape squares again (Hartmanis–Stearns), giving T = Õ(t^4) and space Õ(t^{8/5}), which is useless. The two-fifths theorem needs a single writable head, so the direct scan below is needed.

*Machine layout.*
- The input sits on the endmarked read-only tape.
- The writable tape, initially blank, holds two things:
  - a time-ordered list of at most t write records (address, value), each 2w + O(1) cells;
  - a *cursor block* of O(w) cells. It holds the fixed number of RAM registers, the sought address, a candidate value, an input-position counter and arithmetic scratch. It lives on a fixed number of tracks disjoint from the record tracks, or equivalently is swapped past each record, which is the O(w^2)-per-record move below.
- *Setup.* One O(N) scan of the input, with an O(log N)-bit counter, computes N, w and ⌈N/w⌉.

*One RAM instruction.*
- **Register arithmetic.** Done inside the cursor block in O(w^2) moves. Schoolbook multiplication and division make w passes over O(w) cells.
- **Load from address a.** Sweep the cursor block across the record list. Shifting an O(w)-cell block by one cell costs O(w) moves, so passing one record costs O(w^2). At each record, compare its address with a by zig-zagging inside an O(w)-cell window, in O(w^2) moves. On a match, copy the value into the candidate field in O(w^2). Records are in time order, so the last match is the latest write.
  - If nothing matched and a < ⌈N/w⌉, fetch input word a. Leave the writable head on the counter, move the input head to the left endmarker, then advance it a·w cells while decrementing the counter (amortized O(1) per move). Then read w bits. Cost O(N + w^2).
  - Otherwise the value is 0.
- **Store.** Append a record at the right end, where the sweep ends, in O(w^2). A store with no preceding load still sweeps to the right end and back, at O(L w^2).
- **Return.** Sweep back in O(t w^2).

*Total.* With L ≤ t records, one instruction costs O(L w^2 + N). Hence T ≤ c_P (t^2 w^2 + tN + N). With w = Θ(log N), and since tN ≤ (t+N)^2, this is T = O((t+N)^2 log^2(t+N)). No assumption t ≥ N/w is needed.

This step is where the proof uses the fact that one instruction moves O(w) bits: the carried block has O(w) cells. See test (c) in Section 6.

### Step 2: one writable tape in two-fifths-power space

*Source:* OpenAI, "Simulating One-Tape Time in Two-Fifths-Power Space", 25 Sep 2026 (unrefereed preprint). [One-tape theorem](https://github.com/openai/math/blob/main/preprints/Simulating-One-Tape-Time-in-Two-Fifths-Power-Space-September-25-2026/article.pdf)

*How much was read.*
- Read in full: abstract, Introduction and Theorem 1, the section "Time lower bounds from the space hierarchy", and subsection `sec:balance`.
- Skimmed for logarithmic factors only: the evaluation and simulation sections.

*Theorem 1 as stated.* The model is a fixed deterministic machine with one writable tape and head, plus a fixed number of read-only input heads. Each initial symbol within distance T of a head origin must be supplied by an accessor in polylog(T) space. Given a binary cap T ≥ 2, the finite-control and halting outcome by time T is computable in Õ(T^{2/5}) = O(T^{2/5} log^C(T+2)) work bits, with C "a fixed constant". With unknown halting time t, the bound is Õ((t+2)^{2/5}) via doubling caps.

*Caveats from the source.*
- Simulation time is unrestricted ("Limits": "It cannot be iterated as a time improvement").
- "No log-free endpoint at exponent 2/5 is asserted."
- The source gives no numerical value for C, and says "constants may depend on the fixed machine and accessor". A reading during review confirmed that the Lean comparator statements (`OneTapeSpace.lean`) quantify the exponent after the machine is fixed. So C = C(P).
- `lean/docs/137.md` in the same repository reports a Lean formalization of exactly this simulation, with bound O(T^{2/5}(log(T+2))^C). The scope document was fetched; the Lean files were not inspected for this note. [Source formalization scope](https://raw.githubusercontent.com/openai/math/main/lean/docs/137.md)

*Why the access condition holds.* The writable tape starts blank and the input is ordinary. Rescanning with an O(log(N+T))-bit counter supplies any symbol.

### Composition

Space is O(T^{2/5} log^C T) = O((t+N)^{4/5} log^{C+4/5}(t+N)) bits, plus O(log N) for counters, with C = C(P). Doubling caps removes any constructibility requirement on t. This proves Lemma A, up to the correctness of the preprint.

### Attribution

Li–Tell's footnote 1, which the steering file cites for this chain, was **not accessed**. Williams (https://arxiv.org/abs/2502.17779v1) was read via its TeX source: Remark `rem:RAM` and the section "Open problems" in full. He asks: "Can time-t random-access Turing machines be simulated in space O(t^{1−ε})?" He records the earlier best as O(t/log t) for random-access models (Paul–Reischuk 1981; Halpern–Loui–Meyer–Weise 1986), and separately asks for an O(t^{1/2−ε}) one-tape simulation. Given the preprint, Lemma A would answer the RAM question with ε = 1/5 − o(1). Presumably this is the observation Li–Tell attribute to Williams. No priority is claimed. [Where the hierarchy proof stops](../research-steering.md#where-the-hierarchy-proof-stops)

## 3. Exact implications and the 5/4 ceiling

**Proposition B (from Lemma A).** For fixed b ≥ 1: if SAT ∉ DSPACE(N^{4b/5} log^{c} N) for every fixed c, then no log-word RAM decides SAT in time O(N^b). The quantifier over c is needed because C(P) depends on the program. Implication B (a > 4b/5) is unaffected.

Reading this at particular exponents:
- b = 1 needs a > 4/5, so "SAT needs N^{0.81} space" suffices.
- b = 1+δ needs a > 4(1+δ)/5.
- "SAT ∉ DSPACE(N^{1−ε}) for every ε > 0" excludes every b < 5/4.

**Proposition D (unconditional upper bound; proved here).** For DIMACS CNF, SAT ∈ DSPACE(k + O(log N)), where k is the number of distinct variables that actually occur. Moreover k ≤ k_max(N) = Θ(N/log N). The same holds for the journal's fixed-width binary encoding, since k ≤ min(n, 3m) and N ≈ 3m⌈log₂ n⌉.

*Bound on k.* The i-th smallest of k distinct positive integers has at least digits(i) decimal digits, so Σ_{i≤k}(digits(i)+1) ≤ N/8. The bound is attained by `p cnf k 1 / 1 2 … k 0`.

*Algorithm.* Index the assignment bits by **first-occurrence rank**, not by variable name, because the header's n and the numerals need not be log-bounded. The rank of the variable at occurrence p is the number of first occurrences up to and including that variable's first occurrence. "Occurrence q is a first occurrence" is decided by comparing numerals digit by digit with two input pointers. Both are O(log N)-space, polynomial-time computations.

Enumerate all 2^k assignments as a k-bit counter. For each one, check every clause by computing the rank of each literal's variable. Accept if some assignment satisfies every clause. Work space is k + O(log N).

*Finite check* (output abridged to six rows): [dimacs_distinct_variable_bound.py](../audits/dimacs_distinct_variable_bound.py)

```
$ python3 dimacs_distinct_variable_bound.py
 log2N           N_bits            k_max  k*log2N/N    k/N^0.8
    10             1024               41     0.4004       0.16
    20          1048576            23693     0.4519       0.36
    30       1073741824         16147645     0.4512       0.96
    40    1099511627776      12379172045     0.4504       2.88
    50 1125899906842624   10123239964426     0.4496       9.21
    60 1152921504606846976 8542723481586290     0.4446      30.35
limit log2(10)/8 = 0.4152
```

(The full output also lists exponents 15, 25, …, 55; their ratios range from 0.44 to 0.47. The e = 10 row shown above is 0.40.)

*Correctness check of the algorithm at finite size.* `first_occurrence_rank_enumeration_check.py` implements the decider. Its only mutable state is the k-bit counter and a fixed number of integer positions; the input is accessed only by read-only indexing. The space bound itself is by inspection, not measured. The test formulas have 1–9 distinct variables with names drawn from 1..10^6, and 1–3 literals per clause. CaDiCaL is found via `$CADICAL`, PATH or a Lean toolchain, and each formula is piped to it on stdin; the run takes about 20 s. [first_occurrence_rank_enumeration_check.py](../audits/first_occurrence_rank_enumeration_check.py)

```
$ python3 first_occurrence_rank_enumeration_check.py 300
trials=300 agree=300 sat=129 unsat=171
```

All 300 verdicts agree with CaDiCaL (seed 20261127).

The last column of the k_max table bears on the statement "N^{4/5} bits is fewer than one assignment". For the extremal file it holds from about N ≈ 1.4318·10^9 bits (log₂ N ≈ 30.415). Because k_max is a step function, the predicate k_max(N) > N^{4/5} oscillates near the threshold, so a bisection is not valid. In an exhaustive scan of a ±3000 window plus coarse grids on both sides, it first holds at N = 1,431,755,144 and holds for every N ≥ 1,431,755,504 in the scanned range (an independent scan during review agrees): [extremal_file_space_crossover.py](../audits/extremal_file_space_crossover.py)

```
$ python3 extremal_file_space_crossover.py
window [1431752300, 1431758300]: first success 1431755144, last failure 1431755503
coarse grid below window (step 997 from 2^20): successes found = 0
coarse grid above window (step 1000003 to 2^33): failures found = 0
```

The statement is true asymptotically.

**Ceiling.** By Proposition D, the premise of Proposition B is *false* for every b ≥ 5/4. More precisely, for each program P the route can exclude only times with t^{4/5} log^{C(P)+1} t = o(N/log N), that is, t below N^{5/4}/log^{5(C(P)+2)/4} N.

Output of the exponent bookkeeping, abridged (rows for b = 21/20, 11/10 and 3 omitted from the first block; the second block shows only its header and ceiling lines): [space_route_exponents.py](../audits/space_route_exponents.py)

```
$ python3 space_route_exponents.py
two-fifths preprint (Sep 2026) + direct one-tape scan: alpha=2/5 beta=2  space exponent per unit RAM time = 4/5
   exclude RAM time N^1     needs SAT notin DSPACE(N^4/5    polylog)  -> premise possible (a<1)
   exclude RAM time N^6/5   needs SAT notin DSPACE(N^24/25  polylog)  -> premise possible (a<1)
   exclude RAM time N^5/4   needs SAT notin DSPACE(N^1      polylog)  -> premise FALSE: SAT in DSPACE(N/log N)
   exclude RAM time N^2     needs SAT notin DSPACE(N^8/5    polylog)  -> premise FALSE: SAT in DSPACE(N/log N)
   ceiling: b < 5/4
classical sqrt(T) one-tape bound (Hopcroft-Ullman/Paterson): alpha=1/2 beta=2  space exponent per unit RAM time = 1
   ceiling: b < 1
to reach b=2 with beta=2 need one-tape space exponent alpha < 1/4
to reach b=3 with beta=2 need one-tape space exponent alpha < 1/6
```

What the ceiling means:
- The route can never reach the quadratic or cubic targets.
- With the classical √T one-tape bound it would exclude nothing. Its whole content is the preprint's improvement of the exponent by 1/10.
- Reaching N^2 would need a one-tape space exponent below 1/4, or a RAM-to-one-tape simulation faster than quadratic.

## 4. The hypothesis W, ETH, SETH, and NP versus L

**State of knowledge inside the journal.** The journal uses the October 2026 preprint "The Exponential Time Hypothesis is False" as a pinned external theorem (commit 3344da5); it is cited in the projected-parity-holes, native-history-parity and six-permutation notes. As quoted there, and as read at the pinned commit during review (that preprint was not read for this note), its Theorem 1.1 gives: [ETH preprint](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf) · [Projected parity holes](projected-parity-holes.md) · [Native-history parity](parity-of-native-histories.md) · [Six permutations](branching-in-equations-over-six-permutations.md)
- deterministic exact counting of width-k CNF in poly_k(v+m)·2^{O_k(v log log v/√log v)} time and polynomial space;
- at m ≤ Dv, time 2^{O_{k,D}(v/√log v)}.

So statements headed "under ETH" or "under SETH" are vacuous inside the journal. The route has to be based on a hypothesis that is consistent with that preprint.

**Hypothesis W.** For every ε > 0, SAT (DIMACS, N bits) ∉ DTIME(2^{N^{1−ε}}).

An equivalent form, W', needs no sparsification: for every δ > 0 and every fixed D, 3-SAT with at most Dv clauses on v variables ∉ DTIME(2^{O(v^{1−δ})}).
- *¬W ⇒ ¬W'.* A bounded-density 3-CNF has N = Θ(v log v), so 2^{N^{1−ε}} = 2^{v^{1−ε+o(1)}}.
- *¬W' ⇒ ¬W.* Convert an N-bit CNF by Tseitin splitting to a 3-CNF with O(N) variables. Pad it with O(N) fresh variables, each in one tautological clause, so that it has linear density. Then 2^{O(v^{1−δ})} = 2^{O(N^{1−δ})}.

**W is consistent with the October preprint.** Transferred by Tseitin conversion, the preprint gives SAT in time 2^{O(N/log^{3/2} N)} at bounded density, and at most 2^{O(N log log N/√log N)} for arbitrary CNF, using v' = O(N). Both are 2^{N^{1−o(1)}}, which W does not exclude.

**Relation to the journal's variable-count Weak ETH** (from the November tape preprint, as recorded in the results index). That hypothesis excludes 2^{O(v^{1−δ})}·poly(n) on 3-CNFs of arbitrary density. [Results index](../RESULTS.md#result--a-superlinear-boolean-circuit-lower-bound-for-3-sat)
- *W ⇒ variable-count Weak ETH (proved).* If 3-SAT on v variables ran in 2^{O(v^{1−δ})} poly(n) at any density, the same Tseitin conversion would give SAT in 2^{O(N^{1−δ})} poly(N), contradicting W.
- *The converse needs sparsification with subconstant ε,* that is ε = v^{−γ} with c(ε) polynomial in 1/ε. This form is recalled from Calabro–Impagliazzo–Paturi (2006) but was not verified.
- Constant-ε IPZ sparsification costs 2^{εv}, so it can never contradict a 2^{v^{1−δ}}-type hypothesis.
- So the note adopts W, or equivalently W', directly. The tape preprint's exact definition of Weak ETH (density, deterministic or randomized) was not checked.

**What W gives, by configuration counting (DSPACE(s) ⊆ DTIME(2^{s+O(log N)})):** SAT ∉ DSPACE(N^{1−ε}) for every ε > 0, and hence the premise of Proposition B at every b < 5/4. It does **not** give o(N/log N) or Θ(N/log N) space lower bounds.

**Proposition E (proved here; quantitative form).** SAT ∈ DSPACE(s) implies that 3-SAT with at most Dv clauses on v variables lies in DTIME(2^{s̄(O_D(v log v)) + O(log v)}), where s̄ is the monotone majorant of s.
- For example, s = N^{1−ε} gives 2^{v^{1−ε+o(1)}}. That refutes W' and so W, and beats the October preprint's bounded-density bound 2^{O(v/√log v)} polynomially in the exponent.
- *ETH corollary* (constant-ε IPZ sparsification, Impagliazzo–Paturi–Zane 2001, from memory): if SAT ∈ DSPACE(s) with s = o(N/log N), then ETH fails.
- Constant-ε sparsification transfers only ETH-type conclusions (2^{εv+o(v)}) to arbitrary density. Since the October preprint claims ETH is false anyway (by a polynomial-space algorithm), this corollary is no barrier, and whether SAT ∈ DSPACE(o(N/log N)) is open. Under W, SAT ∉ DSPACE(N^{1−ε}) for every ε > 0, while SAT ∈ DSPACE(O(N/log N)) unconditionally (Proposition D).
- The form Θ(N/log N) would need ETH at bounded density. If the preprint's bounded-density exponent v/√log v were optimal, configuration counting would give SAT ∉ DSPACE(o(N/log^{3/2} N)). Even under ETH, such lower bounds hold only infinitely often.

Other consequences:
- SAT ∈ DSPACE(N^{1−ε}) would also give NTIME(n) ⊆ DTIME(2^{n^{1−ε'}}), through quasi-linear Cook–Levin reductions.
- Any "nondeterministic Williams theorem" NTIME(t) ⊆ DSPACE(t^{1−ε}) would put SAT in DTIME(2^{O(N^{1−ε} polylog N)}) and so refute W, because SAT lies in NTIME(N log N) on multitape machines. This is folklore-level; no priority claimed.

**Proposition S (CNF-SAT hypothesis; same counting).** Suppose some deterministic machine decides CNF-SAT (unbounded clause width) in (1−δ)k + O(log N) work bits, with a binary work alphabet. Then CNF-SAT ∈ DTIME(2^{(1−δ)n}·poly(N)).
- That contradicts the CNF form of SETH: for every δ > 0, CNF-SAT on n variables and N input bits is not in DTIME(2^{(1−δ)n} poly(N)). SETH implies this form.
- The October 2026 preprint claims to refute SETH. Its theorem is stated for fixed width k, and whether its k-dependence also refutes the CNF form was not checked.

**Where the premise sits.** The chain of implications is:

W ⇒ SAT ∉ DSPACE(N^{1−ε}) for every ε > 0 ⇒ SAT ∉ DSPACE(N^{4b/5} polylog) for all b < 5/4 ⇒ SAT ∉ DSPACE(N^{0.81}) ⇒ SAT ∉ DSPACE(polylog N) ⇔ NP ⊄ polyL ⇒ NP ≠ L.

ETH, which the October 2026 preprint claims is false, would give the stronger SAT ∉ DSPACE(o(N/log N)).

Up to polylogarithmic factors, the premise also equals NTIME(n) ⊄ DSPACE(n^{4/5+ε}). In one direction, SAT ∈ NTIME(N log N) on multitape machines. In the other, the quasi-linear reductions have bits computable in polylog space.

**With a time hypothesis as the premise, the route adds nothing.** W directly gives SAT ∉ DTIME_RAM(2^{N^{1−ε}}), whereas through the route W yields only N^{5/4−o(1)}. The same holds for ETH. The route's genuine content is that it turns a *space* hypothesis into a time bound.

**The target is not known to imply NP ≠ L.** That would need "SAT ∈ L ⇒ SAT ∈ DTIME_RAM(N)", and log-space algorithms run in polynomial time of unbounded degree. Conversely, NP ≠ L is not known to imply the target. So the premise is at least as hard as each of the two separately.

## 5. The converse first step: SAT in N^{1−ε} space

Any such algorithm would refute W (Proposition E). That would be a polynomial improvement in the exponent over the October 2026 counting preprint, obtained in small space.

Three nearby facts:
- o(N/log N) space would only refute ETH, which the October preprint already claims to refute (by a polynomial-space algorithm). Whether SAT ∈ DSPACE(o(N/log N)) is open.
- (1−δ)·#vars space for unbounded-width CNF would refute the CNF form of SETH (Proposition S).
- The trivial algorithm achieves O(N/log N) (Proposition D).

No attempt beyond this reduction was made, since a success would refute W.

## 6. The three standard tests (applied to the premise and to Lemma A)

**(a) Fast globally correct solver.** The premise names no family. Any witness family needs:
- more than N^{0.81} distinct variables (otherwise enumeration fits in N^{0.81} bits), and
- no linear-time RAM solver (otherwise Lemma A gives N^{4/5} polylog space).

So every packed-scan family of the journal fails as a witness.

*The standard hierarchy corollary (no novelty claimed).* The chain of Section 2 is the one the simultaneous-space note already instantiates for its diagonal J (a quadratic one-tape scan, then two-fifths-power space, giving Õ(n^{49/50}) work bits), and the observation behind it, about t^{4/5} space for RAM time t, is recorded in the steering file from Li and Tell (§1, footnote 1), who credit Williams. Its standard space-hierarchy corollary is DSPACE(s) ⊄ DTIME_RAM(s^{5/4−ε}) for space-constructible s ≥ n (meant for polynomially bounded s, so that the Θ(log N) word width stays meaningful). For example, the preprint's bounded-space-halting language H is DSPACE(n)-complete under log-space reductions of linear output length; composing its Corollary (proof of `cor:bounded-space-halting`) with Step 1 gives H ∉ DTIME_RAM(O(N^{5/4−ε})) for every ε > 0, because Lemma A would put H into DSPACE(N^{1−4ε/5} polylog), and composing with the reduction contradicts the space hierarchy. This separates DSPACE(n) from DTIME_RAM(n^{5/4−ε}); equivalently, it is a polynomially superlinear log-word RAM lower bound for a *linear-space-complete* problem, modulo the preprint. Explicit problems outside DTIME_RAM(n^{1+δ}) already follow from the RAM time hierarchy, J being one, so the only point is linear-space completeness. It passes test (a) automatically, being a hierarchy theorem, but it is on the wrong side for SAT. [Simultaneous space](simultaneous-space.md) · [Where the hierarchy proof stops](../research-steering.md#where-the-hierarchy-proof-stops)

Two scope notes:
- The preprint's hierarchy section asserts "no general multitape or random-access bound".
- `lean/docs/137.md` places the hierarchy and bounded-space-halting corollaries outside the formalization, so the completeness of H and the hierarchy step are manuscript-level.

It does not transfer to SAT. A polynomial reduction from H to SAT would give DSPACE(n) ⊆ NP, and by padding NP = PSPACE.

The other two tests, applied to the corollary:
- **(b)** It is a space-hierarchy argument for a DSPACE(n)-complete language, so it says nothing about 2-SAT, which lies in DSPACE(log² N).
- **(c)** It uses Step 1, which needs each instruction to move O(w) bits. With the Θ(N log N)-bit opcode, Step 1 only gives Õ(t²N) one-tape time, so the argument does not go through as written relative to that oracle.

**(b) 2-SAT.** 2-SAT ∈ NL ⊆ DSPACE(log² N) (Savitch), so the premise is false for 2-SAT. Any proof must use the NP-hardness of 3-SAT. Lemma A is a simulation and applies to every language.

**(c) Relativized clock.** Convention: the oracle space machine has a write-only query tape that is not charged to space and is erased at each query (Ladner–Lynch). [Relativized clock](relativized-clock.md)
- In the p=1 world, the linear-time solver's single query is the wrapper Q₁(1F) = 1·1F·1^P, with P = 2m⌈log₂(m+2)⌉ and m = N+1. It is in A exactly when F is satisfiable. A log-space transducer can write it: two tag bits, a copy of the input, then P ones counted with an O(log N)-bit counter. So **SAT ∈ L^A, and the premise is false relative to A.**
- Relative to TQBF, NP^{TQBF} = PSPACE ⊆ L^{TQBF}, so the premise is false there too.
- So a proof of the premise must be non-relativizing, just as for the original target. The route does not escape the relativization barrier.
- Lemma A uses "one instruction reads O(w) bits" in Step 1. With the Θ(N log N)-bit opcode, the carried block is that long, Step 1 gives only T = Õ(t²N), and at t = Θ(N) the resulting bound is Õ(N^{6/5}), which is useless. Moreover, an oracle machine's query tape is a second writable tape, so the preprint's one-writable-tape model does not apply as stated.
- With a *charged* query tape, an N^{0.81}-space machine cannot write the wrapper, and in that convention the premise relative to A is not settled here.

## 7. Exact obstruction and next step

**The missing step** is SAT ∉ DSPACE(N^{4/5+ε}), or, up to polylog factors, NTIME(n) ⊄ DSPACE(n^{4/5+ε}). Any ω(log N) space lower bound for SAT already implies NP ≠ L, so no such bound is known for any language in NP. The route asks to go from that state of knowledge to N^{0.81}.

**Why the journal's levers do not apply.**
1. *Space hypotheses do not compose across quantifiers.* From SAT ∈ DSPACE(s), the direct argument gives Σ₂-SAT only DSPACE(|x| + s), because the outer witness must be stored to feed the inner machine. So the alternation trading that drives the journal's time–space band, the H(e) iteration of the band note, has nothing to trade. [Band](sat-time-space-band.md)
2. *A diagonal contradiction would run the wrong way.* It would need a language in NTIME(t) outside DSPACE(t^{4/5}), which is the reverse of Williams' direction.
3. *The two-fifths simulator has no time bound.* Any premise of the form "SAT ∉ C" with C ⊇ L implies NP ≠ L. So a variant that avoids NP≠L-hardness must bound time as well as space, as a simultaneous premise does, for example DTIME_RAM(t) ⊆ DTISP_RAM(O(t L^a), O(t/L^{2a+7})) against the band. That is exactly the speedup lemma at which "Where the hierarchy proof stops" halts, and the factored-lookups and simultaneous-space notes already name it as the open step for this representation. **The space route therefore merges back into the hierarchy route. As a pure-space route its premise implies both the original target and NP ⊄ polyL, so in the implication order it is not easier than the original question.** [Factored lookups](factored-lookups.md)

**Next step.** No further lemma is suggested for SAT along this route.

## 8. What is not proved

- The two-fifths theorem is not verified here. It is an unrefereed preprint; its reported Lean formalization was not inspected; C = C(P) is unknown and program-dependent.
- The October 2026 counting preprint was not read for this note. Its Theorem 1.1 is used as quoted by the journal and as read during review.
- That W implies the journal's variable-count Weak ETH is proved above. The converse rests on quantitative sparsification (Calabro–Impagliazzo–Paturi 2006), which is unverified.
- Whether SAT ∈ DSPACE(o(N/log N)) is open; nothing here bears on it beyond Proposition D.
- Step 1 is a manuscript proof, not formalized.
- Li–Tell's footnote 1 was not read. The IPZ sparsification lemma is used from memory and was not re-read.
- No unconditional statement about SAT's space or RAM time is proved. Only the stated implications are proved, together with the unconditional upper bound of Proposition D.
- The hierarchy corollary depends on the preprint and on its Corollary's reduction, which was read but not checked line by line.
- The relativization claim for a charged query tape is open.

## Sources and access

| Source | Access |
| --- | --- |
| OpenAI two-fifths preprint, TeX sources | main.tex, introduction, hierarchy and `sec:balance` read in full; evaluation and simulation skimmed |
| `lean/docs/137.md` of the same repository | read in full |
| Williams, https://arxiv.org/abs/2502.17779v1 (e-print TeX) | `rem:RAM` and open problems read in full; remainder grep only |
| Li–Tell, ECCC TR26-233 | not accessed |
| Impagliazzo–Paturi–Zane (2001) | not accessed; standard statement |
| "The Exponential Time Hypothesis is False" (Oct 2026, pinned at journal commit 3344da5) | not accessed for this note; Theorem 1.1 as quoted in the projected-parity-holes note and as read at the pinned commit during review |
| Calabro–Impagliazzo–Paturi (2006), quantitative sparsification | not accessed; from memory, unverified |
| Pippenger–Fischer, Cook–Reckhow, Hartmanis–Stearns, Savitch, Ladner–Lynch, Paul–Reischuk, Halpern–Loui–Meyer–Weise | not accessed; cited for standard facts only |

## Reproducing the checks

Run from `audits/`. The rank check needs CaDiCaL (via `$CADICAL`, PATH or a Lean toolchain under `~/.elan/toolchains`); the crossover scan takes about two and a half minutes.

```
python3 dimacs_distinct_variable_bound.py
python3 space_route_exponents.py
python3 first_occurrence_rank_enumeration_check.py 300
python3 extremal_file_space_crossover.py
```
