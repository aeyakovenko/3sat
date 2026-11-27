# Black-box routes through the diagonal compile stop at length o(s), where a packed compile would already exclude linear SAT

Take the compiler criterion for the square-time deterministic diagonal alone, whose files have length s, with a compile of M bits. In a black-box model of that criterion with hidden clause signs, a procedure reads the compiled structure and calls a SAT solver charged N·log^a N on N-bit queries. There, deciding the verdict on Tseitin structures of M bits costs Ω(M·log^a M) in solver charges, so under linear SAT (a = 0) no route through the model passes compile length o(s). The bound is matched on files without repeated clauses; with repeated clauses the one-query procedure costs Θ(M log M·log^a M). Outside the model, a direct route shows that a compile of the diagonal of length o(s·log^θ s) with constant-time packed access would imply SAT ∉ DTIME[O(N/log^θ N)], for 0 ≤ θ ≤ 1. So at θ = 0 a packed compile of length o(s) would exclude linear SAT, improving the o(s/log² s) known for polylogarithmic bit indexers. Packed access is an extra hypothesis that the criterion, whose indexer reads a bit in polylogarithmic time, does not supply, and no such compile is known. The compile exponent b, with h-step nondeterministic runs compiled into h·log^b h bits, is exactly 3 for switching-network compiles and lies between 2 + σ_k and 3 for exact ones, where σ_k is the exact-network exponent of the simulation note. The proofs are at manuscript level, with finite checks. Nothing here is progress on the bound; the linear, quadratic and cubic questions remain open. [Compiler criterion](compact-compilers-and-linear-sat-time.md) · [Round three](parallel-proof-attempts-of-27-november-round-three.md)

## Setting

Notation, as in the round-three record of the diagonal-only criterion:
- J is the square-time deterministic diagonal, with clock T = Cn², and s = Θ(T) is the length of a J-file.
- C_J(M) is a decision-preserving, locally indexed compile of J-files into proper DIMACS of length M.
- H_SAT is the hypothesis SAT ∈ DTIME_RAM[O(N)].
- M = ε(T)·T·log₂T.
- b is the bit exponent of a compile of h-step nondeterministic runs, meaning h·log^b h bits.

The round-three record leaves open whether C_J(o(s log s)) excludes linear SAT. Its route removes the outer existential block of the short witness by compiling the nondeterministic verifier V with the usual compile, at a log³ overhead (the V route), and stops at o(s/log² s).

The question here, for one round: in a model where a deterministic procedure may read the compiled formula and call a SAT solver, both as black boxes with stated prices, either prove that no procedure decides the source verdict in o(T) steps, or find one.

## 1. The black-box model

A black-box statement must hide three things, or it collapses:
- **The source verdict.** Otherwise the procedure computes J(x) itself, in time T.
- **Clause semantics.** Otherwise the procedure reads F and decides it internally, and a lower bound in the model would contain a lower bound on the procedure's own SAT computation, which is the open problem.
- **The solver's speed beyond what H_SAT guarantees.** A solver padded to take c·N steps on every N-bit input satisfies H_SAT, so a proof that works for every solver satisfying H_SAT must work for that one.

**Model 𝔅₁.** An instance is a pair (σ, χ).
- **The structure σ** is public. It is the DIMACS file of F with every minus sign deleted: K clause scopes, each a triple of distinct variable names, in a fixed layout. Its length is M up to the sign bits.
- **The interpretation χ** is hidden. It fixes the sign pattern of each clause, so clause j forbids exactly one pattern f_j(χ) ∈ {0,1}³ on its scope.
- **The source verdict** is β = [F(σ,χ) ∈ SAT]. It is free: the procedure has no other access to it.

A procedure D is a deterministic word RAM with word width w = Θ(log M), on an arbitrary input x independent of χ. It has:
1. **A compile oracle** that returns any w-bit word of σ at cost 1. This is packed access, which is more generous than the criterion's polylogarithmic cost per bit.
2. **A solver oracle.** D writes a query G in memory: an explicit circuit list in the format of the relativized-clock note (inputs, constants, gates, each pin a binary predecessor index). G may contain *opaque gates*. An opaque gate has 3 argument pins and an index of r = ⌈log₂K⌉ bits. The index is given either as an r-bit literal written in the gate's record, or by r index pins. Either way the gate costs at least r bits. On index j < K and arguments (a,b,c) it outputs [(a,b,c) ≠ f_j(χ)], which is the truth value of clause j of F on those values. The reply is [∃ input assignment with output 1]. The charge is c_S·|G|·log^a(|G|+2) steps, for a fixed a ∈ [−1, 0]. H_SAT is the case a = 0.
3. **Its own steps**, at unit cost.

[Relativized clock](relativized-clock.md)

𝔅₀ is the sub-model in which every index must be a literal: the compile is then used only from outside the queries. 𝔅₁ also allows computed indices, so it admits queries that access F's clauses through the indexer, such as the failure test "∃ challenge c: clause c fails under z". 𝔅₁ does not allow compiling the solver's own run into a query. That is exactly what the V route does, at the price of the compile exponent b.

## 2. Theorem BB: the black-box barrier

**Hard structures.** Let G be a connected cubic graph with vertex set V, and σ_G its Tseitin structure:
- one variable per edge;
- at each vertex v, four clauses on the three incident edges;
- the i-th clause at v forbids the i-th pattern (in a fixed order) of parity 1 − χ_v.

So χ ∈ {0,1}^V is a hidden charge vector. There are K = 4|V| clauses on 3|V|/2 variables, and the DIMACS length is M = Θ(K log K). Classically, F(σ_G, χ) ∈ SAT ⇔ ⊕_v χ_v = 0, for connected G; Part 1b of the checks confirms this exhaustively for four graphs.

**Theorem BB.** Let D be a deterministic 𝔅₁-procedure that outputs β correctly for every χ ∈ {0,1}^V. Then for some χ:
- the opaque gates in all of D's queries number at least |V| = K/4 in total;
- hence Σ_i |G_i| ≥ ⌈log₂K⌉·K/4;
- and the total solver charge is at least c_S·S·log^a(S+2), with S = ⌈log₂K⌉·K/4.

Conversely, one query decides β: the K clauses as opaque gates with literal indices, each with 3 argument pins, followed by an AND tree. On these structures it has |G| = O(K log K) = O(M), and D reads σ in O(M/w) steps. With r index *pins* instead of literals, each gate would cost Θ(log K · log|G|) bits and this query Θ(M log M), which is why literal indices are allowed.

So on these structures, in 𝔅₀ and in 𝔅₁, the cost of deciding β is Θ(M·log^a M). This is not a worst case over all files. A proper file may repeat clauses, so it can have K = Θ(M) clause occurrences, and then the one query costs Θ(M log M·log^a M). In 𝔅₀ this cost is forced: an adversary that fixes each referenced clause to forbid 000 keeps β open while 7 clauses are unreferenced. On a family with every clause on one scope, checked during review, the forced cost grows from 0.13·M at K = 2^10 to 0.39·M at K = 2^30. In 𝔅₁ the worst case over files with repeated clauses lies between Ω(M·log^a M) and O(M·log M·log^a M) and is not determined here.

*Proof.* Fix a witness y of a query G, that is, an input assignment that drives G's ordinary gates. Evaluate G in topological order. Each opaque gate's index and arguments are then determined by y and by the outputs of earlier opaque gates. Its output is a constant or a literal χ_v or ¬χ_v, where v is the vertex of clause j, because the forbidden pattern of clause j is one of two patterns, selected by χ_v. So for fixed y, G(y,·) is a decision tree of depth at most g on χ, where g is the number of opaque gates. G's reply, ∃y G(y,χ), is therefore a DNF whose terms (the accepting paths) have width at most g. This covers nested opaque gates, whose pins are outputs of other opaque gates.

Run the following adversary. It keeps a partial assignment P to χ, initially empty.
- On a query G with g gates, if some term is consistent with P, reply YES and add that term's at most g literals to P.
- Otherwise every term contradicts P, so G is unsatisfiable on every completion of P: reply NO.

Compile reads reveal σ only, which does not depend on χ. After the run, |P| ≤ Σ_i g_i, and every reply is consistent with every completion of P. If Σ_i g_i < |V|, some χ_v is free. Then the two completions that differ only at v give opposite parities, hence opposite β, and D outputs the same bit on both: a contradiction.

Each opaque gate costs at least r = ⌈log₂K⌉ bits (an r-bit literal, or r pins of at least one bit each), so |G_i| ≥ r·g_i. For the charge: when a ≤ 0, |G_i|·log^a|G_i| ≥ |G_i|·log^a S′ with S′ = Σ_i |G_i|, and x·log^a x is increasing. ∎

**Corollary (one round of the existential-block step, in the model).** Let M = ε·T·log T and a = 0.
- **Only if.** If ε·log T does not tend to 0, then no 𝔅₁-procedure that works on all files decides β in o(T) steps (Theorem BB on Tseitin structures).
- **If.** If ε·log T → 0, the one-query procedure decides β in o(T) steps on every file with K·log K = O(M), in particular on every file without repeated clauses. On files with Θ(M) repeated short clauses it needs ε·log²T → 0, and in 𝔅₀ that is forced.
- With a word-linear solver (a = −1), the lower bound would move to M = o(s log s), the length the diagonal-only criterion asks for.

So the one logarithm between the criterion's target o(s log s) and what black-box proofs give is exactly the factor between the bit-linear time that H_SAT guarantees and word-linear solver time. It does not depend on b.

**The natural guess fails.** One might expect that no o(T) procedure exists unless ε·log^b T → 0. This fails for every b > 2 on all files. Take ε = 1/log^c T with 2 < c < b. Then ε·log^b T → ∞, yet the one-query procedure costs O(K log K) ≤ O(M log M) = O(T/log^{c−2} T) = o(T) on every file. For 1 < b ≤ 2 it fails on files without repeated clauses: take ε = 1/log^c T with 1 < c < b, and the cost is O(M) = o(T). Over all files in 𝔅₀, the form with b = 2 is correct.

At ε = 1/log T exactly, M = T. The one-query procedure then costs Θ(T) on files without repeated clauses and up to Θ(T log T) on files with them, and Theorem BB gives a lower bound of order T. Part 2 of the checks puts its constant at about 0.027·M for these structures at K = 8·10⁵.

**Scope.** 𝔅₁ allows the indexer inside queries, but it does not allow compiling the solver's run. A proof that compiles the solver's run, as the V route does, is outside the theorem.

## 3. Proposition D: the direct route outside the model

**Packed access.** A compile has packed access if, after a setup of o(T) steps, any aligned w-bit word of F_x is returned in O(1) steps.

The journal proves packed access for two compiles:
- its usual compile, in a fixed-width binary CNF list (the packed-band note's "Packed access to the reduction", quoted in the alternation note as "constant-time packed reads after polylogarithmic setup");
- the trivial native reduction of the native band note.

Packed access is not part of the compiler criterion, whose hypothesis is a bit indexer of polylogarithmic time. For the hypothetical compile C_J it is an additional assumption. [Packed band transfer](packed-band-transfer.md#a-virtual-formula-for-a-bounded-computation) · [Alternation criterion](alternating-native-speedup.md) · [Native band](native-unary-clock-band.md)

**Proposition D.** Let 0 ≤ θ ≤ 1. If C_J(M) holds with packed access and M = o(T·log^θ T), then SAT ∉ DTIME_RAM[O(N/log^θ N)].

*Proof.* Suppose a fixed RAM A decides SAT in at most c·N/log^θ N steps. On input x, the procedure:
1. obtains M from the indexer, in polylog time;
2. writes F_x word by word, in O(M/w) + o(T) steps;
3. runs A on F_x and outputs its verdict.

Step 3 costs c·M/log^θ M. If M ≤ √T this is trivially o(T). Otherwise log M ≥ (1/2)·log T, so M/log^θ M ≤ 2^θ·o(T·log^θ T)/log^θ T = o(T). The total is o(T) = o(n²) on every input, and the procedure decides J. That contradicts the diagonal: no fixed deterministic program running in fewer than n² steps decides J on the long extensions of its own prefix. Widths are handled as in the alternation note ("slightly wider words and sparse addresses are handled as above"); that step is not re-derived here. ∎

**Consequences.**
- **θ = 0.** C_J(o(s)) implies ¬H_SAT under packed access, or merely under bit access in O(1) time after o(T) setup, since writing the M bits then costs O(M). Packed access is needed only for θ > 0, where the write cost must be M/w. This route uses one solver call and no compile of V. For packed compilers it improves the diagonal-only threshold o(s/log² s) of the round-three record.
- **The round-three class of routes.** That class consists of steps that pass through the short witness (deterministic to nondeterministic) and steps back (nondeterministic to deterministic). It omits the direct deterministic step "write F_x, run A". So the threshold o(s/log² s), forced within that class, is not a bound on diagonal-only routes in general; with packed access the direct step alone reaches o(s).
- **Polylogarithmic indexers.** With an indexer that reads a bit in time τ(T), the same route gives o(s/τ(s)). The V route's o(s/log^{b−1} s) remains the better bound when τ grows faster than log^{b−1}; for indexers slower than log² s per bit, the V route's o(s/log² s) is the best threshold known.
- **θ = 1.** C_J(o(s log s)) with packed access implies SAT ∉ DTIME_RAM[O(N/log N)]. As far as the journal records, this conclusion is not known unconditionally: its unconditional RAM bounds for SAT are of order N/log N, matched by O(N/log N) algorithms on their families. So a packed compile at the criterion's target length would already imply a word-superlinear SAT bound, by a one-line argument. No such compile is known, and the implication is not progress on the bound. What the diagonal-only criterion needs beyond that is one logarithm in the conclusion: ¬H_SAT instead of SAT ∉ DTIME[O(N/log N)].
- **Exponent form.** Write β for the compile-length exponent (M = O(s log^β s)) and a for the SAT exponent (time O(N log^a N)). The direct route proves the diagonal-only criterion for β + a ≤ 0 (strictly, the little-o version at β + a = 0), with a ≥ −1, so β ≤ 1 and the write cost M/w is o(s). The journal's criterion for the native language U is stated for a, β ≥ 0 and holds for β + a < 1. The gap is one in the exponent sum.
- **The V route does not beat the direct route for packed compilers.** The V route certifies o(s/log^{b−1} s). A compile of V that keeps one occurring variable per guessed bit has b ≥ 1, because h occurring variables cost Ω(h log h) bits. A compile with b < 1 leaves o(h) variables; by the round-two variable count it would then decide its source in deterministic time 2^{o(h)}, which is excluded only under a hypothesis that the source's succinct class needs more time. So, among the routes analysed so far, none passes o(s): black-box routes (Theorem BB), the direct route (Proposition D), V routes that keep the witness, and generic V routes under that hypothesis.

[Round-two record](parallel-proof-attempts-of-27-november-and-why-each-stopped.md)

## 4. Proposition C: the compile exponent

Recall the accounting of the usual compile in the packed-band note: O(HL) Beneš switches on O(L)-bit records, plus O(L²) gates per step, with O(L)-bit names, give O(HL³) bits. With fast multiplication circuits the local part is L^{1+o(1)} per step, and routing dominates.

**C(i). Switching-network compiles: b = 3 exactly.**
- **The class.** A compile is *switching-type* if its memory check routes the access records through a fixed network of S binary switches whose settings are existential variables. Each switch passes two records of at least L bits, and each routed bit has its own clause, as in the Beneš layer, with a multiplexer per bit.
- **The source.** Take the program that guesses h words a_1, …, a_h and stores at address a_t at step t.
- **Claim.** Every complete switching-type compile of this program has S ≥ log₂(h!).

*Proof.* For each permutation π of [h], the run with a_t = π(t) has distinct addresses. Its records have a unique sorted order, and the sorted-order check forces the network to realize exactly that order. Distinct π need distinct permutations of the write records, hence distinct switch settings. So 2^S ≥ h!. ∎

There are then at least L·log₂(h!) distinct clauses. By the distinct-clause count of the round-two record, a proper file with c distinct clauses has M ≥ (8/log₂10 − o(1))·c·log₂M. Hence M = Ω(h·log h·L·log h) = Ω(h·L³) for L = Θ(log h). The Beneš network attains this with S = h·log₂h − h/2 (ratio to log₂ h! of 1.05 at h = 2^20, Part 3).

So guessed switch settings do **not** escape: classical counting gives c_route = 1, stronger than anything the routing lemma gives (σ, or 1/2 in fields without ports). An escape must give up switching networks altogether, not merely guess the settings. [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)

**C(ii). Exact compiles: 2 + σ_k ≤ b ≤ 3.**
- **The class.** A compile is *exact* if it is oblivious and unambiguous. Oblivious: F_x = Φ_n ∧ Pins(x), with x entering only through pin clauses. Unambiguous: for a deterministic source, F_x has one model if the source accepts x and none otherwise.

*Lower bound.* Turn Φ_n into a tensor network over a finite field k:
- each distinct clause becomes a 0/1 tensor of arity 3 (duplicates are idempotent and are dropped);
- each variable becomes a copy tree;
- each input variable keeps one open leg.

The contraction at input x counts the models of F_x, which is the source's decision. Its volume is at most 4·c_distinct + O(n). Apply this to the linear-time direct-address program for D_w (T = Θ(n/w) steps). Using vol_k(D_w) > n·w^{σ_k} (the list theorem, as the simulation note records it) and the distinct-clause count:

M ≥ Ω((n·w^{σ_k} − O(n))·log n) = Ω(T·(log T)^{2+σ_k}).

On this source every oblivious compile already has b ≥ 2: its n = Θ(T log T) pinned input variables cost Ω(n log n) = Ω(T log² T) bits by the occurring-variable count. Exactness adds the factor (log T)^{σ_k}.

*Upper bound.* The AKS-based exact compile has O(T log²T) gates, so O(T log³T) bits.

So 2 + σ_k ≤ b ≤ 3. This holds for exact compiles, not for the ambiguous routing-type ones. The lower bound is a worst case over source programs, measured on runs with payload about T·w bits. It is not shown for the verifier instances of the V route, whose payload is short. [Exact networks](simulating-a-ram-step-by-exact-networks.md)

**C(iii). General satisfiability-preserving compiles.** The only general floor is the name count: b ≥ 1 for compiles with at least h occurring variables. A better floor would be a superlinear lower bound for nondeterministic circuits, which nobody has. Robson's and Cook's reductions were not consulted. If either gave h·log²h bits for this instruction set (b = 2), the V route's threshold would become o(s/log s). That is still below Proposition D's o(s) for packed compilers.

## 5. Checks

`diagonal_compile_barrier_checks.py` runs in about 3 s:
- **Part 1** checks the 𝔅₀ form of the adversary: every single sign change of an unsatisfiable Tseitin file makes it satisfiable, so every clause must be referenced.
- **Part 1b** checks the parity fact used in Theorem BB.
- **Part 2** gives the constants: the parity bound is about 0.027·M with ASCII names.
- **Part 3** compares Beneš switch counts with the counting floor.
- **Part 4** tabulates the route exponents, log₂(time/T) at ε = (log₂T)^{−θ}, for the direct route and for V routes with b = 3, 2 and 2.5.
- **Part 5** is a randomized check of the adversary in Theorem BB's proof. On 20,000 random query sequences of DNFs with total width below n = 8, every reply equals the query's value on every completion of P, and the parity is never determined.

```
Part 1: Tseitin structures (odd total charge), brute force
  K4        vertices= 4 vars= 6 clauses K=16 UNSAT=True every-deletion-SAT=True sign-changes SAT=112/112
  prism3    vertices= 6 vars= 9 clauses K=24 UNSAT=True every-deletion-SAT=True sign-changes SAT=168/168
  Q3        vertices= 8 vars=12 clauses K=32 UNSAT=True every-deletion-SAT=True sign-changes SAT=224/224
  Petersen  vertices=10 vars=15 clauses K=40 UNSAT=True every-deletion-SAT=True sign-changes SAT=280/280
Part 1b: hidden charges; SAT <=> charges have even parity, all charge vectors
  K4        charge vectors=   16 SAT==even-parity on 16/16
  Petersen  charge vectors= 1024 SAT==even-parity on 1024/1024
Part 2: minimum reference cost sum_{j<=K} floor(log2 j) vs ASCII DIMACS bits M
  m=100000 K= 800000 M= 149689440 refs>= 14151445 refs/M=0.0945 log2(K!)-K=13733567 |V|*ceil(log2 K)=4000000 ratio=0.0267
Part 3: Benes switches h*log2(h) - h/2 vs counting floor log2(h!)
  h=2^20 benes=  20447232 log2(h!)=  19458755.9 ratio=1.0508
Part 4: log2(time/T) at eps = (log2 T)^(-theta); negative and decreasing = o(T)
  log2T   theta | direct(a=0) | V b=3 | V b=2 | V b=2.5
  2^20   1.0  |      0.0    |  40.0 |  20.0 |   30.0
  2^20   1.5  |    -10.0    |  30.0 |  10.0 |   20.0
Part 5: parity adversary, n=8, trials=20000: inconsistent replies=0, parity determined=0
```

**Independent checks.** `diagonal_compile_barrier_independent_check.py` was written during review. Part A evaluates random 𝔅₁-style queries on the Tseitin structure of K4 with nested opaque gates and computed indices: no reply function needs certificates wider than the number g of opaque gates, and 152 of the 3,000 queries have certificates of width at least 2. Part B is the repeated-clause family in 𝔅₀, every clause on the scope (1,2,3). It prints the forced query length against M, and the cost at M = T/log₂T:

```
A: nested opaque gates on K4 Tseitin, trials=3000: 1-certificate > g in 0 queries; queries with certificate width >= 2: 152
   2^10             77928                 10180     0.1306
   2^30       81604378776           32212254540     0.3947
   log2 T= 20: cost/T = 0.0062
   log2 T= 80: cost/T = 0.0111
```

The rows give K, M in bits, the forced length (K − 6)·⌈log₂K⌉ and its ratio to M. These are finite checks of the ingredients. The theorems are the manuscript proofs above.

## 6. The three standard tests

No lower bound for SAT is claimed. The tests apply to the barrier and to Proposition D.
- **(a) Is there a fast globally correct solver on the hard family?** Yes. With visible signs, Tseitin files are decided in linear time by a parity computation. The barrier binds only procedures that never interpret clauses: it is a statement about black-box proofs, not about SAT.
- **(b) Does the same argument give the same bound for 2-SAT?** Yes. Hidden signs on any family whose satisfiability is the parity of hidden local bits give the same Θ(M), and 2-CNF Tseitin-type parity systems exist on cycles. So the barrier uses nothing specific to SAT; as a barrier, it is not meant to.
- **(c) The oracle of the relativized-clock note (p = 1).**
  - Theorem BB is a statement about a model, and that oracle does not touch it.
  - Proposition D is an implication. In the p = 1 world SAT has O(n) oracle algorithms. If the deterministic diagonal relativizes, as the usual argument suggests (not checked for this RAM), then relative to that oracle no compile C_J(o(s)) with packed access exists. That is consistent with Proposition D, not a refutation of it.
  - The step of C(ii) from a RAM run to a network needs O(w) bits per instruction and fails for a Θ(n log n)-bit query.

## 7. Exact obstruction and next step

**The precise obstruction.** The diagonal-only criterion at o(s log s) cannot be proved by a black-box use of the compiler, even with an indexer usable inside queries, together with a black-box use of the solver. Such proofs stop at o(s), and the lost factor is the word width (Theorem BB). The direct route attains o(s) for packed compilers (Proposition D). Every white-box route analysed so far compiles the solver's run, and that compile costs b ≥ 1 logarithms (Proposition C and the name count), which again caps the route at o(s).

So a proof at o(s log s) must interpret the compiled formula or the solver at a cost below one logarithm per solver step. By Proposition D at θ = 1, the same hypothesis already gives SAT ∉ DTIME[O(N/log N)]. What is missing is exactly the step from that conclusion to ¬H_SAT, one logarithm.

**Next lemmas:**
1. **A barrier for routes that compile the solver's run.** Allow Σ₂-shaped queries (the solver's run inside a query) at price h·log^b h, and ask for the threshold o(s/log^{b−1}s) and no better.

   The Tseitin structures of Theorem BB do **not** work there. Parity of |V| bits has depth-3 circuits of size 2^{O(√|V|)} with bottom fan-in O(√|V|). Concretely, one Σ₂ query does it: guess √|V| block parities p_i with even total; universally range over a block i and a pattern of parity ≠ p_i; check, with √|V| opaque gates, that the block's charges differ from the pattern. One opaque gate reads one charge: give it the i-th odd pattern as arguments and it outputs χ_v. This query has O(√K·polylog K) bits; the polylogarithm covers the index arithmetic and the multiplexer that selects p_i.

   So a Σ₂ barrier needs structures whose verdict function has no small depth-3 circuits. For explicit structures that is the depth-3 lower-bound frontier, where the best known bounds are 2^{Θ(√n)} (not verified at source). A black-box model may use non-explicit structures, and whether counting supplies one realizable as [F(σ,χ) ∈ SAT] is the first question.
2. **A non-switching, possibly ambiguous compile with b < 3.** For example, check Robson's reduction at source. It moves only the V route, and only for non-packed compilers.
3. **Proposition D at θ = 1 as a target.** "C_J(o(s log s)) with packed access ⇒ SAT ∉ DTIME[O(N/log N)]" is proved here. Its conclusion is open and is weaker than ¬H_SAT. Whether a packed J-compiler of length o(s log s) is plausible at all is the question the round-two counting bears on: under a succinct-class hypothesis it is excluded for compilers defined on all sources, but not for J alone.

## 8. What is not proved

- No SAT lower bound, and no barrier against proofs that compile the solver's run or use clause semantics. Theorem BB is a statement about the model 𝔅₁, whose hidden-sign convention is what makes any lower bound provable there.
- The diagonal-only criterion at o(s log s) is neither proved nor refuted.
- The worst-case cost in 𝔅₁ over files with repeated clauses is not determined; membership circuits of Lupanov type might bring it to O(M), which was not settled during review.
- Proposition D relies on the journal's width and sparse-address bookkeeping, which is not re-derived here. It needs packed access, which C_J with the criterion's indexer (polylogarithmic time per bit) does not include.
- C(i) is proved only for the class as defined: binary switches, existential settings, at least one clause per routed record bit. C(ii) rests on the list theorem of the 24 November preprint, as the simulation note records it, and on the distinct-clause count of the round-two record, which is unrefereed but checked at finite size. C(ii)'s lower bound is a worst case over sources and is not shown for the verifier instances of the V route.
- That Proposition D is new to the journal rests on searches of the notes, here and during review, not on a full read.
- Robson's reduction and Cook's (1988) were not consulted; for Robson only the bibliographic record was seen. Whether either gives a compile with b < 3 for this instruction set is unknown here. Such a compile would lie outside the switching class of C(i), and it would not affect Theorem BB or Proposition D. [Robson, TCS 82 (1991) 141–149](https://doi.org/10.1016/0304-3975%2891%2990177-4)

## Reproducing the checks

Run from `audits/`; neither script takes arguments or writes files.

```
python3 diagonal_compile_barrier_checks.py
python3 diagonal_compile_barrier_independent_check.py
```

The first takes about 3 seconds and needs numpy; the second takes under a second. [Checks](../audits/diagonal_compile_barrier_checks.py) · [Independent checks](../audits/diagonal_compile_barrier_independent_check.py)
