# The frame game on an overwrite ladder touching C cells is worth at least C − 1

Every black pebbling of the frame DAG of an overwrite-ladder run touching C cells holds at least C pebbles at some time, and C + 1 pebbles always suffice. So the frame game of the round-three truth-claim entry has value at least C − 1 on every such run, which on the round-robin ladder is ⌈T/2⌉ − 1. This settles that entry's restated conjecture for the frame game in its existential form, witnessed by ladders touching a constant fraction of T cells. For ladders touching o(T) cells, such as Θ(T/log T), the frame value itself is o(T), so the conjecture fails for them in the frame game ([frame-game upper bound](frame-game-upper-bound-on-overwrite-ladders.md)). Black pebbling cannot give more, because C + 1 pebbles suffice. By Chan's theorem, read at source, the reversible pebbling price is the game value plus one; this was checked by exhaustive search on the 64 instances of the round-three table with T ≤ 9. So a bound of T − o(T) needs an argument specific to reversible pebbling. A partial bound for the node game is included. The bounds were checked during review with independent solvers. They are bounds inside one move class, not time bounds; the linear, quadratic and cubic questions remain open.

## Setting

**Runs.** A run has T steps. On the *overwrite ladder* every step τ is a load-then-store at a data-dependent address a_τ: it loads cell a_τ and stores a new value there. A ladder run is given by its address sequence a_1, …, a_T, and C is the number of distinct cells in it. The *round-robin ladder* has a_τ = (τ − 1) mod M with M = ⌈T/2⌉, so C = M; the scripts call it `ladder_rr`. C, or C(T) as a function of T, always means this cell count; C(σ, a), with two arguments, is a node of the frame DAG.

**Frame DAG** ([truth_claim_frame_game.py](../audits/truth_claim_frame_game.py)).
- The nodes are S_τ, the state after step τ ≥ 1, and C(σ, a), the content of cell a after step σ, for a step σ that does not write a.
- version(a, σ) is S_σ if step σ writes a (on the ladder, if a_σ = a) and C(σ, a) otherwise. S_0 and version(a, 0) are known and are not nodes.
- On the ladder the predecessors are S_τ ← S_{τ−1}, version(a_τ, τ−1) and C(σ, a) ← version(a, σ−1), S_{σ−1}.
- In runs with plain loads and stores, S_τ needs version(a_τ, τ−1) only if step τ loads, and C(σ, a) needs S_{σ−1} only if step σ stores at a data-dependent address. The other families of the round-three table and the initialised-memory runs below use these rules.
- Only the ancestor cone of S_T is kept. By these rules every edge of a ladder's frame DAG goes from time σ − 1 to time σ; the cone check confirms it for `ladder_rr` at T = 2, …, 14.

**Frame game.** This is the Dymond–Tompa game on the frame DAG, with one placement per move.
- The challenged node starts at S_T, which is not pebbled.
- In each move the prover places a pebble on a node v, at cost 1, and the challenger either stays or moves to v.
- A position whose challenged node has all its predecessors pebbled is worth 0. The *value* is the least number of placements that the prover can guarantee on every branch.
- So every claim is an atomic truth claim, checked against its predecessors in one step, and the prover pays per claim.
- A lower bound on the frame value also holds for every game whose prover strategies are frame-game strategies. By the round-three entry the interval game of the standing-opponent suite is one of them, up to one folded claim.

**The restated conjecture.** The truth-claim entry of [round three](parallel-proof-attempts-of-27-november-round-three.md) left open whether truth-claim games can beat walking the state chain on the overwrite ladder. Its conjecture, restated with the cell count, reads: there are c > 0 and address sequences such that, for every T, the overwrite ladder with C(T) cells has frame-game value at least c·T, and likewise for every truth-claim game with one-step checks.
- In the frame game the conjecture needs liminf C(T)/T > 0: a cone-restricted bisection wins within C·log₂(T/C) + O(C) placements ([frame-game upper bound](frame-game-upper-bound-on-overwrite-ladders.md)). The earlier bound, from the bisection interval game of the [standing-opponent suite](../audits/standing_opponent_suite.py), which costs at most (C + 1)⌈log₂ T⌉ claims on a run touching C cells and is a strategy in the frame game, gave only C(T) = Ω(T/log T); it is quoted from the round-three entry and was not rechecked here.
- Walking the state chain costs at most T − 1 + ⌈log₂ T⌉. The prover places S_1, …, S_{T−1} in order. Wherever the challenger moves, every earlier state is pebbled, so what remains is one frame chain of at most T − 1 nodes below a challenged state, and bisection settles a path of m nodes in ⌈log₂ m⌉ placements.

**Black and reversible pebbling.**
- *Black.* Place v when all predecessors of v are pebbled, remove any pebble at any time, and reach a configuration containing the sink. Black(G) is the least possible maximum configuration size.
- *Reversible* (Bennett; Chan's Definition 3.3). Place or remove v only when all predecessors of v are pebbled, and finish with exactly {sink}. Rev(G) is the least possible maximum configuration size. RevVisit(G), the same number with any configuration containing the sink as the goal, is also reported.

## 1. Results

- **Theorem.** Take an overwrite-ladder run touching C distinct cells. Every black pebbling of its frame DAG has at least C pebbles on the board at some time (Section 3). Hence the frame value is at least C − 1 (Lemma 1, Section 2).
  - On the round-robin ladder the value is at least max(1, ⌈T/2⌉ − 1) for every T ≥ 2, since the prover must place S_{T−1}. That is at least T/4 at every T ≥ 2, and (1/2 − o(1))·T asymptotically.
  - On ladders touching C(T) ≥ c′·T cells the value is at least (c′ − o(1))·T. This is the restated conjecture for the frame game, in its existential form.
  - On ladders touching o(T) cells, such as Θ(T/log T), the bound C − 1 is o(T), and the frame value itself is o(T) ([frame-game upper bound](frame-game-upper-bound-on-overwrite-ladders.md)), so the conjecture fails for them in the frame game.
  - The bound does not rest on loads of never-stored cells. Started at any time σ0, the same proof gives Black ≥ the number of distinct cells accessed after σ0 (Lemma 2′).
- **The black-pebbling route is exhausted.** Black ≤ C + 1 on every ladder run (Section 4), so black pebbling can never show more than value ≥ C. The exact black number is C + 1 on every ladder sequence checked.
- **The dictionary.** By Chan's Theorem 1 the reversible pebbling price is the frame value plus one (Section 5). On the round-robin ladder at T ≤ 10 the reversible numbers are about T, not T/2. A bound of T − o(T) therefore needs an argument specific to reversible pebbling, which is not given here.
- **Node game.** On every ladder run the value of the round-three node game is at least (T − 1) − max(P* − 1, 0), where P* is the largest last-writer index of any load (Section 6). It is exactly T − 1 when all addresses are distinct, and at least ⌈T/2⌉ on the round-robin ladder.
- So the frame value of every ladder run lies between C − 1 and min(f_C(T), T − 1 + ⌈log₂ T⌉), where f_C(T) ≤ C·log₂(T/C) + 2C + 2log₂C + 2 is the cone-restricted bisection bound of the [frame-game upper bound](frame-game-upper-bound-on-overwrite-ladders.md). Also f_C(T) ≤ C⌈log₂ T⌉, and f_C(T) can exceed the walk bound, for example f_9(9) = 15 > 12.

## 2. From the frame game to black pebbling

**Lemma 1.** If the prover wins the frame game from the sink within k placements on every branch, then Black(G) ≤ k + 1.

*Proof.* Write a position as (c, Q), where c is challenged and Q is the set of pebbled vertices other than c, and let anc(c) be the set of proper ancestors of c. After a placement of v the stay branch is (c, Q ∪ {v}) and the move branch is (v, Q ∪ {c}), because the old challenged vertex stays pebbled. The root sink is not pebbled; since the sink is in no anc(v), this changes nothing below.

Claim, by induction on k: if (c, Q) is won within k placements, then from any board B ⊇ Q ∩ anc(c) one can place c without removing any pebble of B, using at most k + 1 extra pebbles at any time, and end with B ∪ {c}.
- *If the predecessors of c lie in Q*, as they must when k = 0, they lie in Q ∩ anc(c) ⊆ B, so place c.
- *Otherwise k > 0* and the strategy places some v. Both branches are won within k − 1.
  - If v ∉ anc(c) or v ∈ B, then (Q ∪ {v}) ∩ anc(c) ⊆ B. Place c by the stay branch, with at most k extra.
  - Otherwise v ∈ anc(c) \ B. Then anc(v) ⊆ anc(c) and c ∉ anc(v), so (Q ∪ {c}) ∩ anc(v) = Q ∩ anc(v) ⊆ B.
    - Place v by the move branch, with at most k extra. The board is now B ∪ {v} ⊇ (Q ∪ {v}) ∩ anc(c).
    - Place c by the stay branch, with at most 1 + k extra.
    - Remove v, which is not in B.
- At the root (sink, ∅) with B = ∅, this is a black pebbling with at most k + 1 pebbles. ∎

This is the standard simulation of alternating time in deterministic space, and Chan's Remark 1.3 states the inequality. Restricting the hypothesis to Q ∩ anc(c) matters. When v is a descendant of c, the move-branch strategy may use c's pebble, which is not yet on the board. In this form the proof was checked line by line during review.

## 3. The lower bound

**Lemma 2 (spine runs).** Fix a ladder run.
- Let τ_1 = 1 < τ_2 < … < τ_C be the times at which a cell is accessed for the first time, and let c_j be that cell.
- Let I_j = {C(μ, c_j) : 1 ≤ μ ≤ τ_j − 1} ∪ {S_{τ_j}}. This is the chain that carries the initial value of c_j, plus the state that reads it.
  - Since c_j is not written before τ_j, version(c_j, μ) = C(μ, c_j) for μ < τ_j.
  - C(1, c_j) is a source, and C(μ, c_j) ← C(μ − 1, c_j), S_{μ−1}.
  - The sets I_j lie in the cone of S_T and are pairwise disjoint.
- Fix a black pebbling P_0 = ∅, P_1, …, and call θ_1 ≤ θ_2 ≤ … ≤ θ_r a *spine run up to r* if S_μ ∈ P_{θ_μ} for μ = 1, …, r.

*Claim R(j):* for every spine run up to τ_j there is a time i ∈ [θ_1, θ_{τ_j}] with |P_i ∩ (I_1 ∪ … ∪ I_j)| ≥ j.

*Proof by induction on j.* R(1) holds because S_1 ∈ P_{θ_1} and I_1 = {S_1}.

For j ≥ 2, let p be the last move at or before θ_{τ_j} that places S_{τ_j}. It exists because P_0 = ∅, and S_{τ_j} ∈ P_i for all i ∈ [p, θ_{τ_j}].
- **Case 1: p ≤ θ_1.** I_j is occupied throughout [θ_1, θ_{τ_j}]. R(j − 1), applied to the prefix θ_1, …, θ_{τ_{j−1}}, gives a time i in [θ_1, θ_{τ_{j−1}}] with j − 1 pebbles on I_1 ∪ … ∪ I_{j−1}, and I_j adds one more.
- **Case 2: p > θ_1.** At move p, C(τ_j − 1, c_j) and S_{τ_j − 1} are pebbled. Build a witness chain backwards.
  - Set v_{τ_j} = p. For μ = τ_j − 1 down to 1, let v_μ be the last move before v_{μ+1} that places C(μ, c_j).
  - Then C(μ, c_j) ∈ P_i on [v_μ, v_{μ+1}], and S_{μ−1} ∈ P_{v_μ} for μ ≥ 2.
  - So I_j is occupied on [v_1, p] and, through S_{τ_j}, on [p, θ_{τ_j}].
  - **Case 2b: v_1 ≤ θ_1.** I_j is occupied throughout [θ_1, θ_{τ_j}]. Conclude as in Case 1.
  - **Case 2a: v_1 > θ_1.** Then (v_2, v_3, …, v_{τ_j − 1}, p) is a spine run up to τ_j − 1 ≥ τ_{j−1}, because S_{μ−1} ∈ P_{v_μ} and S_{τ_j − 1} ∈ P_p. It lies inside [v_2, p] ⊆ [θ_1, θ_{τ_j}]. R(j − 1), applied to its prefix, gives a time in [v_2, p] with j − 1 pebbles on I_1 ∪ … ∪ I_{j−1}, while the chain holds a pebble on I_j.

In every case the count is at least j. ∎

**Corollary 3.** Every black pebbling contains a spine run up to T. Let θ_T be the first placement of S_T and, going down, let θ_μ be the last placement of S_{μ+1} at or before θ_{μ+1}; S_μ is a predecessor of S_{μ+1}, so S_μ ∈ P_{θ_μ}. Applying R(C) to its prefix up to τ_C gives **Black(G) ≥ C**, and Lemma 1 gives **frame value ≥ C − 1**. On the round-robin ladder every cell is accessed, so the value is at least ⌈T/2⌉ − 1.

**Lemma 2′ (any window).** Let σ0 ≥ 1, and suppose every step in σ0 + 1, …, T is a load-then-store at a data-dependent address. Then Black is at least the number of distinct cells accessed in steps σ0 + 1, …, T.

*Proof.* Repeat Lemma 2 with these changes.
- τ_j is the first access of c_j after σ0.
- I_j = {C(μ, c_j) : σ0 + 1 ≤ μ ≤ τ_j − 1} ∪ {S_{τ_j}}. These are frame nodes, because c_j is not accessed in (σ0, τ_j).
- A spine run starts at S_{σ0}, and every black pebbling contains a spine run from σ0 to T.
- The witness chain stops at C(σ0 + 1, c_j), whose placement needs S_{σ0}.
- In Case 2a, (v_{σ0+1}, …, v_{τ_j − 1}, p) is a spine run from σ0 to τ_j − 1. In Case 2b, v_{σ0+1} ≤ θ_{σ0}.
- The base case j = 1 uses S_{τ_1} ∈ P_{θ_{τ_1}}. ∎

So the bound does not depend on loads of never-stored cells. On the round-robin ladder any window of M consecutive steps already gives Black ≥ M. A run that first stores to cells 0, …, M − 1 at public addresses and then runs the round-robin ladder for one or two rounds never loads a never-stored cell. Its black number is M + 1 for M = 2, …, 5 in both cases. This check uses the note's own pebbling solver; the independent solvers of the review covered pure ladders only, and Lemma 2′ was checked by hand.

**Scope.** Lemma 2 needs every step of a frame chain to depend on the previous state. That holds whenever every step stores at a data-dependent address. For such runs the same proof gives Black ≥ the number of loads of a cell never stored before, which on the ladder equals C. This extension was checked on paper during review, not numerically. In runs with loads that do not store, a frame-chain step need not depend on the state, and Case 2a breaks.

## 4. The upper bound C + 1

Column σ is S_σ plus the nodes C(σ, a), a ≠ a_σ, of cells accessed after σ. S_σ is itself the version of the cell written at σ, so the column has at most C nodes. Column 1 consists of sources, so place it. Then go from column σ to column σ + 1 in this order:
1. For each cell a ∉ {a_σ, a_{σ+1}} with C(σ + 1, a) in the cone, place C(σ + 1, a), then remove C(σ, a).
2. Place S_{σ+1}. Then remove C(σ, a_{σ+1}) if a_{σ+1} ≠ a_σ.
3. Place C(σ + 1, a_σ) if it is in the cone.
4. Remove S_σ.

Every move keeps at most |column σ| + 1 ≤ C + 1 pebbles, so **Black ≤ C + 1** on every ladder run. The order matters: placing C(σ + 1, a_σ) before step 1 would reach C + 2. During review the order was checked by hand in both cases, a_{σ+1} = a_σ and a_{σ+1} ≠ a_σ.

By Lemma 1 the value is at least Black − 1, and Black − 1 ≤ C. So black pebbling can never show more than value ≥ C, which on the round-robin ladder is about half the walk bound.

## 5. Chan's theorem and the reversible numbers

**Source.** S. M. Chan, *Just a Pebble Game*, ECCC TR13-042 (CCC 2013), https://eccc.weizmann.ac.il/report/2013/042/download (41 pages, sha256 5dd22a5688e235e3a087af78bd9bad818b70400e98f2e3c225fd48a58c3dd076).
- Theorem 1 opens: "The Dymond–Tompa pebble game, the Raz–McKenzie pebble game, and the reversible pebble game of Bennett have the same pebble cost." For a DAG with a unique sink, h time in the Dymond–Tompa game is equivalent to h pebbles in the reversible game.
- Footnote 5: "In the reversible pebble game, it is required to pebble the sink vertex and to remove pebbles on all other vertices."
- Definitions 3.4 and 3.5 fix the convention. The initial configuration is ⟨⟨{τ}, ⊥, τ⟩⟩, where τ is Chan's sink, so the sink starts pebbled; a leaf has value 1, and each Challenger node adds 1.
- So Chan's Dymond–Tompa time is the frame value plus one, and the predicted identity is **Rev = frame value + 1**. On the two-vertex DAG the frame value is 1 and Rev = 2.
- Remark 1.3 states that the Dymond–Tompa cost is at least the black pebble cost, which is the inequality of Lemma 1.
- The statements and definitions were read at source and rechecked during review. The proofs of Lemmas 3.22–3.25, which carry the equivalence of the Raz–McKenzie and reversible games, were not read. The lower bound does not use Chan's theorem; only the identification with reversible pebbling does.

**The round-three table.** At each T it has eight instances: the constant reader (one store, then T − 1 loads of the same cell, all at public addresses), the round-robin ladder, two random ladders on ⌈T/2⌉ cells, and four random store-heavy runs of loads and stores at data-dependent addresses, two on 4 cells and two on 6. The seeds are fixed in the comparison script.

**Exhaustive search.** For each budget s = 1, 2, … the pebbling solver searches, breadth first, the whole component of the empty configuration among configurations of size at most s. So a failed budget proves that s pebbles do not suffice. The frame values come from the Dymond–Tompa solver.
- On all 64 instances of the round-three table with T ≤ 9 (eight families, T = 2, …, 9), Rev = frame value + 1.
  - For `ladder_rr` at T = 9, budget 9 fails exhaustively in the table run, which then stops at its state cap. A separate run at budget 10 with a 2^28-entry table succeeds: `exact 10 states 163915511`, in about 50 seconds and 3.4 GB.
- At T = 10 the identity holds exactly on 7 of the 8 instances.
  - For `ladder_rr` the frame value is 9. Complete search finds no win within 8 placements, and a single run at budget 9 with a 2^28-entry table finds one: `win 9 states 34637947`, in about 23 seconds and 4.2 GB.
  - The reversible search there proves only Rev ≥ 10. That is consistent with 9 + 1, but it does not check it.
- During review, independent solvers gave Rev = frame value + 1 on all 277 ladder sequences with T ≤ 6 and any number of cells.

**The round-robin ladder.** At T = 2, …, 9 the frame values are 1, 3, 4, 5, 6, 7, 7, 9, and Rev = 2, 4, 5, 6, 7, 8, 8, 10. At T = 10 the frame value is 9 and Rev ≥ 10. Meanwhile Black = M + 1. So at T ≤ 10 the reversible numbers are about T, while the black numbers stay at C + 1. Nothing beyond T = 10 is computed.

**The first-round triangle.** This is the frame DAG of the ladder with addresses 0, 1, …, L − 1, in which every step reads a cell never written before. Black = L + 1 for L = 2, …, 7, and Rev = 3, 5, 6, 7, 8, 10 there. At L = 8 and 9 both searches stop at the state cap. On the round-robin ladder the cone of S_M is exactly this triangle with L = M, so the first round alone already gives Black ≥ C.

## 6. The node game

**Node game** ([truth_claim_node_game.py](../audits/truth_claim_node_game.py), rule P). Its claims are machine states S_u, with S_0 known.
- For a challenged step c that loads a cell, let p(c) be the last step that wrote that cell, or 0 if none. The state S_c is checked against hard(c), which is S_{c−1} together with S_{p(c)} when p(c) ≥ 1.
- The claim that no step in (p(c), c) stores to that cell is disputed by a range challenge. On the ladder the challenger may name any state in R(c) = {S_{k−1} : p(c) < k < c, k ≥ 2}. If that state is not pebbled, the prover must place it, and the challenge moves there.
- The prover pays 1 per placed state, and the challenger's names are free and unlimited.
- The switch PUB, when on, lets the challenger name only steps that store at a data-dependent address. On ladders its two settings coincide, because every ladder step is such a store.

**Proposition 5.** On every ladder run the node value is at least (T − 1) − max(P* − 1, 0), where P* = max_c p(c).

*Proof.* Let the challenger never move on a placement. When the prover declares c ready, let it name the largest unpebbled state in R(c), or accept if there is none.
- Let Φ(c, P) be the number of unpebbled states among S_1, …, S_{c−1}. Initially Φ = T − 1.
- A placement costs 1 and lowers Φ by at most 1.
- At a naming of S_k, hard(c) is pebbled and every state of R(c) above S_k is pebbled, so S_{k+1}, …, S_{c−1} are all pebbled. The prover's forced placement of S_k costs 1, and the new Φ is the old Φ minus 1.
- The game ends only at a ready node c_f with R(c_f) ∪ hard(c_f) pebbled. There the unpebbled states lie in S_1, …, S_{p(c_f)−1}, so Φ ≤ max(p(c_f) − 1, 0).
- So cost + Φ never decreases, and the cost is at least (T − 1) − max(P* − 1, 0). ∎

**Consequences.**
- If all addresses are distinct, P* = 0 and the value is exactly T − 1. The walk costs at most T − 1: the prover places S_1, …, S_{T−1} in order, and wherever the challenger moves every earlier state is pebbled, so every range challenge names a pebbled state.
- On the round-robin ladder P* = T − M, so the value is at least M = ⌈T/2⌉.
- On 0^{T−k} 1 2 … k with T − k ≥ 2 the bound is only k + 1. At T − k = 1 the sequence is all distinct and the bound is T − 1 = k.
- The worst ladders of the round-three entry reach the walk bound T − 1 for T = 3, …, 8, on sequences with large P* such as 0012030, where the bound gives only 2. So T − O(1) on the worst sequences is not reached.

## 7. Checks

The commands are in the last section; each reproduces the outputs quoted here.
- **The comparison table.** The frame values and Rev − frame value = 1 are as stated in Section 5. The key rows for `ladder_rr` (name T M nodes | frame value | Rev | RevVisit | Rev − frame value | states) are
  ```
  ladder_rr 4 2 7 | 4 | 5 | 4 | 1 | 118
  ladder_rr 6 3 15 | 6 | 7 | 6 | 1 | 14498
  ladder_rr 7 4 22 | 7 | 8 | 7 | 1 | 410134
  ladder_rr 8 4 26 | 7 | 8 | 8 | 1 | 1137424
  ladder_rr 9 5 35 | 9 | >=10 | 9 | - | 93952410
  ladder_rr 10 5 40 | >=9 | >=10 | None | - | 93952410
  ```
  The last two rows are lower bounds set by the state caps. The separate runs at budgets 10 and 9 above settle T = 9 and the frame value at T = 10.
- **The round-robin cone is a triangle.** For T = 2, …, 14 the cone of S_M in the `ladder_rr` DAG is exactly the triangle {(a, μ) : μ ≤ a + 1} with the stated predecessors, S_M is an ancestor of S_T, and the DAG is layered (`ALL OK`).
- **Black − C = 1.** On all 891 ladder sequences with T = 2, …, 7 and at most ⌈T/2⌉ cells, relabelled by first occurrence, there is no violation of Black ≥ C, and Black − C = 1 on every sequence.
- **Round-robin and triangle.** Black = M + 1 on `ladder_rr` for T = 2, …, 9, and the triangle numbers are those of Section 5.
- **Initialised memory.** Black = M + 1 for M = 2, …, 5, with one and with two rounds.
- **Node game.** Proposition 5 has no violation on all ladder sequences with T = 2, …, 7 and at most ⌈T/2⌉ cells, under both settings of PUB. On all-distinct sequences value = bound = T − 1 for T = 2, …, 12. On `ladder_rr` at T = 12 the value is 9 and the bound 6.
- **Independent solvers, written during review from the definitions.** Their frame-DAG builder agrees with the one used above, node for node and edge for edge, on all 891 sequences, and their own minimax of the frame game agrees with the Dymond–Tompa solver on the 176 of them with T ≤ 6.
  - On those 891 sequences and on all 1,154 restricted-growth ladder sequences with T ≤ 7 and any number of cells, Black = C + 1 exactly and Black ≤ frame value + 1.
  - Their own reversible search gives Rev = frame value + 1 on the 176 sequences and on all 277 any-cell sequences with T ≤ 6.

## 8. The three standard tests

- **(a) Fast solver for the hard family.** No time lower bound is claimed. The objects are game values of specific runs inside one move class: atomic state and frame claims with one-step checks, with the prover paying per claim. The run itself is a linear-time computation, so the bound says only that this class of truth-claim games cannot shorten the run below C − 1 claims per branch.
- **(b) 2-SAT.** A 2-SAT solver whose run is an overwrite ladder touching C cells gets exactly the same bound. So this is a statement about the method, never about a language.
- **(c) The oracle of [the relativized clock](relativized-clock.md).** There a query passes a contiguous packed bit string of the RAM and receives one membership bit.
  - The bound here is a combinatorial fact about frame DAGs in which a step has O(1) predecessors. No oracle enters, so it holds relative to that oracle as stated.
  - It says nothing about runs containing such queries. A query step reads a packed string of unbounded length, so it is not a node of this frame model.
  - No conclusion about time follows in either world.

## 9. Exact obstruction and next step

- **Settled.** The restated conjecture for the frame game, in its existential form. The value is at least C − 1 ≥ c·T on ladders with C(T) ≥ c′·T cells, with c = c′ − o(1). The round-robin ladder gives c = 1/2 − o(1), and value ≥ T/4 at every T ≥ 2.
- **Settled negatively for the frame game: the conjecture on ladders touching o(T) cells.**
  - On every ladder touching C ≥ 2 cells, with T ≥ C, the prover wins the frame game within f_C(T) placements. Here f_C(1) = 0 and f_C(L) = min(C, ⌈L/2⌉ + 1) + f_C(⌈L/2⌉), and f_C(T) ≤ C·log₂(T/C) + 2C + 2·log₂C + 2.
  - The strategy is a bisection that cuts only the ancestors of the claim currently challenged ([frame-game upper bound](frame-game-upper-bound-on-overwrite-ladders.md)).
  - So the frame value is o(T) whenever C(T) = o(T). At C = T/log₂T it is at most C·(log₂log₂T + 2) + O(log T).
  - With the lower bound C − 1: a ladder family has frame value at least c·T at every T ≥ 2, for some c > 0, exactly when liminf C(T)/T > 0.
  - This bounds the frame game only. The interval game's prover strategies are frame-game strategies, so the bound does not pass to it. On round-robin ladders (a_τ = (τ − 1) mod C) the interval value is C·⌈log₂T⌉ at the sizes computed with 8C ≤ T ≤ 512, for example 288 against f_32(512) = 164. The node game is not covered either.
- **Open: whether the frame value is Θ(C) or Θ(C·log(T/C)) when C = o(T).** On 28 November a round-six note settled it for round robin: Θ(C·log(T/C)) once T ≥ 8C, while other ladders touching C cells can have V = O(C + log T) ([round-robin ladders](frame-value-on-round-robin-ladders.md)).
  - It lies between C − 1 and C·log₂(T/C) + O(C).
  - For C = 2 the exact values at T ≤ 24 are about 2·log₂T, within 2 of f_2(T) = 2⌈log₂T⌉.
  - For C = 3 and C = 4 they are known only for T ≤ 15 and T ≤ 11.
- **Open: the constant when C = Θ(T).** This bullet uses a corollary noted during review and not refereed.
  - The first term of f_C(T) is at most C, and the i-th at most ⌈T/2^i⌉ + 1. So the frame value is at most C + T/2 + 2⌈log₂T⌉.
  - For C ≤ (1/2 − ε)·T it is therefore at most (1 − ε)·T + O(log T).
  - On the round-robin ladder with M = ⌈T/2⌉ it lies between ⌈T/2⌉ − 1 and T + O(log T). The data at T ≤ 10 suggest about T there. Black pebbling cannot decide it.
- **Next lemma.** Rev of the frame DAG of the round-robin ladder with M = T/2 is at least T − O(log T), or at least (1/2 + ε)·T. It would need a Raz–McKenzie colourer strategy, or equivalently a direct reversible-pebbling lower bound, that uses the second round of reads; the first-round triangle already gives C.
- **Node game.** Proposition 5 is exact on distinct addresses and gives ⌈T/2⌉ on the round-robin ladder. A potential that rewards naming states whose own last writer is early is the next thing to try.
- **Scope.** None of this reaches the SAT bound. On runs touching a constant fraction of T cells, truth-claim games of this kind cannot shorten the run below a constant fraction of its length. Games whose moves are not atomic truth claims are untouched.

## 10. What is not proved

- Chan's equivalence between the Raz–McKenzie and reversible games: only the statements and definitions were read, not the proofs of Lemmas 3.22–3.25. The lower bound does not use it; only the dictionary check does.
- Rev for `ladder_rr` at T ≥ 10: there is only Rev ≥ 10 at T = 10. Nothing was run at T = 11 or 12, so the round-three brackets there are not narrowed.
- Black = C + 1 in general. It is checked at T ≤ 7 only, and the proof gives Black ≥ C. Black ≥ C beyond T = 7 and the extension to all-store runs were not checked numerically.
- A node-game bound of T − O(1) on the worst sequences. Proposition 5 is weaker there.
- Any bound for combined claim languages, or for games in which the challenger asserts values.
- The clause "likewise for every truth-claim game with one-step checks" of the restated conjecture. It follows only for games whose prover strategies are frame-game strategies. The node game is not one of them, since its range challenges are not frame-game moves; for it only Proposition 5 holds.
- The extension of the theorem to runs with loads that do not store.
- An independent check of Lemma 2′ beyond pure ladders. The initialised-memory runs were rerun during review only with the note's own solver.
- The bisection bound (C + 1)⌈log₂ T⌉, which is quoted from the round-three entry.

## Related notes

No other journal note states black or reversible pebbling numbers of frame DAGs. [Pushdown invariant probes](pushdown-invariant-probes.md) treats pebbling formulas as a query search problem on pyramids, and [the mixed-tape pebble frontier](mixed-tape-pebble-frontier.md) treats segregators and bounded-round placement costs on tape-run graphs.

## Reproducing the checks

Run from the audits directory. [frame_dag_solvers.py](../audits/frame_dag_solvers.py) compiles the two solvers, [frame_dag_dymond_tompa_value.cpp](../audits/frame_dag_dymond_tompa_value.cpp) and [frame_dag_black_and_reversible_pebbling.cpp](../audits/frame_dag_black_and_reversible_pebbling.cpp), with $CXX (default c++) into a temporary directory. With no argument each script runs a short default.
```
python3 -I -B frame_dag_reversible_pebbling_versus_frame_value.py 2 7 60 24 20
python3 -I -B frame_dag_reversible_pebbling_versus_frame_value.py 8 9 150 27
python3 -I -B frame_dag_reversible_pebbling_versus_frame_value.py 10 10 100 27
python3 -I -B frame_dag_writer.py ladder_rr 9 | python3 -I -B frame_dag_solvers.py peb rev 10 28 10
python3 -I -B frame_dag_writer.py ladder_rr 10 | python3 -I -B frame_dag_solvers.py dt 9 28 9
python3 -I -B frame_dag_round_robin_cone_check.py
python3 -I -B frame_dag_black_pebbling_at_least_cells_check.py 2 7
python3 -I -B frame_dag_round_robin_black_pebbling.py 2 9 60 26
python3 -I -B frame_dag_first_round_triangle_pebbling.py 1 9 40 25
python3 -I -B frame_dag_initialised_memory_check.py 5
python3 -I -B node_game_last_writer_potential_check.py 2 7
python3 -I -B frame_dag_pebbling_independent_check.py 2 7 6 6
python3 -I -B frame_dag_pebbling_any_cell_count_independent_check.py 2 7 6
```
- The three table runs take about 1, 50 and 80 seconds. The T = 8–9 and T = 10 runs use up to 1.8 GB, and their capped rows reach the state cap well within the time limits.
- The two single-instance runs take about 50 and 25 seconds and 3.4 and 4.2 GB.
- The triangle run takes about 50 seconds, because the searches at L = 8 and 9 stop at the cap. The independent checks take about 25 seconds and 2.5 minutes. The rest take a few seconds each.
- The comparison recomputes every frame value. It also uses the node-game and frame-game modules of the round-three entry, [truth_claim_node_game.py](../audits/truth_claim_node_game.py) and [truth_claim_frame_game.py](../audits/truth_claim_frame_game.py).

[Comparison](../audits/frame_dag_reversible_pebbling_versus_frame_value.py) · [DAG writer](../audits/frame_dag_writer.py) · [Cone check](../audits/frame_dag_round_robin_cone_check.py) · [Black ≥ C check](../audits/frame_dag_black_pebbling_at_least_cells_check.py) · [Round-robin black numbers](../audits/frame_dag_round_robin_black_pebbling.py) · [Triangle](../audits/frame_dag_first_round_triangle_pebbling.py) · [Initialised memory](../audits/frame_dag_initialised_memory_check.py) · [Node-game bound](../audits/node_game_last_writer_potential_check.py) · [Independent check](../audits/frame_dag_pebbling_independent_check.py) · [Independent check, any cell count](../audits/frame_dag_pebbling_any_cell_count_independent_check.py) · [Chan, ECCC TR13-042](https://eccc.weizmann.ac.il/report/2013/042/download) · [Round-three attempts](parallel-proof-attempts-of-27-november-round-three.md)
