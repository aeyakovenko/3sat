# A cone-restricted bisection wins the frame game on every overwrite ladder within C·log₂(T/C) + O(C) placements

On every overwrite ladder touching C ≥ 2 cells, a bisection strategy that cuts only the ancestors of the claim currently challenged wins the frame game of the round-three truth-claim entry within f_C(T) ≤ C·log₂(T/C) + 2C + 2log₂C + 2 placements, so the frame value is o(T) whenever C = o(T). With the published lower bound C − 1, a ladder family has frame value at least c·T at every T exactly when liminf C(T)/T > 0. This settles negatively, for the frame game, the conjecture that the [frame-game lower-bound note](frame-game-lower-bound-on-overwrite-ladders.md) left open for ladders touching o(T) cells. The bound concerns the frame game only. The interval game restricts its prover to frame strategies that cut whole layers, so the bound does not pass to it; on the round-robin ladder its value is C·⌈log₂T⌉ at every size computed with 8C ≤ T ≤ 512. The node game is not covered. Open: whether the frame value is Θ(C) or Θ(C·log(T/C)) when C = o(T). These are bounds on a game value inside one move class, not time bounds; the linear, quadratic and cubic questions remain open. [Round-three summary](parallel-proof-attempts-of-27-november-round-three.md) · [Round-four summary](parallel-proof-attempts-of-27-november-round-four.md)

## Setting

The definitions are those of the round-three entry and the lower-bound note, as implemented in `truth_claim_frame_game.py`.
- **Frame DAG.** Steps τ = 1..T; on a ladder every step loads and then stores at a data-dependent address a_τ. The nodes are S_τ, the state after step τ, and C(σ, a), cell a after a step σ that does not write a. Their predecessors are S_τ ← S_{τ−1}, version(a_τ, τ−1) and C(σ, a) ← version(a, σ−1), S_{σ−1}, where version(a, σ) is S_σ if a_σ = a and C(σ, a) otherwise; S_0 and version(a, 0) are known facts, not nodes. Only the ancestor cone of S_T is kept. The layer of S_τ and of C(τ, a) is τ, every edge goes from layer μ−1 to layer μ, and layer μ has at most C nodes.
- **Frame value V.** The Dymond–Tompa game, one placement per move, with the sink challenged and unpebbled. After each placement the challenger stays or moves to the new pebble, and the game ends when every predecessor of the challenged node is pebbled. V is the number of placements. By Chan's theorem, as the lower-bound note reads it, the reversible pebbling price is V + 1.
- **Round-robin ladder.** a_τ = (τ − 1) mod C, so every cell is touched. The lower-bound note's round-robin ladder is the case C = ⌈T/2⌉.

## 1. The upper bound

**Lemma 1 (cone width).** For every node v at layer r and every 1 ≤ m < r, |anc(v) ∩ layer m| ≤ min(C, r − m + 1).

*Proof.* The bound C holds because a layer has at most C nodes. For r − m + 1, induct on k = r − m. For k = 1, anc(v) ∩ layer r−1 = preds(v), which has at most 2 nodes. In the step, edges join consecutive layers only, so anc(v) ∩ layer(m−1) is the union of preds(u) over u ∈ anc(v) ∩ layer m; every predecessor set is {S_{m−1}} plus at most one version node, so the union has at most 1 + |anc(v) ∩ layer m| ≤ k + 2 nodes. ∎

**Proposition 2 (cone-restricted bisection).** V ≤ f_C(T), where f_C(1) = 0 and f_C(L) = min(C, ⌈L/2⌉ + 1) + f_C(⌈L/2⌉).

*Proof.* The invariant (v, l) says that v is challenged at layer r > l and every ancestor of v in layer l is pebbled; layer 0 consists of known facts, so (S_T, 0) holds at the start. From (v, l) the prover wins at block cost at most f_C(r − l), by induction on L = r − l. For L = 1, preds(v) ⊆ anc(v) ∩ layer l is pebbled and the game is over. For L ≥ 2, put m = l + ⌊L/2⌋, so l < m < r, and place the block A = anc(v) ∩ layer m one claim at a time; by Lemma 1, |A| ≤ min(C, ⌈L/2⌉ + 1). If the challenger stays, (v, m) holds with r − m = ⌈L/2⌉. If it moves to u ∈ A, after j ≤ |A| placements, then anc(u) ⊆ anc(v), so anc(u) ∩ layer l is pebbled and (u, l) holds with m − l = ⌊L/2⌋; the cost is at most |A| + f_C(⌊L/2⌋). Pebbles already on the board are skipped, which only removes challenger options. Since f_C is non-decreasing, the cost is at most min(C, ⌈L/2⌉ + 1) + f_C(⌈L/2⌉) = f_C(L). ∎

The strategy differs from the round-three interval game and its bisection, which cut whole layers: it cuts only the ancestors of the currently challenged claim.

**Corollary 3 (closed form).** For T ≥ C ≥ 2, f_C(T) ≤ C·log₂(T/C) + 2C + 2log₂C + 2.

*Proof.* Since ⌈⌈x⌉/2⌉ = ⌈x/2⌉, f_C(T) = Σ_{i=1}^{k} min(C, ⌈T/2^i⌉ + 1) with k = ⌈log₂T⌉. Put j = ⌈log₂(T/C)⌉ ≥ 0. The terms i ≤ j add at most C·j ≤ C·(log₂(T/C) + 1). For i > j, ⌈T/2^i⌉ + 1 ≤ C·2^{j−i} + 2, because T/2^j ≤ C, so these add at most C + 2(k − j) ≤ C + 2(log₂C + 1). ∎

At C = T/log₂T this gives V ≤ C·(log₂log₂T + 2) + O(log T) = O(T·log log T/log T), which is o(T). The round-three bisection bound (C+1)⌈log₂T⌉ exceeds f_C(T) by a factor of about log₂T/(log₂(T/C) + 1), which is about log₂T/log₂log₂T at C = T/log₂T. The refutation of the Θ(T) frame value at C = T/log T is asymptotic: f_C(T)/T at C = round(T/log₂T) is 0.64 at T = 64, 0.31 at T = 2^16 and 0.156 at T = 2^40. On a grid of 2 ≤ C ≤ 300 the slack (f_C(T) − C·log₂(T/C))/C is at most 2.08:
```
closed form: max over grid of (f(T) - C*log2(T/C))/C = 2.0817 at (C, T, f) = (3, 9, 11); bound 3 holds
64 | 11 | 41 | 0.6406 | 72 | 28
65536 | 4096 | 20491 | 0.3127 | 65552 | 16384
1099511627776 | 27487790694 | 171798691872 | 0.1563 | 1099511627800 | 146288045561
```
The last three lines give T, C = round(T/log₂T), f_C(T), f_C(T)/T, (C+1)⌈log₂T⌉ and C·log₂(T/C).

**Corollary 4 (the conjecture on ladders, frame game).** If C(T) = o(T), then V = o(T), since x·log₂(1/x) → 0 as x = C/T → 0. For a family of address sequences with C(T) cells, the frame value is at least c·T at every T ≥ 2, for some c > 0, if and only if liminf C(T)/T > 0. If liminf C(T)/T = 0, Proposition 2 gives V/T → 0 along a subsequence. Otherwise C(T) ≥ c′·T for all T ≥ T₀, and the lower bound V ≥ C − 1 gives V ≥ (c′/2)·T for T ≥ max(T₀, 2/c′); V ≥ 1 covers the finitely many smaller T once c is small enough. So the clause of the round-three conjecture for every truth-claim game with one-step checks fails whenever liminf C(T)/T = 0, because the frame game is one of those games. For C(T) = Θ(T) the conjecture holds for the frame game and for games whose prover strategies are frame-game strategies, and it is open for other games, such as the node game.

**Which games the bound covers.** An upper bound on V passes only to games in which this strategy is legal. The interval, interface and pebble games of the round-three entry restrict the prover to frame-game strategies, so their values are at least V. The interval game cuts whole layers, so this strategy is not legal in it: on the round-robin ladder the journal's interval value is C·⌈log₂T⌉ at every size computed during review with 8C ≤ T ≤ 512 (288 against f_32(512) = 164). The interface and pebble games were not checked, and the node game is not covered. Reversible pebbling inherits the bound through Rev = V + 1.

**Remark (other step kinds).** The round-three model's loads and data-dependent stores also give layered DAGs whose predecessor sets are S plus at most one version node. A layer then has at most C + 1 nodes (after a pure load, no write is folded into S), so V ≤ f_{C+1}(T) for every run of that model touching C cells. This was checked during review on 77 runs: the constant reader, store-heavy runs and random mixed runs with T ≤ 12, all solved exactly.

**Checks.** On round-robin ladders the strategy's actual cost equals f_C at every size computed, so Lemma 1 is attained there, and the cost grows by exactly C per doubling of T:
```
4 256 | 29 | 29 | 40 | 256
16 256 | 83 | 83 | 136 | 256
```
(C, T | the strategy's cost | f_C(T) | (C+1)⌈log₂T⌉ | T). Against exact frame values, for every T = 2..10, on the round-robin ladder for every C = 2..T and on two random sequences for each of C ∈ {2, 3, ⌊T/3⌋, ⌊T/2⌋}, Lemma 1 holds at every node and layer, and exact V ≤ the best block strategy ≤ the midpoint strategy ≤ f_C(T); on 14 rows, all with C ≥ 5 and T ≥ 8, the exact solver's memo of 2^23 entries filled before it finished:
```
# rows 117, DT solved 103, DT == gmin on 27, violations 0
```
The independent check written during review plays the strategy one placement at a time on the true pebble set under the journal's rules, asserting the invariant at every node and that the game is over at every leaf, and computes the interval value; on 20 ladders up to T = 512 it finds no violation, and none on 72 ladders against exact values, 60 of them solved exactly:
```
rr 32 512 15888 | sim 164 | f 164 | interval 288 | C*log2(T/C)+2C+2log2C+2 = 204.0
# rows 72 solved 60 violations 0
```

## 2. Exact values on the round-robin ladder (data)

The exact frame values below come from the journal's solver (`frame_dag_dymond_tompa_value.cpp`); `≥ k` means that k − 1 placements were shown not to suffice before the memo filled.

| C | T | exact V | f_C(T) |
|---|---|---|---|
| 2 | 2..12 | 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7 | 2, 4, 4, 6, 6, 6, 6, 8, 8, 8, 8 |
| 2 | 13..22 | 7, 7, 7, 8, 8, 8, 8, 8, 8, 8 | 8, 8, 8, 8, 10, …, 10 |
| 2 | 23, 24 | 8, 9 | 10, 10 |
| 3 | 3..13 | 4, 5, 5, 6, 6, 7, 7, 8, 8, 8, 9 | 5, 5, 8, 8, 8, 8, 11, 11, 11, 11, 11 |
| 3 | 14, 15, 16, 17 | 9, 9, ≥ 10, ≥ 10 | 11, 11, 11, 14 |
| 4 | 4..11 | 5, 6, 7, 7, 7, 8, 9, 9 | 5, 9, 9, 9, 9, 13, 13, 13 |
| 4 | 12 | ≥ 10 | 13 |

- **C = 2.** V rises by 1 exactly at T = 3, 4, 6, 8, 12, 16, 24 and equals 2 + ⌊log₂T⌋ + ⌊log₂(T/3)⌋ for all T = 2..24. That is consistent with a slope of 2 = C per doubling of T rather than 1, but it is data only: nothing beyond V ≥ ⌈log₂T⌉ is proved for C = 2. At T = 2^j (j = 1..4), V = f_2(T) = 2j, so the bisection is exactly optimal there. The reversible pebbling price equals V + 1 for all T ≤ 12 (exhaustive).
- **C = 3, 4.** The data stop at T ≤ 5C and T ≤ 3C, too short to tell a slope of C per doubling from a smaller one.

## 3. Minimal blocking sets

A *blocking set* B meets every path from a source to S_T; it is *minimal* if no proper subset is blocking. The *column path* of cell c is the chain of nodes version(c, μ), μ = 1..T, within the cone; distinct cells have vertex-disjoint column paths.

**Lemma 5.** Let B be a minimal blocking set of the frame DAG of an overwrite ladder, with lowest layer a. For each cell c accessed in steps a..T, let λ_c be its first access at or after a, and let Λ(a) = max_c λ_c. Then (i) each such column path has a node of B in layers [a, λ_c]; (ii) B lies in layers [a, Λ(a)]; and (iii) B has exactly one node on the column path of each cell accessed in steps a..T, at a layer in [a, λ_c], and no other node, so |B| equals the number of such cells.

On the round-robin ladder, a minimal blocking set whose lowest layer is a ≤ T − C + 1 therefore has exactly C nodes, one on each column, and spreads over at most C layers. One whose lowest layer is higher has one node for each cell accessed at or after that layer: {S_T}, and on round robin with C ≥ 2 also preds(S_T), are minimal blocking sets of size 1 and 2.

*Proof.* Every layer above a has a node outside B with a B-avoiding path to S_T: take x ∈ B at layer a; by minimality some source-to-sink path avoids B∖{x}, it passes through x, and its part after x avoids B. Let Below be the set of nodes outside B that some source reaches by a B-avoiding path. Then S_λ ∉ Below for every λ ≥ a: for λ < T, the node of layer λ+1 just found lies outside B, has S_λ as a predecessor (on a ladder every node of layer λ+1 does) and has a B-avoiding path to S_T, so S_λ ∈ Below would complete a B-avoiding source-to-sink path; for λ = T this is the blocking property.
- (i) Column c's nodes below layer a are in Below, since B has nothing below a. If column c had no node of B in [a, λ_c], then version(c, μ) = C(μ, c) ∈ Below for μ = a..λ_c−1, each through its column predecessor, and then S_{λ_c} ∈ Below, a contradiction.
- (ii) Let x_c be the lowest node of B on column c in [a, λ_c], at layer μ_c, put B′ = {x_c}, and write Below′ for reachability avoiding B′. For every μ ≥ a and every c with μ_c ≤ μ, version(c, μ) ∉ Below′, by induction on μ. At μ = a, μ_c ≤ a forces μ_c = a, so version(c, a) = x_c ∈ B′. If μ+1 = μ_c, the node is x_c ∈ B′. Otherwise version(c, μ+1) is not a source (its layer is μ+1 ≥ 2), and both its predecessors are outside Below′: one is version(c, μ), the other is S_μ, which lies on column a_μ with μ_{a_μ} ≤ λ_{a_μ} ≤ μ, since μ ≥ a is an access of a_μ. At μ = T on column a_T this gives S_T ∉ Below′, so B′ is blocking, and by minimality B = B′ ⊆ layers [a, Λ(a)].
- (iii) B = B′, and the x_c lie on disjoint column paths, so they are distinct, one per cell accessed in steps a..T. ∎

The lemma has no surplus over the spread, unlike Lemma 4.3 of Chan, Lauria, Nordström and Vinyals (below), which says that a minimal blocking set spreading over d layers of a chain of width w has size at least d + w − 1. Here the C consecutive state claims S_M, …, S_{M+C−1}, with M + C ≤ T, form a minimal blocking set of size C spreading over C layers (removing S_M opens column a_M's path, which reaches S_{M+C}). The exhaustive check enumerates every vertex subset, keeps the minimal blocking sets and asserts (ii) and |B| ≥ (number of cells); the independent check written during review asserts the strong form (iii) on 9 round-robin and 40 random ladders with at most 24 nodes, where on random ladders the spread can exceed C (6 at C = 4), as it may, since spread ≤ C is claimed for round robin only:
```
C=4 T=7 nodes=22 minimal_blocking_sets=90 max_spread=4 violations=0
C=2 T=12 nodes=23 minimal_blocking_sets=22 max_spread=2 violations=0
```
and the independent check, on a random ladder whose spread exceeds C:
```
rand C=4 T=8 [0, 3, 1, 3, 1, 2, 3, 1] n=22 minimal=61 minsize=1 maxsize=4 maxspread=6 violations=0
```

## 4. The residual and the literature

The frame value lies between C − 1 and C·log₂(T/C) + O(C). Single-fault adversaries, whose false claims are the descendants of one node, force only about log₂(CT), since binary search on the state chain and then on one column finds the fault (a sketch, unchecked). An adversary for C·log(T/C) would have to hide a false path that visits the state chain only at gaps up to C.

S. M. Chan, M. Lauria, J. Nordström and M. Vinyals, *Hardness of Approximation in PSPACE and Separation Results for Pebble Games* (https://arxiv.org/abs/2305.19104, the full version of the FOCS 2015 paper), were read in part, through a text extraction that garbles formulas. Their Theorem 4.1, credited to Královič, gives reversible price at most p⌈log τ⌉ for a standard pebbling of time τ and space p, by bisection on configurations; the round-three bisection bound is of this kind. Their Lemma 4.5 proves reversible price at least w·log(ℓ/w)/2 for "roads" of width w and length ℓ, with no width restriction, by a Challenger that pays for each minimal blocking set through their Lemma 4.3. Lemma 5 gives size ≥ spread (on round robin, size = C ≥ spread). This may be enough for the payment step of their Lemma 4.5, but that is not verified, and unlike their Lemma 4.3 it gives no surplus of w − 1 over the spread. If their strategy transfers, V ≥ c·C·log₂(T/C) for some constant c > 0, hence V = Θ(C·log(T/C)), which is Θ(T·log log T/log T) at C = T/log T.

## 5. The three standard tests

- **(a) Fast solver for the hard family?** No time lower bound is claimed. The result is an upper bound on a game value, for linear-time runs; any lower bound in the residual would concern one move class on specific runs.
- **(b) 2-SAT?** A 2-SAT solver whose run is an overwrite ladder gets exactly the same values; the statements are about the method, not about a language.
- **(c) The relativized clock?** The strategy and Lemma 1 use only that every frame claim has predecessors "previous state plus at most one version", a combinatorial fact about these DAGs. A packed-query step depends on many bits of memory, so it is not a node of this frame model, and nothing follows about runs containing such queries. [Relativized clock](relativized-clock.md)

## 6. Exact obstruction and next step

The statement "the frame value is Θ(C·log T) at C = T/log T" is false by Proposition 2; the value there is at most C·(log₂log₂T + 2) + O(log T). The open question is whether V is Θ(C) or Θ(C·log(T/C)) on round-robin ladders as C → ∞. Either way it is o(T) when C = o(T), so the round-three program of Ω(T) frame claims needs Θ(T) cells.

The next lemma would be "on the round-robin ladder, V ≥ c·C·log₂(T/C) for T ≥ 2C". The first way in is to transfer the Challenger of Lemma 4.5 above, with Lemma 5 in place of their Lemma 4.3. That needs three things checked: the sub-instances the strategy focuses on must again have the round-robin frame shape, up to the cone's tapered top; pebbles placed in earlier phases may lie inside the new focus region and must not be paid for twice; and Lemma 5 is proved for the sink S_T only, while after a jump the focus sink may be a column claim, so the transfer needs Lemma 5 for such a sink or a rule that always refocuses on a state claim. Other ways in are a Raz–McKenzie colorer (the query complexity of the falsified-clause search on the frame DAG's pebbling formula) with a potential summed over the C disjoint column paths, or a prover strategy below C·log(T/C) that mixes column binary search with layer cuts. The next computation is C = 3 and 4 at T ≥ 8C, which needs a solver beyond 63 nodes.

## 7. What is not proved

- Any lower bound beyond max(C − 1, ⌈log₂T⌉). The bound ⌈log₂T⌉ comes from restricting a reversible pebbling to the state chain, a path, and rests on Chan's theorem.
- Whether the factor log(T/C) is real as C → ∞: C = 2 is settled numerically only to T = 24, and nothing for fixed C bears on that regime.
- The transfer of Lemma 4.5 of Chan, Lauria, Nordström and Vinyals, whose proof was read only through a lossy text extraction.
- The node game, and the interval, interface and pebble games: upper bounds on V do not pass to games whose prover strategies are frame-game strategies, and the interval game is not bounded by f_C on round robin.
- The lower-bound note's next lemma, Rev ≥ T − O(log T) at C = T/2, is untouched; Proposition 2 gives V ≤ f_{T/2}(T) = T + O(log T) there, consistent with it.
- Exact checks of the strategy cover T ≤ 10 only (103 of 117 rows solved); the proof covers all T. The remark on other step kinds is proved on paper and checked on 77 small runs.
- The lower bounds V ≥ 10 for C = 3 at T = 16 and 17 come from a single solver run; every other value of the exact-value table was reproduced, those for C = 2 at T = 24 and C = 4 at T = 12 during review.

## Reproducing the checks

Run from `audits/`. `frame_dag_solvers.py` builds the exact solvers in a temporary directory; nothing else is written.
```
python3 -I -B frame_game_cone_bisection.py
python3 -I -B frame_game_cone_bisection.py check 10 20 23
python3 -I -B frame_game_round_robin_exact_values.py
python3 -I -B frame_game_round_robin_exact_values.py 2 13 22 120 25 dt
python3 -I -B frame_dag_minimal_blocking_sets.py
python3 -I -B frame_dag_minimal_blocking_sets.py 3 8 4 7 5 6 2 12
python3 -I -B frame_game_cone_bisection_independent_check.py
python3 -I -B frame_game_cone_bisection_independent_check.py big 11 2,24 2,64 3,48 4,64 4,256 8,64 8,256 16,128 16,512 32,512
python3 -I -B frame_game_cone_bisection_independent_check.py exact 2026 10 15
python3 -I -B frame_game_cone_bisection_independent_check.py other 31 12 30
python3 -I -B frame_dag_minimal_blocking_sets_independent_check.py
```
With no argument each script runs a short default, in under 4 seconds. The `check` run takes about 40 seconds, the 13–22 exact values about 20 seconds and 0.5 GB, the larger blocking-set run about a minute, and the review's three larger runs about a minute and 5 GB, 80 seconds, and 3 seconds. The other rows of the exact-value table come from the same script with a memo of 2^25 (C = 3, T ≤ 13; C = 4, T ≤ 10), 2^27 (C = 4, T = 11 and 12, about 2 GB) or 2^28 (C = 2, T = 23 and 24; C = 3, T = 14–17, about 4 GB). [Cone bisection](../audits/frame_game_cone_bisection.py) · [Round-robin exact values](../audits/frame_game_round_robin_exact_values.py) · [Minimal blocking sets](../audits/frame_dag_minimal_blocking_sets.py) · [Independent strategy check](../audits/frame_game_cone_bisection_independent_check.py) · [Independent blocking check](../audits/frame_dag_minimal_blocking_sets_independent_check.py) · [Blocking checker (C++)](../audits/frame_dag_minimal_blocking_sets_independent.cpp) · [Chan, ECCC TR13-042](https://eccc.weizmann.ac.il/report/2013/042/download)
