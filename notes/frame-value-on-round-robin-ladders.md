# The frame value on round-robin overwrite ladders is C·log₂(T/C) ± O(C)

On the round-robin overwrite ladder with C cells and T steps, the frame value satisfies V ≥ C·log₂((T+C)/(4C)) for all C, T ≥ 1. With the [frame-game upper bound](frame-game-upper-bound-on-overwrite-ladders.md), C·log₂(T/C) − 2C ≤ V ≤ C·log₂(T/C) + 2C + 2log₂C + 2 for T ≥ C ≥ 2, so V = Θ(C·log(T/C)) once T ≥ 8C, and V = Θ(T·log log T/log T) at C = T/log₂T. This answers the question left open by the frame-game notes, whether the value is Θ(C) or Θ(C·log(T/C)) when C = o(T), for round robin; other ladders touching C cells can have V = O(C + log T). The proof transfers the Challenger of Chan, Lauria, Nordström and Vinyals's Lemma 4.5 (arXiv 2305.19104), a Dymond–Tompa game lower bound on roads, to the frame game, with the upper-bound note's Lemma 5 in place of their Lemma 4.3, and a potential that pays for pebbles carried into each new focus. During review every step was re-derived, the source was confirmed as the arXiv v1 TeX, and independent reimplementations of the Challenger and of the closure check found no failure. The result is about one move class of truth-claim games and says nothing about time or SAT; the linear, quadratic and cubic questions remain open. [Frame-game lower bound](frame-game-lower-bound-on-overwrite-ladders.md) · [Frame-game upper bound](frame-game-upper-bound-on-overwrite-ladders.md)

## Setting

The definitions are those of the frame-game notes. The round-robin ladder has addresses a_τ = (τ−1) mod C for τ = 1..T. Its frame DAG is the cone of the last state S_T: node (μ, c) is version(c, μ), so S_μ = (μ, a_μ), every node at layer μ ≥ 2 has the predecessors (μ−1, c) and S_{μ−1} (which coincide when c = a_{μ−1}), and layer 1 holds the sources. V is the number of placements in the Dymond–Tompa game with the sink challenged and unpebbled: the challenger stays or moves to the new pebble, and the game ends when every predecessor of the challenged node is pebbled.

**The source.** S. M. Chan, M. Lauria, J. Nordström and M. Vinyals, *Hardness of Approximation in PSPACE and Separation Results for Pebble Games* ([arXiv:2305.19104](https://arxiv.org/abs/2305.19104)). Lines 8280–8579 of its v1 TeX source were read in full: Theorem 4.2, chains and roads, blocking sets, Lemmas 4.3 and 4.4, and Lemma 4.5 with its whole proof. During review the e-print was fetched again and found byte-identical to the copy used (sha256 765f410a…ec87; the TeX file `ReversiblePebbling-single-file.tex` has sha256 8ceada5f…fe6), so the TeX is the v1 source. Their Lemma 4.5 reads: "The reversible pebbling price of a road of width w and length ℓ is at least w·log(ℓ/w)/2." Its Challenger focuses on a subgraph, keeping a semiopen path from the subgraph's sink to the challenged pebble; it stays while that sink is connected to the sources; when a blocking set forms it takes a minimal one, B, which contains the last pebble u, and either jumps, focusing on the ancestors of the vertex v at layer a − 1 of a semiopen path from the sources to u, or stays, focusing on the road above B. Two points of the source matter here:
- **A slip in their (4.2).** The text before it focuses on "the road of length ℓ − b − 1 obtained considering only the vertices at the layers from b + 1 to ℓ", but (4.2) writes DT(w, b − 1). From m ≤ ℓ/2 one gets ℓ − b − 1 ≥ (ℓ − d − 1)/2, which is the next step of (4.2), while b − 1 ≥ (ℓ − d − 1)/2 does not follow, so the term should read DT(w, ℓ − b − 1). The lemma is unaffected, and the v1 PDF has the same slip.
- **Carried-over pebbles are implicit.** The source applies its induction to the new focus road and says only that it "is not blocked" and is disjoint from B; the new road may already hold earlier pebbles. The potential below makes this step explicit. The published proof is not claimed wrong.

## 1. The statement

**Theorem.** On the round-robin ladder with C ≥ 1 cells and T ≥ 1 steps, V ≥ C·log₂((T + C)/(4C)).

For T ≥ 2C this is at least C·log₂(T/C) − 2C, and at least (1/3)·C·log₂(T/C) once T ≥ 8C. For 2C ≤ T < 8C the lower-bound note's V ≥ C − 1 ≥ C/2 > (1/6)·C·log₂(T/C) applies, so the upper-bound note's next lemma, V ≥ c·C·log₂(T/C) for every C ≥ 2 and T ≥ 2C, holds with c = 1/6.

## 2. The class of foci

A *segment* of length L is an address sequence e_1..e_L over the C cells such that e_1..e_{L−1} is a consecutive piece of round robin; the top address e_L is arbitrary. Its frame DAG F(e) is the cone of its last state, layers 1..L. A *focus* is R = (v_R, s): the nodes of anc(v_R) ∪ {v_R} in layers ≥ s, for a node v_R of the original DAG at layer top ≥ s.

**Claim 1 (closure).** If R is (isomorphic to) F(e) for a segment e of length L = top − s + 1, then:
- **(a) stay focus:** for s ≤ b < top, the nodes of R in layers ≥ b + 1 form F(e_{b−s+2}, …, e_L), with layer b + 1 as sources. Every edge joins consecutive layers, so a path from layer ≥ b + 1 to v_R stays there, and a node (b + 1, c) lies in the cone exactly when it does in the suffix's own frame DAG.
- **(b) jump focus:** for a node v of R at layer σ − 1 ≥ s with cell c, the nodes of anc(v) ∪ {v} in layers ≥ s form F(e_1, …, e_{σ−1−s}, c). If v is a state this is truncation at the top; if v is the column claim C(σ−1, c), its predecessors version(c, σ−2) and S_{σ−2} are those of the last state of the ladder whose step σ − 1 accesses c. The new segment is round robin except its top.

The whole cone of the round-robin ladder is F(e) with e round robin of length T, so every focus below is in the class; this settles the upper-bound note's question about the shapes of the sub-instances, and a column-claim sink is the state claim of a ladder with a changed top.

**Lemma 5 in the class.** The upper-bound note's Lemma 5, in its strong form (iii), holds for the frame DAG of every overwrite ladder: a minimal blocking set B with lowest layer a has exactly one node on the column of each cell accessed in steps a..L, at a layer in [a, λ_c], where λ_c is the first access of c at or after a, and no other node. For a segment of length L, with layers relative to the focus:
- **(A) a ≤ L − C.** Steps a..a+C−1 lie in the round-robin part and access all C cells, so |B| = C and the spread b − a + 1 is at most C.
- **(B) a > L − C.** Steps a..L−1 are L − a < C consecutive round-robin steps, and the top cell adds 0 or 1, so |B| = x ∈ {L − a, L − a + 1}, with 1 ≤ x ≤ C.

## 3. The Challenger σ

A position consists of the pebble set P (pebbles are never removed), the challenged node u_c and the focus R = (v_R, s) of L layers. R is **open** if some path inside R from a layer-s node to v_R contains no pebbled node, its ends included. The **link** holds if u_c = v_R ∉ P, or there is a path v_R = y_0 → … → y_k = u_c with k ≥ 1 and y_0, …, y_{k−1} ∉ P. I(R) means that R is open and the link holds.

**Fact 1.** If I(R) and L ≥ 2, the game is not over: if u_c ≠ v_R, y_{k−1} is an unpebbled predecessor of u_c; if u_c = v_R, an open path has an edge, and its second-to-last node is one.

At the start P = ∅ and u_c = v_R = S_T with s = 1, so I(R) holds. After the Pebbler places p, with P′ = P ∪ {p}:
1. **If p ∈ R and R is no longer open.** Let B ⊆ P′ ∩ R be a minimal blocking set of R; since P ∩ R did not block, p ∈ B. Before p an open path Q ran from layer s to v_R, and now p ∈ Q. Let a ≤ b be B's lowest and highest layers relative to R.
   - **(1a) a ≤ L − C.** Stay if a + b ≤ L, with new focus R ∩ (layers > b); otherwise jump to p, with new focus anc(v) ∪ {v} in layers ≥ s, where v is Q's node at layer a − 1.
   - **(1b) a > L − C.** Jump to p, with the same v. If a = 1 there is no such v: σ jumps to p and has no focus from then on.
2. **Else, if p breaks the link.** Then p lies strictly above v_R on a link path (p = v_R falls under rule 1, since it closes R). Jump to p; the focus is unchanged and the new link is the prefix of the old link path.
3. **Otherwise stay.**
4. **No focus.** Once σ has no focus (rule 1b with a = 1), it stays on every later placement, so σ is a total strategy.

If p = v_R, then {v_R} is the unique minimal blocking subset, so a = b = L and rule 1b refocuses on the ancestors of Q's node at layer L − 1.

**I(R′) is restored after rule 1.** After a jump, Q's part from v to p has no pebble except p, so the link from v to p holds, and Q's part from layer s to v is pebble-free and lies in the new focus. After a stay the link is untouched, since p is at layer ≤ b < L, and Q's part above layer b is pebble-free because B ⊆ layers [a, b]. Rules 2 and 3 keep I(R).

**Nesting.** Every new focus R′ satisfies R′ ⊆ R and R′ ∩ B = ∅, because B ⊆ layers [a, b] and R′ ⊆ layers < a or > b. In case 1a every jump has a ≥ 2, since 2a ≥ L − C + 2 and L ≥ a + C give 2a ≥ a + 2. Case 1b with a = 1 forces L ≤ C; nothing is claimed after that move, and the Main Lemma never meets it, because it needs G(L) > 0, that is L > 3C.

## 4. The Main Lemma and the closed form

Let G(L) = C·log₂((L + C)/(4C)) and G⁺ = max(0, G).

**Main Lemma.** Take any position with focus R of L layers in the class, I(R) holding, and p_R = |P ∩ R| pebbles inside R. Against every Pebbler continuation, σ forces at least G⁺(L) − p_R further placements before the game ends.

*Proof, by strong induction on L.* If G(L) ≤ 0 there is nothing to show; otherwise L > 3C ≥ 3, and by Fact 1 the game cannot end while the focus is R. The focus changes only by rule 1. If that never happens, the game never ends. Otherwise let k be the number of placements up to and including the rule-1 move, and P′ the pebble set after it. Then |P′ ∩ R| ≤ p_R + k, and |P′ ∩ R| ≥ |B| + |P′ ∩ R′| by nesting; I(R′) holds and L′ < L. By induction at least G⁺(L′) − |P′ ∩ R′| further placements follow, so in all

  k + G⁺(L′) − |P′ ∩ R′| ≥ |P′ ∩ R| − p_R + G⁺(L′) − |P′ ∩ R′| ≥ |B| + G⁺(L′) − p_R,

and it remains to show |B| + G⁺(L′) ≥ G(L) when G(L) > 0, that is L > 3C:
- **Case 1a** (|B| = C and b − a + 1 ≤ C by (A)). A stay (a + b ≤ L) gives 2b ≤ (a + b) + (b − a) ≤ L + C − 1, so L′ = L − b ≥ (L − C + 1)/2. A jump (a + b ≥ L + 1) gives 2a ≥ L + 1 − (C − 1), so L′ = a − 1 ≥ (L − C)/2. Either way L′ + C ≥ (L + C)/2, so G(L′) ≥ G(L) − C and |B| + G⁺(L′) ≥ G(L).
- **Case 1b** (|B| = x with 1 ≤ x ≤ C and x ≥ L − a by (B)). L′ = a − 1 ≥ L − x − 1. Put N = L + C > 4C; then G(L′) ≥ G(L) + C·log₂(1 − (x+1)/N), and it suffices that φ(x) = x + C·log₂(1 − (x+1)/N) ≥ 0 on [1, C]. φ is concave, so check the endpoints. At x = 1, φ(1) ≥ 0 iff 1 − 2/N ≥ 2^{−1/C}, and 1 − 2/N > 1 − 1/(2C) ≥ 2^{−1/C}, because t ↦ 2^{−t} + t/2 is convex and equals 1 at t = 0 and t = 1; take t = 1/C. At x = C, φ(C) ≥ 0 iff N ≥ 2C + 2, which holds since N > 4C ≥ 2C + 2. ∎

At the start p_R = 0 and L = T, so V ≥ G⁺(T), which is the Theorem.

**Why the surplus of their Lemma 4.3 is not needed.** CLNV need a blocking set of size d + w − 1 because their target w·log(ℓ/w)/2 is paid for by w/2 per halving plus the d − 1 discarded layers. Here the halving is L ↦ L′ ≥ (L − C)/2, which satisfies L′ + C ≥ (L + C)/2 exactly, so a payment of C per halving gives C·log₂(L + C) with no loss: the discarded layers are absorbed by the shift +C inside the logarithm, and Lemma 5's size equal to the spread is enough. Near the top, Lemma 5 gives |B| ≥ L − a, so a payment of x loses at most x + 1 layers.

**Corollaries.**
- **Two-sided bound.** log₂((T+C)/(4C)) ≥ log₂(T/C) − 2, so with the upper-bound note's Proposition 2 and Corollary 3, for T ≥ C ≥ 2, C·log₂(T/C) − 2C ≤ V ≤ f_C(T) ≤ C·log₂(T/C) + 2C + 2log₂C + 2.
- **Reversible pebbling.** Rev = V + 1 by Chan's Theorem 1, as the lower-bound note reads it at source (its Section 5), so the reversible pebbling price of the round-robin frame DAG is C·log₂(T/C) ± O(C), while C ≤ Black ≤ C + 1 (that note's Sections 3 and 4): another multiplicative separation Θ(log(T/C)) between standard and reversible pebbling, of the same form as CLNV's roads, for DAGs with Θ(CT) nodes and fan-in 2.
- **Other games.** Lower bounds on V pass to every game whose prover strategies are frame-game strategies. By the lower-bound note's Setting, citing the round-three entry, the interval game is one of them up to one folded claim, so on round robin its value is at least C·log₂((T+C)/(4C)) − 1, consistent with the value C·⌈log₂T⌉ that the upper-bound note reports at every size computed.
- **At C = T/log₂T**, V = C·(log₂log₂T ± O(1)) = Θ(T·log log T/log T).

**General ladders.** The lower bound is specific to round robin. Take the ladder 0, 1, …, C−1 followed by T − C accesses of cell 0. For τ ≥ C + 2, S_τ has the single predecessor S_{τ−1}, and no column node above layer C + 1 is in the cone. The prover places S_{C+1}: if the challenger moves there, the upper-bound note's strategy on the cone of S_{C+1} costs at most f_C(C+1) ≤ 3C + 2log₂C + 2 for C ≥ 2 (Corollary 3, since C·log₂(1 + 1/C) ≤ log₂e < C); if it stays, bisection on the path S_{C+2}..S_{T−1} costs ⌈log₂(T − C − 1)⌉. So V ≤ 1 + max(f_C(C+1), ⌈log₂T⌉) = O(C + log T), which is o(C·log(T/C)) when, for example, C = √T. "The frame value on ladders touching C cells is Θ(C·log(T/C))" therefore holds as an upper bound on every ladder and as a lower bound on round robin, not as a statement about all ladders.

## 5. Checks

**The exact recursion.** The same induction, taking the minimum over every blocking-set shape allowed by (A) and (B) and the Challenger's better option in case 1a, gives a valid lower bound V ≥ g(T):

  g(0) = g(1) = 0, g(L) = min( min_{1≤a≤L−C, 1≤d≤C} C + max(g(L−a−d+1), g(a−1)), min_{max(1,L−C+1)≤a≤L} max(1, L−a) + g(a−1) ).

`frame_game_round_robin_recursion.py` compares g with every exact frame value recorded in the frame-game notes (C = 2, T ≤ 24; C = 3, T ≤ 15; C = 4, T ≤ 11; and C = ⌈T/2⌉, T ≤ 10); a single g > V would refute the proof. It also checks g ≥ G and g ≤ f_C for all C ≤ 16 and L ≤ 500, and a fast version of the recursion against the brute-force one:

```
C=2 T=24: g_rec=6 exact V=9 f_C=10 G=3.40 ok
C=3 T=15: g_rec=6 exact V=9 f_C=11 G=1.75 ok
rows 47 violations 0
C<=16 L<=500: violations 0; min over L>=4C of (g - C log2(L/C))/C = -0.9944 at C=1 L=255 g=7
grec == grec_fast for C<=12, L<=400
```

At L = C·2^k (k = 2..10) g − C·log₂(L/C) lies between −C/2 and −C/4 in each of the 36 rows for C = 2, 4, 16 and 64, and f_C − C·log₂(L/C) is C + 5 at C = 64, k = 10; both ratios to C·log₂(L/C) tend to 1:

```
C | L | g_rec | G=C*log2((L+C)/4C) | C*log2(L/C) | f_C(L) | g_rec/(C log2(L/C)) | f_C/(C log2(L/C))
2 | 2048 | 19 | 16.0 | 20.0 | 22 | 0.9500 | 1.1000
16 | 16384 | 152 | 128.0 | 160.0 | 179 | 0.9500 | 1.1187
64 | 65536 | 608 | 512.1 | 640.0 | 709 | 0.9500 | 1.1078
```

**σ against an exhaustive Pebbler.** `frame_game_round_robin_challenger.py` builds the round-robin frame DAG, plays σ exactly as in Section 3 with deterministic tie-breaking (B by greedy single-node removal in index order, v as the least index, and the midpoint rule in case 1a, which keeps the longer side and so realises the recursion's maximum, since g is nondecreasing), and searches breadth first over all Pebbler move sequences for the least number of placements P*(σ) with which some Pebbler ends the game. At every answer of σ it asserts p ∈ B, Lemma 5's strong form inside the focus with (A) and (B), that v exists, I(R′), Fact 1, and that a jump with a = 1 happens only when L ≤ C. The theorem predicts g(T) ≤ P*(σ), and P*(σ) ≤ V must hold. In Pebbler mode 0 the Pebbler may place any unpebbled node; in mode 1 only proper ancestors of the challenged node, as the journal's exact solver does. On C = 2, 3, 4 and T ≤ 12, both modes:

```
C T n | g_rec | Pstar(any move) | Pstar(ancestors of uc) | exact V | f_C
2 3 5 | 1 | 2 | 3 | 3 | 4
2 6 11 | 3 | 3 | 3 | 5 | 6
2 12 23 | 4 | 5 | 5 | 7 | 8
3 12 33 | 5 | 6 | 6 | 8 | 11
4 11 38 | 5 | 7 | 7 | 9 | 13
4 12 42 | 6 | 7 | 7 | >=10 | 13
runs 60, rule-1 answers with Lemma 5 asserted: 6348426
violations 0
```

No assertion failed. σ is not an optimal Challenger (P*(σ) < V on most rows). The one mode difference, C = 2, T = 3, is the excepted case a = 1 with L = 2 ≤ C: the mode-0 Pebbler places the challenged sink itself, σ refocuses on {S_1, C(2, 0)}, and a placement on S_1 closes that focus at a = 1. In Pebbler mode 1 with a larger memo (`large`), the runs at C = 2, T = 13 to 18; C = 3, T = 13 to 15; C = 5, T = 5 to 10; C = 6, T = 6 to 9; and C = 4, T = 13, where the memo filled at P*(σ) ≥ 7, give no violation either. Some of its rows, and its last lines:

```
C T n | g_rec | Pstar(any move) | Pstar(ancestors of uc) | exact V | f_C
2 18 35 | 5 | - | 6 | 8 | 10
3 15 42 | 6 | - | 7 | 9 | 11
5 10 40 | 5 | - | 7 | 9 | 14
6 9 39 | 4 | - | 7 | ? | 15
runs 20, rule-1 answers with Lemma 5 asserted: 21591648
violations 0
```

The branch counters (`branches`) show every rule of σ in use, including rule 2 and the jump with a = 1:

```
sigma C=2 T=18 n=35 restrict=1: Pstar 6 states 1886831 asserts 1812905
branches: 1a-stay 941443 1a-jump 693661 1b 177801 (of which a=1, no focus: 2) rule2 18652 rule3 6316758
sigma C=3 T=15 n=42 restrict=1: Pstar 7 states 9562009 asserts 3457962
branches: 1a-stay 1906162 1a-jump 1003697 1b 548103 (of which a=1, no focus: 1) rule2 42600 rule3 46593120
sigma C=4 T=11 n=38 restrict=0: Pstar 7 states 4061043 asserts 1305379
branches: 1a-stay 284924 1a-jump 114577 1b 905878 (of which a=1, no focus: 1) rule2 8424 rule3 20765467
```

**Closure.** `frame_game_focus_closure_check.py` compares, for every node v of the round-robin frame DAG and every s ≤ layer(v), the nodes of anc(v) ∪ {v} in layers ≥ s, with their edges, against the frame DAG of the segment a_s..a_{σ−1}, cell(v), under the layer shift τ ↦ τ − s + 1; this covers Claim 1(a) and (b), including nested foci:

```
closure check: C<=5, T<=14: 6504 (node, s) foci compared with frame_dag of the top-modified segment; all isomorphic
```

**The general-ladder example.** `frame_game_general_ladder_example.py` runs the exact Dymond–Tompa solver on the ladder of Section 4:

```
ladder 0..2 then 0^37: n=45 frame_dt: exact 6 states 1168681 | round robin (C=3, T=40): g_rec=10, f_C=17
ladder 0..3 then 0^36: n=49 frame_dt: lower 7 states 11744052 | round robin (C=4, T=40): g_rec=11, f_C=21
```

At C = 3, T = 40 that ladder has V = 6 exactly, while the round-robin ladder of that size has V ≥ g = 10. At C = 4 the solver's memo filled at V ≥ 7; the strategy of Section 4 gives V ≤ 1 + max(f_4(5), ⌈log₂35⌉) = 10, below round robin's 11.

**Independent checks during review.** `frame_game_round_robin_challenger_independent.py` implements σ from Section 3 alone, with its own frame DAG, its own blocking, open and link tests, and two tie-breaking variants that differ from the challenger above (B greedy in descending order with v of largest index, and greedy ascending with v of smallest index); the Pebbler may place any unpebbled node. It asserts, at every answer, that B is minimal and blocking with p ∈ B, Lemma 5's strong form with (A) and (B), I(R′) and nesting after rule 1, rule 2 only with p ∉ R, Fact 1, and a jump with a = 1 only when L ≤ C; and at the end g(T) ≤ P*(σ) ≤ V where its own exact solver ran. Both variants hit every branch, including the a = 1 no-focus case. Its two lists, 23 instances and 46 runs, end without a violation:

```
C=4 T=5 n=14 [asc,min] g=2 G+=0.00 Pstar=4 V=6 states=573 r1a_stay=24 r1a_jump=0 r1b=157 nofocus=1 r2=0 r3=1253 ok
violations 0
C=2 T=12 n=23 [asc,min] g=4 G+=1.61 Pstar=5 V=None states=52293 r1a_stay=23556 r1a_jump=14847 r1b=12742 nofocus=1 r2=523 r3=137156 ok
C=1 T=33 n=33 [asc,min] g=5 G+=3.09 Pstar=6 V=None states=1015391 r1a_stay=712312 r1a_jump=644212 r1b=136225 nofocus=0 r2=0 r3=2416372 ok
violations 0
```

At C = 3 and 4 these sizes have T ≤ 3C, where the closed form G is not positive, so there they test the recursion g rather than G; the challenger above has G > 0 at C = 3 for T = 10 to 15, and at C = 4 only at T = 13, where its memo filled. `frame_game_focus_closure_independent_check.py` builds the frame DAG from the definition and compares the round-robin foci, and also segments of the class with an arbitrary round-robin start and an arbitrary top:

```
closure: round robin C<=5, T<=12: 4074 foci; segments with arbitrary start/top: 52050 foci; all equal
```

## 6. The three standard tests

- **(a) Fast solver for the hard family.** No time lower bound is claimed. The statement is about game values of specific linear-time runs inside one move class, and the run itself is the fast solver.
- **(b) 2-SAT.** A 2-SAT solver whose run is a round-robin overwrite ladder gets the same value; the bound is about the method, not a language, as for the other frame-game notes.
- **(c) The oracle of the [relativized clock](relativized-clock.md).** The proof is a combinatorial fact about frame DAGs, whose nodes have the predecessors "previous state plus one version", so no oracle enters and it holds in either world. A packed-query step is not a node of this frame model, so nothing follows about runs containing such queries, and no conclusion about time follows in either world.

## 7. Exact obstruction and next step

- **What this closes.** The frame-game program of the round-three entry and the two frame-game notes is settled on round-robin ladders up to an additive O(C): V = C·log₂(T/C) ± O(C). The frame game forces Ω(T) placements on round-robin ladders exactly when C = Θ(T), by the lower-bound note's V ≥ C − 1 and the upper-bound note's Corollary 4. For the other games of the move class only the lower bound passes, and only to games whose prover strategies are frame-game strategies: the "if" direction is open for the node game, and the "only if" direction is not shown for the interval game, whose computed value C·⌈log₂T⌉ is about T at C = T/log₂T.
- **The obstruction for the larger route** is the one the frame-game notes named, now with a matching lower bound: the frame game measures a pebbling quantity of one run, and this quantity is Θ(C·log(T/C)) for a 2-SAT solver as much as for SAT. No step here bears on SAT.
- **Next lemmas inside the move class.** The constant when C = Θ(T): at C = T/2 the bound here is negative, the lower-bound note's C − 1 is the best known, and the data suggest about T (that note's next lemma, Rev ≥ T − O(log T) at C = T/2, is untouched). A characterisation of V on general ladders by a window profile of the address sequence: for a sequence in which every window of W steps meets k(W) distinct cells, the same Challenger should give something like a sum of k(W) over halvings. And the interval game on round robin, where the data say C·⌈log₂T⌉ and this note gives only C·log₂(T/C) − 2C below it.

## 8. What is not proved

- Anything about time, or about SAT.
- Lower bounds for ladders other than round robin: the proof uses (A) and (B), which need the round-robin window property below the top step.
- The matching coefficient beyond an additive O(C): the bounds differ by at most 4C + 2log₂C + 2.
- The node game, which is not a frame-game strategy class, so neither bound covers it.
- CLNV's paper beyond lines 8280–8579 of the TeX; every step used is reproved here. Chan's Theorem 1 is used only for the reversible-pebbling corollary, through the lower-bound note's reading.
- Lemma 5 is not reproved here: it is the upper-bound note's strong form (iii), checked during that note's review, and it was asserted at every rule-1 answer of the checks.
- That σ is an optimal Challenger: it is not.
- The finite checks beyond their ranges: σ against an exhaustive Pebbler for C ≤ 6 and T ≤ 18; closure for C ≤ 5 and T ≤ 14; the recursion for C ≤ 16 and L ≤ 500, plus the tables. The Theorem rests on the proof, not on these checks.

## Reproducing the checks

Run from `audits/`, under an 8 GB memory cap; the C++ programs are compiled into temporary directories with `$CXX`. No script writes files, and with no argument each script runs a short default.

```
python3 frame_game_round_robin_recursion.py
python3 frame_game_round_robin_recursion.py closed 16 500
python3 frame_game_round_robin_recursion.py fastcheck 12 400
python3 frame_game_round_robin_recursion.py table 2 8,16,32,64,128,256,512,1024,2048
python3 frame_game_round_robin_recursion.py table 4 16,32,64,128,256,512,1024,2048,4096
python3 frame_game_round_robin_recursion.py table 16 64,128,256,512,1024,2048,4096,8192,16384
python3 frame_game_round_robin_recursion.py table 64 256,512,1024,2048,4096,8192,16384,32768,65536
python3 frame_game_round_robin_challenger.py
python3 frame_game_round_robin_challenger.py large
python3 frame_game_round_robin_challenger.py branches
python3 frame_game_focus_closure_check.py
python3 frame_game_general_ladder_example.py 3 40
python3 frame_game_general_ladder_example.py 4 40
python3 frame_game_round_robin_challenger_independent.py
python3 frame_game_round_robin_challenger_independent.py 2,8 2,9 2,10 2,11 2,12 3,7 3,8 3,9 4,6 4,7 1,16 1,33
python3 frame_game_focus_closure_independent_check.py
```

The commands take about 7 minutes in all: `large` about 2 minutes, allocating up to 3 GB, the independent challenger's second list about 4 minutes, and each of the others under 30 seconds. [Recursion](../audits/frame_game_round_robin_recursion.py) · [Challenger](../audits/frame_game_round_robin_challenger.py) · [Challenger program](../audits/frame_game_round_robin_challenger.cpp) · [Closure check](../audits/frame_game_focus_closure_check.py) · [General-ladder example](../audits/frame_game_general_ladder_example.py) · [Independent challenger](../audits/frame_game_round_robin_challenger_independent.py) · [Independent closure check](../audits/frame_game_focus_closure_independent_check.py) · [Exact solvers](../audits/frame_dag_solvers.py)
