# The price inequality and its table-reading dual cannot certify more than O(N log N)

The vertex-site price inequality (P) behind the list-distinctness technique, and its single-vertex dual (D), which charges each vertex the price of its own table, both cap at O(N log N). One Beneš graph G_N with |E(G_N)| = N(6 log₂N − 3) edges passes (P) at every placement, and (D) with all-GHZ tables, for every target with N binary legs over every field (Theorem C). Every 2×2×2 table over a finite field is dominated by the GHZ tensor at every spectral point (Lemma A, checked exhaustively over F₂ and F₃, and over F₅ during review). So reading the network's or the target's tables through (P) or (D) adds nothing beyond topology, and "B⊕B is not a subspace" is invisible to them. This is a sharper, uniform form of the technique-ceiling note's Lemma 2 and of the round-three gadget cap, with a worse constant than the gadget cap. Price inequalities that place multi-vertex pieces as one tensor are not covered, since Lemma A's domination fails for two-vertex pieces. The upstream batch bound uses diagonal counting, which (P) and (D) cannot express. Both remain open escapes for the circuit route. The direction, reading the network's vertex tables through prices for the fixed-B slices, came from an external review. Nothing here is a lower bound; the linear, quadratic and cubic questions remain open. [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md) · [Round-three summary](parallel-proof-attempts-of-27-november-round-three.md) · [Simulating a RAM step by exact networks](simulating-a-ram-step-by-exact-networks.md)

## Setting

The framework is that of `background.tex` in the 24 November matrix-multiplication preprint (upstream tree at the journal's pinned commit: https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026; read from a local copy whose revision was not compared with that commit). Sites carry spaces. A spectral point φ is restriction-monotone, ⊕-additive and ⊗-multiplicative, with φ(0) = 0 and φ(**1**) = 1, so nonzero tensors have φ ≥ 1; the price at scale D is H = D log φ. The common-label rate δ(A) is defined by H(Δ_A(q)) = δ(A) log q, and the wire distance d(a,b) = δ({a,b}) is a pseudometric. The transport bound is |H(T;x) − H(T;y)| ≤ Σ_i d(x_i,y_i) log q_i, and a nonzero tensor with all legs at one site has price 0. These three facts follow from the axioms in a line each: Δ_{a,c} is a restriction of Δ_{a,b}⊗Δ_{b,c}; T(x) is a restriction of T(y)⊗⊗_iΔ_{x_i,y_i}(q_i); and a nonzero tensor at one site is equivalent to the unit.

**The primal inequality (P).** Sites are the vertices of a network G realizing f, and each exterior bit has its own leaf. Then f, with its legs at the leaves x, is a restriction of ⊗_e Δ_e(2) by one map per vertex, so H(f; x) ≤ log 2 · Σ_{e∈E(G)} d(e). The same right side bounds every restriction of f, and tables never enter. The preprint states this only for routed wires (`list.tex`: r·E_μ d ≤ m·E_α d, from Σ_i d(x_i, y_{π(i)}) ≤ Σ_e d(e) per permutation); the same argument gives (P) for any realized f.

**The dual inequality (D).** Put one site at each edge, internal or exterior, and place the table t_v of vertex v with its legs at the sites y_v of its incident edges. Then f is the image of ⊗_v t_v under the pairing map k²⊗k² → k at each internal-edge site, so H(f; x) ≤ Σ_v H(t_v; y_v). This form, which is not in the preprint, reads the tables: a rank-one table costs 0, a "matrix ⊗ vector" table one wire price, and a table spread across all three legs more. A certificate excludes a topology through (D) when, for every table assignment, some placement violates (D).

## Lemma A: trivalent tables are dominated by GHZ

**Lemma A.** Let k be a finite field, t ∈ (k²)^{⊗3} a table whose legs sit at sites a, b, c (not necessarily distinct), and φ a spectral point. Then φ(t) ≤ φ(Δ_{{a,b,c}}(2)), and hence H(t; y) ≤ δ({a,b,c}) log 2.

*Proof.* There are three cases, by the GL₂(k)³-orbit of t.
- **Tensor rank ≤ 2.** Write t = Σ_{j≤2} u_j⊗v_j⊗w_j, the image of Δ(2) = Σ_j f_j⊗f_j⊗f_j under f_j ↦ u_j, v_j, w_j at the three legs: a restriction (legs at a common site get the product map).
- **The orbit of W = e₁e₀e₀ + e₀e₁e₀ + e₀e₀e₁.** Over k[ε], take A = B: f₀ ↦ e₀+εe₁, f₁ ↦ e₀, and C: f₀ ↦ e₀+εe₁, f₁ ↦ −e₀. Then (A⊗B⊗C)Δ(2) = εW + O(ε²), and comparing the coefficients of εⁿ in the n-th power gives W^{⊗n} = Σ_{a+b+c=n} (A_a⊗B_b⊗C_c)Δ(2)^{⊗n}, with A_a the εᵃ-coefficient of A^{⊗n}. A sum of m restrictions of S is a restriction of S^{⊕m} (block-concatenated maps at every site), so φ(W)ⁿ ≤ C(n+2,2)·φ(Δ(2))ⁿ, and n-th roots give φ(W) ≤ φ(Δ(2)).
- **The multiplication tensor M_K of the quadratic extension K/k** (separable, since k is finite). The map a⊗b ↦ (ab, aσ(b)), with σ the Frobenius, is an algebra isomorphism ψ: K⊗_kK → K×K. Through the invertible leg maps (ψ^{−T}, ψ^{−T}, ψ) it gives M_K⊗M_K ≅ M_K⊗Δ_{{a,b,c}}(2), so φ(M_K)² = φ(M_K)·φ(Δ(2)), and φ(M_K) = φ(Δ(2)) since φ(M_K) ≥ 1.

The cases are complete. A non-concise table (some flattening of rank ≤ 1) has rank ≤ 2. A concise table is a regular 2×2 pencil whose determinant is a nonzero binary quadratic form: two distinct rational roots give rank 2, a double root gives W, and an irreducible form gives M_K. This is the standard Kronecker–Weierstrass argument, stated rather than formalized. ∎

Rank-3 tables exist (66 over F₂, 2,400 over F₃), so the domination needs the second and third cases. The exhaustive check classifies every table into orbits:
```
  p=2: tensors=256 orbits=8 rank histogram={0: 1, 1: 27, 2: 162, 3: 66}
  p=2: unclassified orbits=0
  p=3: tensors=6561 orbits=8 rank histogram={0: 1, 1: 128, 2: 4032, 3: 2400}
  p=3: unclassified orbits=0
```
The independent check written during review covers every table by explicit witnesses instead (sums of two rank-one tensors re-verified as restrictions of Δ(2), and the orbits of W and M), with another irreducible polynomial over F₃, and extends to F₅:
```
  p=5: tensors=390625  rank<=2 (explicit sums)=225505 (restriction re-check failures=0)  |orbit W|=69120  |orbit M|=96000  W in rank<=2: False  M in rank<=2: False  orbits W,M disjoint: True  uncovered=0  (x^2-0x-2 irreducible: True)
```

**Corollary B (the dual inequality reads nothing).** Every dual certificate must exclude the all-GHZ assignment, which by Lemma A has the largest right side of (D) at every placement. So the dual method excludes G exactly when it excludes (G, all-GHZ), whose right side log 2·Σ_v δ(y_v) depends on the topology only. On random networks with 3 to 7 vertices and flattening rank across a cut as the spectral point, neither inequality is ever violated, and the actual tables often give a smaller right side than all-GHZ, which no certificate can use:
```
  p=2: (network, cut) trials=2580 dual violations=0 primal violations=0 cases where actual tables give a smaller dual bound than all-GHZ=1389
  p=3: (network, cut) trials=3640 dual violations=0 primal violations=0 cases where actual tables give a smaller dual bound than all-GHZ=1589
```

## Theorem C: one O(N log N) graph for every target

**The graph.** For r = 2^m, G_r is the Beneš network on r inputs in which each 2×2 switch is a K_{2,2} gadget (two in-vertices, two out-vertices, four edges); stage wires join out-vertices to in-vertices, and the leg leaves sit at the r inputs. G_r has maximum degree 3, r(2m−1)/2 switches and r(6m−3) edges, leg edges included. For the dual statement one pendant edge hangs at each output, ending in a degree-1 vertex whose unary table sits at a single site and has price 0.

**Theorem C.** Let k be any field. Take any spectral point, any placement of G_r's vertices (respectively edges), and any nonzero tensor f with r binary legs at the leaves. Then:
- **(a) Primal.** H(f; x) ≤ log 2 · Σ_{e∈E(G_r)} d(e).
- **(b) Dual.** H(f; x) ≤ log 2 · Σ_v δ(y_v), the right side of (D) with all-GHZ tables.
- **(c) Gadgets.** In any inequality of the form (P) for a gadget network whose N-leg boxes are each placed as one tensor at their leg sites, each box may be replaced by a copy of G_N without making the inequality false.

So no lower bound on vol_k(f) that uses the network only through (P) or (D) can exceed |E(G_N)| = N(6 log₂N − 3), or N(6 log₂N − 2) in the dual form, for any target and any field, with or without ports: for f or any restriction of f, singly or averaged, directly or through boxes in gadgets, and for batches f^{⊗j} (j copies of G_N, by additivity). For N not a power of 2, pad to the next one. Part (b) does not use Lemma A, so it holds over every field.

*Proof.* (a) Fix a placement. By Beneš rearrangeability every permutation π is routed by edge-disjoint paths from input x_i to output o_{π(i)}, and the triangle inequality along each path gives Σ_i d(x_i, o_{π(i)}) ≤ Σ_e d(e). Averaging over the r cyclic shifts, some output o\* has Σ_i d(x_i,o\*) ≤ Σ_e d(e), and the transport bound moves every leg to o\*, where the price is 0. (b) Sites are now edges. Where a path passes through v from edge e to edge e′, d(p_e,p_{e′}) ≤ δ(y_v), because Δ_{{p_e,p_{e′}}}(2) is the restriction of Δ_{y_v}(2) by the all-ones functional on the third leg. In a graph of maximum degree 3, edge-disjoint paths share no internal vertex, so Σ_i d(x_i, o_{π(i)}) ≤ Σ_v δ(y_v), and the rest is as in (a). (c) By (a), H(box; y) ≤ log 2·Σ_{e∈G_N} d(e) at every placement of G_N's interior, and price additivity under ⊗ does the rest. ∎

The checks route every permutation at r = 4 and 8 and 2,000 random ones at r = 16 and 32, find edge and vertex cuts of at least min(|A|, |A^c|) between complementary leg sets, exhaustively at r = 4 and 8, and test the metric step on random placements:
```
  r=8: switches=20 vertices=88 edges=120 max degree=3 edges/(r log2 r)=5.000 permutations checked=40320 failures (wrong endpoint or shared edge)=0
  r=8: over all 254 proper leg subsets A: min(edge cut - min(|A|,|A^c|))=0, min(vertex cut - min(|A|,|A^c|))=0  (both must be >= 0)
```
The independent check builds its own graph, routes all cyclic shifts up to r = 32 by its own solver with paths that are also internally vertex-disjoint, and tests both metric steps, the dual one with δ equal to the diameter (the smallest set function the proof allows):
```
  r=32: all 32 cyclic shifts routed; endpoints correct, paths pairwise edge-disjoint AND internally vertex-disjoint: True
  r=32: placements=200 (l2, Cauchy-l2, l1, l_inf grid)  primal: max(min_j sum_i d - sum_e d)=-708, max over shifts=-692  dual (delta=diameter): max(min_j sum_i d - sum_v diam)=-728, max over shifts=-706  (all must be <= 0)
```

**Relation to the published caps.** For a routing restriction, Theorem C matches the ceiling note's Lemma 2 up to constants: both are O(r log r) Beneš topologies with different switch gadgets, and Lemma 2's graph moreover realizes the routings. By (c), the preprint's uniform-destinations lemma (`lem:uniform-demand`), whose proof uses the network only through (P), bounded degree and the edge count, runs verbatim on gadget ∪ k·G_N. This gives |E(gadget)| + k·N(6 log₂N − 3) + O(r) ≥ c·r√log q, the round-three gadget cap's conclusion without its hub-entropy step and with a worse constant, as checked during review. So an evaluation of that lemma that excludes networks only by violations of (P), however sharp its constants, certifies at most O(N log N) internal edges per box.

## What (P) and (D) do not cover

- **Multi-vertex pieces.** A price inequality may place a sub-network with two or more vertices as one tensor. Lemma A's domination then fails: two adjacent trivalent vertices, each holding a wire on two legs and a vector on the shared edge, make wire(a,b) ⊗ wire(c,d), whose price d(a,b) + d(c,d) can exceed δ({a,b,c,d}). The path step of (b) also loses a factor, since a piece with D dangling legs can carry ⌊D/2⌋ edge-disjoint paths, and the one-piece inequality reads all the tables. Whether some O(N log N) graph passes every bounded-piece price inequality is open.
- **Diagonal counting.** The one superlinear exact-network bound in the upstream sources, vol((U*_n)^{⊗k}) > k·n^{1+δ} in characteristics with ports (`thm:batches` in the Hamiltonian-cycle and permanent preprint of the same release, https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026, likewise from a local copy), cannot have a (P) or (D) proof: k disjoint copies of G_n pass (P) for (U*_n)^{⊗k} at every placement. Its proof is a self-referential count, in which the program runs the compressed evaluator on its own description and adds one success, so the two results are consistent. It beats N log N only for a field-valued counting tensor, not for a 0/1 predicate measured in its own length. Only its statement and the structure of its proof were read, during review.
- **Other escapes.** Invariants that are not restriction-monotone or not ⊗-multiplicative, and the ports branch, a substitution argument rather than a price inequality; under one-sided randomized Weak ETH no positive characteristic has ports ([finite-characteristic ports](finite-characteristic-ports-and-weighted-sat.md)), so that residual is empty. Shannon counting over the slices gives at most O(N/log N), since there are at most C(2^w, n) ≤ 2^N distinct slices.

## The fixed-B slices and the smallest cases

For the slices P_B(a) = [a_i ⊕ a_k ∉ B⊕B for all i ≠ k] with N = nw input bits, Theorem C(b) refutes, at C = 6, the natural table-reading lemma that some b-lists B_n with B_n⊕B_n not a subspace make (D) exclude every trivalent topology with at most C·N log₂N edges, for every C (G_N has N(6 log₂N − 2) ≤ 6N log₂N edges in the dual form). Every 3-element B has B⊕B a subspace, so the first genuine non-subspace, non-constant slices have N = 16 input bits:
```
  w=3: 4-sets B=70  B+B not a subspace=56  of these with P_B not identically 0=0  (subspace sumsets with P_B not identically 0=0);  N = 4w = 12
  w=4: 4-sets B=1820  B+B not a subspace=1680  of these with P_B not identically 0=1680  (subspace sumsets with P_B not identically 0=140);  N = 4w = 16
```
Exact minimum networks are out of reach there, so the measures were compared with true minima only at 4 legs over F₂: every topology with at most 5 vertices of arity at most 3, with tables found by CaDiCaL. LB_primal and LB_dual are the fewest vertices of a topology passing every cut-rank inequality of (P), respectively of (D) with all-GHZ tables, and V\* is the true minimum. On the 7 targets tested at this size both are sound and tight, so tiny cases cannot separate table reading from topology:
```
  distinct 2-bit words [x1x2 != x3x4]: pairing ranks=[4, 2, 4]  LB_primal=2  LB_dual=2  V*=2  sound=True  witness topology legs->[0, 1, 0, 1] edges=[(0, 1)]
  random (seed 7): pairing ranks=[3, 3, 3]  LB_primal=4  LB_dual=4  V*=4  sound=True  witness topology legs->[0, 1, 2, 3] edges=[(0, 2), (0, 3), (1, 2), (1, 3)]
```

## The three standard tests

- **(a) Fast solver on the hard family?** Not used: Theorem C holds for every target, from affine-B slices (an O(n)-step RAM) to D_w and SAT itself.
- **(b) 2-SAT?** The cap applies verbatim to 2-SAT functions, as a technique limit must.
- **(c) The relativized clock?** The cap concerns network certificates only; the step that fails under that oracle, the RAM-to-network simulation, is not touched. [Relativized clock](relativized-clock.md)

## Exact obstruction and next step

Reading vertex tables through the single-vertex dual (D) does not let the price method certify more than topology, or more than O(N log N), for P_B: every trivalent binary table is spectrally at most GHZ, and every N-leg target's price is at most the all-to-one transport cost, which G_N carries. This gives nothing toward the RAM bound for SAT; it removes (P), (D), the routing lemma and every variant that reads targets, or single vertex tables, through spectral points, as a source of the exact-network bound for SAT above N log²N that the circuit route needs (§4 of the simulation note). Any proof that vol(P_B) = ω(N log N) must show, with an invariant outside (P) and (D), that P_B is not the contraction of G_N, or of any topology of size O(N log N), for any choice of tables. A first instance is any explicit N-leg 0/1 function not realizable on G_N over F₂; most functions are not, by counting, but at N = 4 every function tested has a network with at most 4 vertices (realizability on G_4 itself was not tested), and the first genuine slice instance is N = 16 on G_16, with 240 vertices.

## What is not proved

- No lower bound on vol(P_B), on any network volume, on RAM time or on SAT.
- Lemma A is proved for finite fields, and the completeness of its case list rests on the stated pencil classification. An extension to all fields was sketched during review and not checked, except that the structure tensor of k[ε]/(ε²), which governs an inseparable quadratic extension, lies in the orbit of W over F₂. Theorem C does not need Lemma A.
- Beneš rearrangeability is a classical fact, cited from memory and not re-derived here; it is checked for every permutation at r ≤ 8, and for the cyclic shifts the proof needs up to r = 32.
- The finite checks use one spectral point, flattening rank across a cut; they test the inequalities and the graph facts, not the theorem for all spectral points. No minimum-network comparison was possible on a genuine non-subspace slice.
- Whether Theorem C appears in the literature was not checked. A search of the journal's notes for spectral points, price inequalities, common-label rates and transport found no statement of it; the related entries are the ceiling note's Lemma 2 and the round-three gadget cap.

## Reproducing the checks

Run from `audits/`; nothing is written outside a temporary directory.
```
python3 -B table_reading_price_checks.py
python3 -B four_leg_minimum_networks.py
python3 -B table_reading_price_independent_check.py
```
The first runs Checks A (Lemma A over F₂ and F₃), B (the graph, routing, cuts and metric step) and C (the two cut-rank inequalities on random networks) in about 18 seconds. The second runs the slice census and the 4-leg minimum networks in about 40 seconds, with CaDiCaL found on PATH or in a Lean toolchain. The third is the independent check written during review, including its F₅ parts, in about 25 seconds. [Checks A–C](../audits/table_reading_price_checks.py) · [Minimum networks](../audits/four_leg_minimum_networks.py) · [Independent check](../audits/table_reading_price_independent_check.py)
