# The list-distinctness technique cannot certify more than O(n log n), so the circuit route needs a new lower-bound technique

The tensor-network technique behind the journal's superlinear circuit bound for 3-SAT (the list-distinctness theorem) has two branches, and both are capped at O(n log n) in the number n of input bits whenever the hard instance is obtained by restricting the function under test, or by a constant number of copies plus gadgets routing O(n) bits. That is below the threshold that the circuit route needs, so this route needs a lower-bound technique that is not yet known. The cap is shown here for product checking over F_3, the candidate the simulation note points to, and in general for restriction-type embeddings. This is a statement about one proof technique; it gives no SAT time bound in either direction, and the linear, quadratic and cubic questions remain open. [Simulation threshold](simulating-a-ram-step-by-exact-networks.md) · [Barrier note, route A](what-any-proof-of-superlinear-sat-time-must-get-past.md) · [Circuit bound for 3-SAT](checking-the-sat-circuit-bound.md)

**Notation.**
- n is the number of input bits of the candidate function; for G_d = [AB = C over F_3], n = Θ(d^2).
- N is the DIMACS length of the candidate's SAT projection: N = Θ(d^2 log d) for the journal's mismatch projection, and N = Θ(d^2) = Θ(n) for a linear-length projection (sketched in Section 4, not built).
- c_lin is the run exponent of the simulation note: the simulation exponent for an N-step run on N bits, which is what the circuit route needs. That note shows only σ_k ≤ c_lin ≤ 2. Its bracket c* ∈ [1+σ_k, 2] is for the per-step exponent over all programs, not for c_lin.
- A linear-time SAT RAM therefore gives G_d networks of size about n(log n)^{c_lin+1} with the journal's projection, and n(log n)^{c_lin} with a linear-length one. These are the thresholds of the circuit route.

**Result.** The no-ports hypothesis of the technique holds for G_d. But both branches of the technique are capped at O(n log n) whenever the hard instance is obtained by restricting the candidate (or by a constant number of copies plus gadgets routing r = O(n) bits):
- **No-ports branch:** a Beneš topology of size O(r log r) meets the same routing hypothesis (checked at r = 4 and 8).
- **Ports branch:** a bound of the form "cheap F implies cheap Tag tests" can be no larger than the true cost of Tag, which is O(tNh^2) by sorting.

So, for restriction-type embeddings, the technique never certifies more than O(n log n), for this function or any other.
- That is below the journal-projection threshold n(log n)^{c_lin+1} for every c_lin > 0.
- It is below the linear-projection threshold n(log n)^{c_lin} when c_lin ≥ 1.
- For G_d it is below the threshold for every c_lin, because the restricted family has an O(n)-step RAM (Section 5, Obstruction 1).

The function itself is in two different states:
- **Over coefficient fields of characteristic 3 it is dead against the known simulation (exponent 2), with either projection.** The journal already has an O(d^2 log^2 d) network there. Against a hypothetical better simulation, it stays dead with the journal's Θ(d^2 log d) projection while c_lin ≥ 1, but with a linear-length projection only while c_lin ≥ 2.
- **Over fields of other characteristic it is open.** The upper bound is d^{11/5+o(1)}. The lower bound is Ω(d^2) unconditionally, and Ω(d^2 √log d) if the characteristic has no ports.

The proof chain now needs a lower-bound technique that depends on the characteristic. No such technique is known. In characteristics with ports, none of the embeddings tried yields a bound for G_d (Section 3).

## 1. The technique and the two lemmas

**Source.** Theorem 2.2 and its proof were read in full: `obstruction.tex` and `list.tex` of the 24 November matrix-multiplication preprint (upstream tree at the journal's pinned commit: https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026), from a local copy of its sources whose revision was not compared with that commit. The ports definition is taken from `port-graphs.tex` of the Euclidean-geometry preprint of the same release, read only around Definition `def:ports`. The external results the proof cites, oaG (descent with tagged permutations), oaP (batch bound for U*, price/entropy corollaries) and the Hadamard-space machinery, were **not accessed**. The journal's Lean audit (`upstream-checks/list-distinctness/ListAudit.lean`) covers Theorem 2.2 for D_w only, not any use of the technique on another tensor.

**The technique has two branches, each with its own hypothesis:**
- **(H-np), fields without ports.** This is the uniform-destinations lemma (`lem:uniform-demand`). Suppose a fixed trivalent topology has r input bits and r output bits. Suppose further that for every permutation in the support of a distribution, some choice of vertex tables makes the network realize the r independent wires from each input to its assigned output. If each input's destination is uniform on q ≥ 2 outputs, then the size is Ω(r·√log q).
- **(H-p), fields with ports.** Here the argument needs Tag(h,h)^{⊗t} tests: N = 2^h records with *binary* h-bit tags and h-bit payloads. These must be built from copies of the candidate at overhead O(tNh). The tests are then substituted into the oaG descent, which yields a contradiction with the oaP batch bound vol((U*_ℓ)^{⊗j}) > j·ℓ^{1+δ}.
- That ports depend only on the characteristic is stated in `port-graphs.tex` of the Euclidean-geometry preprint, after `def:ports`. The intro of the Hamiltonian-cycle preprint says "the proof requires no classification of the characteristics". The preprints read do not decide ports for any characteristic.

**Lemma 1 (hypothesis H-np for G_d).** Take any d ≥ 1 and any permutation π of [d]. Pin B := P_π, where P[h][k] = 1 iff k = π(h). Also pin the high bit of the 2-bit code of every entry of A and C to 0. The remaining tensor on 2d^2 bits is then
  [AP = C] = ∏_{i,h} δ(A_{ih}, C_{i,π(h)}).
So for uniform π, the topology of any exact trivalent network for G_d meets (H-np) with r = d^2 and q = d. Consequently, over every finite field without ports, vol(G_d) ≥ c·d^2·√log d. The 4d^2 pin sites are absorbed.

Overlap with the journal:
- The permutation restriction itself is in the balanced-cuts note, section "Permutation restrictions give identity submatrices", where it is used for flattening ranks. [Balanced cuts](balanced-cuts-of-the-binary-product-graph.md)
- The same pin-and-apply use of the uniform-destinations lemma, for tape verifiers, is in the tape-time networks note. [Tape-time networks](tape-time-networks-and-two-types-of-brackets.md)

What is new here is only the application to G_d over F_3, with the high-bit pinning.

**Lemma 2 (ceiling).** For every r = 2^m there is a fixed trivalent topology with 3r(2m−1) = O(r log r) vertices that meets (H-np) for **every** permutation of r bits. Hence no lower bound derived from (H-np) alone can exceed O(r log r). The general form of this cap, for every N-leg target, every spectral point and every field, covers the price inequality itself and its table-reading single-vertex dual: [the price-inequality note](the-price-inequality-and-its-table-reading-dual-cannot-certify-more-than-n-log-n.md).
- Scope: the cap covers restrictions, where r is at most the number of inputs. It also covers gadget reductions that use a constant number of copies and route r = O(n) bits, such as the preprint's own two-copy D_w construction in `list.tex`. It is not shown for embeddings that route r ≫ n bits.
- Overlap: the cap generalizes the σ ≤ 1 remark in the list-and-matrix-costs note. The Beneš construction itself appears in the fixed-routing note. A search of the journal's notes during review found no note stating that a Beneš topology meets the lemma's hypothesis. [List and matrix costs](list-and-matrix-costs-for-ram-and-tapes.md) · [Fixed routing controls](fixed-routing-controls-and-the-unrestricted-sat-clock.md)

The ports branch has an even simpler cap, needing no analysis of embeddings. Its conclusion "vol(F) is large" comes from "cheap F implies cheap Tag(h,h)^{⊗t}", so it can never exceed the true cost of Tag(h,h)^{⊗t}. That cost is O(tNh^2): AKS sorting of N records of width O(h), plus equality checks. The journal already records σ ≤ 1 for this reason in the list-and-matrix-costs note. So for restriction-type embeddings both branches stop at O(n log n).

**Lemma 3 (hypothesis H-p for G_d).** No linear-overhead construction of binary-tag Tag(h,h) tests from copies of G_d was found; the obstruction is in Section 3.

## 2. Checks

**Lemma 1, exhaustive.** `python3 f3_product_permutation_restriction_check.py` prints: [f3_product_permutation_restriction_check.py](../audits/f3_product_permutation_restriction_check.py)
```
d=2: (pi,A,C) triples checked=512 mismatches=0 destination counts of A-bit(0,0) over all pi: {0: 1, 1: 1}
d=3: (pi,A,C) triples checked=1572864 mismatches=0 destination counts of A-bit(0,0) over all pi: {0: 2, 1: 2, 2: 2}
rank of one F_3-entry equality on 2-bit codes: 3 (a bit-wire pair would have rank 4)
```
- The last line shows why the high bits must be pinned. Without that, an F_3 entry routed to an F_3 entry is a rank-3 relation on 2-bit codes, not two bit wires.
- The proof for all d is one line: (AP)_{ik} = Σ_h A_{ih}[k = π(h)] = A_{i,π^{-1}(k)}. Entries in {0,1} are unchanged by reduction mod 3.
- Applying `lem:uniform-demand` relies on the preprint's proof as written, together with the external price and entropy results that were not accessed.

**Lemma 2, exhaustive at r = 4 and 8.**
The switch gadget is a fixed topology of three stages u←u⊕v, v←u⊕v, u←u⊕v. Each stage has one arity-3 copy vertex and one arity-3 vertex whose table is either XOR (giving swap) or "output = first input" (giving identity). Composing switches in a Beneš layout gives the topology. The vertex tables are the only thing that changes with the permutation, which is exactly what the lemma's hypothesis allows.
`python3 benes_routing_hypothesis_check.py` (about 5 s) prints: [benes_routing_hypothesis_check.py](../audits/benes_routing_hypothesis_check.py)
```
switch gadget: pass tables give identity: True | XOR tables give swap: True
r=4: stages=3 switches=6 trivalent vertices=36 permutations realized=24 of 24
r=8: stages=5 switches=20 trivalent vertices=120 permutations realized=40320 of 40320
```
- The tensor contraction is over the integers with 0/1 tables, so it holds in every field.
- For all r, Beneš rearrangeability is classical (Beneš 1964, Waksman 1968; cited from memory, not re-read).
- A Beneš topology of size O(r log r) meets the lemma's hypothesis, so no sharper spectral analysis can push the lemma past O(r log r). Its own proof gives r·√log q, and the √log comes from the Hadamard-space entropy bound.

**The characteristic-3 network, the cell identity.**
`python3 char3_product_cell_identity_check.py` prints: [char3_product_cell_identity_check.py](../audits/char3_product_cell_identity_check.py)
```
d=1: cells checked=27 mismatches=0 choices per cell=5
d=2: cells checked=243 mismatches=0 choices per cell=10
d=3: cells checked=2187 mismatches=0 choices per cell=17
```
- The identity is [a·b = c] = 1 − (a·b − c)^2 over F_3, expanded into 1 + (d+1)^2 selector choices. Each choice requests at most two A-entries and two B-entries.
- With one sorted lookup batch per bank, this is the journal's O(d^2 log^2 d) network over every field of characteristic 3: the matching-characteristic note, section "Many factors and any fixed input field", and the Lean statement `cell_indicator` in `upstream-checks/MatchingCharacteristicProduct.lean`, which needs Mathlib and was not run here. [Matching-characteristic networks](matching-characteristic-networks-for-binary-products.md)

## 3. Why the ports branch does not reach G_d (the Lemma 3 obstruction)

- In G_d the only data-dependent routing is linear. With A a 0/1 matrix having one 1 per row, AB = C checks C_{i,·} = B_{j_i,·}.
- So the tag j_i enters as a **one-hot row of A**: d entries per record. Tag(h,h) with N records needs d ≥ N columns, so N^2 exterior wires of A per instance.
- The (H-p) budget is O(N·h^{1+σ}) per instance. Every exterior wire of the G_d network has to be produced by the gadget, so this embedding is off by a factor of about N/h.
- Rectangular shapes, (N×N)·(N×h), do not help: the N×N one-hot part remains.
- A multi-level selection by several product checks needs intermediate witness tables of N^{1+Ω(1)} bits in the variants tried. There is no proof that every embedding fails. This is a gap, not a theorem.
- **Net effect:** for G_d, the technique gives Ω(d^2 √log d) only conditionally, in characteristics without ports. In characteristics with ports, none of the embeddings tried yields a bound. Even if an embedding were found, the cap of Lemma 2 would hold the result to O(n log n).

## 4. Conversion to SAT length, and the three standard tests

- **With the journal's projection.** Its mismatch projection has N_SAT = Θ(d^2 log d), because every input entry becomes a literal pin with a Θ(log d)-bit name. The conditional bound d^2·√log d is then Θ(N/√log N), below the trivial Ω(N). The ceiling O(d^2 log d) becomes O(N). A SAT circuit of size s gives G_d networks of size O(s + N), so even the true G_d volume transfers only after subtracting O(d^2 log d). [Matrix products from SAT](verifying-matrix-products-from-sat.md) · [List and matrix costs](list-and-matrix-costs-for-ram-and-tapes.md)
- **With a linear-length projection.** The circuit route requires one. A chunk-flag version, like the dense list projection of the circuit-bound note (its Section 3), looks possible (sketch, **not checked**):
  - Select row i and column k with one-hot selectors.
  - Read A's row i and B's column k through banks of flags whose names spell chunks of b = (log_3 d)/4 entries. This uses d^2/b data clauses.
  - Read C's row in chunks the same way, and extract C_{ik} with about d·3^b = d^{5/4} gates.
  - Compute each chunk's partial dot product from a flag-pair table of 9^b = d^{1/2} gates per bank, d^{3/2}/b in all.
  - In total that is O(d^2/log d) clauses, i.e. Θ(d^2) bits.
  - Even then the conditional bound is Ω(N √log N) and the ceiling is O(N log N). Both are at most the threshold N(log N)^{c_lin} once c_lin ≥ 1. As defined in the Notation block, c_lin is the exponent for an N-step run on N bits, which is what the circuit route needs. The simulation note shows only σ_k ≤ c_lin ≤ 2 for it, so c_lin ≥ 1 is not settled; its bracket c* ∈ [1+σ_k, 2] is for the per-step exponent over all programs.
  - For G_d the ceiling needs no condition on c_lin (Section 5, Obstruction 1).
- **(a) Is there a fast globally correct solver for the hard family?** Yes. The pinned family (A, P_π, C) is a routing check that a RAM decides in O(n) steps by indirect addressing. For general G_d, the best known deterministic upper bound is d^{ω+o(1)}; Freivalds gives O(d^2) randomized. A RAM consequence would therefore have to come through the circuit simulation, and the ceiling is below that threshold.
- **(b) Does the same argument give the same bound for an easy language like 2-SAT?** It fails this test. The restricted tensor ∏ δ(x_i, y_{π(i)}) is an equality system, a 2-CNF, so the argument uses nothing specific to NP-hardness. No network bound for 2-SAT in DIMACS length was computed. The journal's tape-time bound for 2-SAT is only an analogy, in a different model. [Tape time under complement](tape-time-under-complement.md)
- **(c) Does it survive the oracle of the relativized-clock note?** The network bound itself is not contradicted by that oracle. The transfer from a linear SAT RAM to small circuits breaks there, because one query reads Θ(n log n) bits. So the route uses the O(w)-bits-per-step property as required. That is irrelevant here because of the ceiling. [Relativized clock](relativized-clock.md)

## 5. Exact obstruction and next step

**Obstruction.**
1. **The ceiling.** Hypothesis (H-np) is met by Beneš topologies of size O(r log r), checked for Lemma 2. The ports branch is bounded by the O(tNh^2) cost of Tag. Hence any lower bound this technique obtains from restrictions of the candidate is O(n log n) in the number n of input bits.
   - **For G_d this holds independently of c_lin.** The restricted family (A, P_π, C) is decided by a RAM in O(n) steps (test (a)). So any bound obtained through it is at most the cost of simulating a linear-time RAM with the same simulation. It therefore never exceeds the threshold, whatever the simulation exponent is. The Beneš network gives the explicit value O(n log n). The simulation note (Section 4, "Families") makes the same point. [Simulation threshold](simulating-a-ram-step-by-exact-networks.md)
   - **For an arbitrary function F** with no RAM-easy restricted family, only the Beneš cap remains. The condition c_lin ≥ 1 (linear-length projection) is then the correct one.
2. **No embedding found for the ports branch.** (H-p) needs binary-tag Tag tests, and G_d supplies tags only one-hot: N^2 against a budget of N·h^{1+σ}. In characteristics with ports, none of the embeddings tried yields a bound for G_d.

**Design constraint for any future technique** (weaker than fact 1, not an obstruction). Theorem 2.2 is uniform over all finite fields, and G_d has O(d^2 log^2 d) networks in characteristic 3. So a lower bound above d^2 log^2 d for G_d must use a characteristic other than 3 *essentially*. Neither branch distinguishes characteristics; they distinguish only ports.

**The listed alternatives die by explicit cheap networks, not by the ceiling:**
- Transpose checking [B = A^T] is d^2 fixed equality wires: volume O(N) over every field.
- A word-sorting check costs O(n log n): AKS plus adjacent equalities.
- List distinctness costs O(n log n) (journal).
- Matrix-product checking over F_p in characteristic p costs O(d^2 log^2 d).

The first three are below N·log^{c_lin} N once c_lin ≥ 1. The characteristic-p matrix check is below it once c_lin ≥ 1 with the journal's projection, but needs c_lin ≥ 2 with a linear-length projection. Against the known simulation (exponent 2) all four die. So the only surviving candidate of this kind is cross-characteristic product checking, for example [AB = C over F_3] with networks over F_2, or the binary product with odd-characteristic networks. Its upper bound is d^{11/5+o(1)}. The journal's obstruction notes there bound only specific implementations: static signings, d^{27/13}; three-bank rank, (9/8)D. [Signed block products](signed-block-products-over-odd-characteristic.md) · [Three-bank rank](three-bank-rank-of-the-binary-matrix-verdict.md)

**Next lemma, open.** A characteristic-sensitive lower bound: vol_{F_2}([AB = C over F_3]) ≥ d^2·(log d)^K for some K > c_lin + 1 with the journal's Θ(d^2 log d) projection, or K > c_lin with a linear-length projection. Here c_lin is the run exponent from the Notation block, known only to lie in [σ_k, 2]. A linear SAT RAM gives G_d networks of size about d^2 (log d)^{c_lin+1}, respectively d^2 (log d)^{c_lin}. Without an improved simulation, K > 3, respectively K > 2, is needed. This would be a network analogue of Razborov–Smolensky: char-2 sums must simulate mod-3 counts. No technique for it is known here.

The only polynomial lower bound inside `list.tex` is the oaP batch bound for U*_ℓ in characteristics with ports. U*_ℓ is a field-valued counting tensor, not a 0/1 predicate in NP, so it cannot be projected from SAT.

## 6. What is not proved

- The (H-np) bound for G_d is conditional on the field having no ports, and rests on the preprint's unaccessed external lemmas.
- There is no proof that *every* embedding of binary-tag Tag tests into G_d costs N^{1+Ω(1)}. Only the one-hot, rectangular and naive multi-level variants were checked.
- The linear-length SAT projection of [AB ≠ C over F_3] is a sketch, not built or tested.
- The ceiling covers lower bounds obtained from (H-np) through restrictions with r ≤ n, and through constant-copy gadget reductions routing r = O(n) bits. A compressing embedding of a much larger routing problem (r ≫ n) into G_d is not excluded by this argument, though none is known. For G_d specifically, any family the technique uses that is decided by an O(n)-step RAM is capped at the threshold regardless of c_lin.
- No lower bound for G_d beyond Ω(d^2) unconditionally, or Ω(d^2 √log d) conditionally on no ports, is proved here. None follows for SAT RAM time.

## Reproducing the checks

Run from `audits/` (the second and first need NumPy):

```
python3 f3_product_permutation_restriction_check.py
python3 benes_routing_hypothesis_check.py
python3 char3_product_cell_identity_check.py
```
