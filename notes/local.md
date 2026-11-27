# Can monotone clause-selector lower bounds transfer to RAMs?

## First attempt — force an internal computation to respect clause deletion

Fix a CNF template. The answer to SAT changes monotonically when clauses are disabled. The candidate lemma asserted that a fast algorithm on such a family gives polynomial-size monotone circuits for its function of the enable bits (orient each input so that 1 makes satisfiability easier).

Bipartite perfect matching refutes the lemma. For a bipartite graph with two sides of size k, let zᵢⱼ indicate a chosen edge. Require at least one chosen edge in each row, at most one in each column, and forbid zᵢⱼ if the input edge (i,j) is absent. The last condition is a unit clause which is dropped, or replaced by a tautology in a fixed-width slot, when the edge is present. Since there are k rows and k columns, any solution chooses exactly one edge per row and column. The long row clauses can be split into width-three clauses with fresh variables. Pairwise exclusions suffice for the column constraints. Each input graph has a fixed-format 3-CNF whose satisfiability is exactly the matching function.

A RAM scans the promised template in O(N) time for N encoded bits and decides perfect matching using at most k augmenting-path searches of O(k²) time each. Since N ≥ k², this is O(N + N^{3/2}). Meanwhile the monotone circuit complexity of the bipartite matching function is superpolynomial in k, and the template has polynomial length in k. This contradicts the proposed transfer even from subquadratic time on a promised selector family. Extending a solver of the promised family to all of SAT is unnecessary for this counterexample to the family-wise lemma. [Matching lower bound and previous results](https://arxiv.org/abs/2507.16105)

## Second attempt — allow a short summary of nonmonotone information

Fix m ordinary input bits x. Give a monotone decoder the additional b bits h(x), where h is deterministic and can be nonmonotone. Ask when this decoder can produce all complements of the original inputs. Write x ≤ y for coordinatewise order.

**Criterion.** A monotone decoder producing the complements exists exactly when every strictly comparable pair x < y has h(x) ≰ h(y).

For necessity, any coordinate going from 0 to 1 has a complement going from 1 to 0. If both parts of the decoder input were nondecreasing, monotonicity would forbid this. For sufficiency, set output i on arbitrary (x,u) to 1 iff some t ≤ x has h(t) ≤ u and tᵢ = 0. This is monotone in both arguments. On (x,h(x)) each eligible t must equal x. This constructs a finite monotone circuit, with no general size guarantee. A maximal chain in the m-cube has m+1 vertices, so the criterion requires 2ᵇ ≥ m+1.

**Efficient upper bound.** Take b = ⌈log₂(m+1)⌉ and let h(x) be the b-bit unsigned representation of (2ᵇ−1)−|x|. A RAM can compute this word in O(m) steps by addition. The summary strictly decreases numerically up each chain. For an explicit efficient decoder, sort the original bits into descending order with a Boolean comparator network of O(m log²(m+1)) comparators (pad with zeros to a power of two). Output j of the sort is 1 iff |x| ≥ j, for positions numbered from 1. Its complement is the threshold h(x) ≥ 2ᵇ−j. A comparison of b binary bits to a fixed constant is monotone in these bits and costs O(b) gates by scanning the threshold bits, recursing on the suffix and using AND for a 1 threshold bit and OR for a 0 threshold bit (the empty suffix gives true). Padded positions j > m have complement 1.

Reverse the network, retaining all the forward wire values. At a comparator with inputs a,b and outputs H = a ∨ b, L = a ∧ b, recover ¬a as ¬H ∨ (b ∧ ¬L) and ¬b as ¬H ∨ (a ∧ ¬L). Thus the decoder obtains every negated input using O(m log²(m+1)) monotone gates. At each gate of an arbitrary AND/OR/NOT circuit of size s it can then propagate both polarities in O(1) gates by De Morgan's laws. A single word of computed nonmonotone information is therefore sufficient for an O(s + m log²(m+1)) monotone decoder for any such circuit. Counting nonmonotone summary words cannot yield the desired lower bound.

The classical negation-limited inverter literature already gives efficient ways to compute all complements using few NOT gates and sorting networks. Here the summary is supplied by preprocessing, so the circuit model differs. The elementary constructions and obstructions in these notes carry no priority claim. [Fischer](https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-065.pdf) · [Beals, Nishino and Tanaka](https://epubs.siam.org/doi/abs/10.1137/S0097539794275136)

## Third attempt — charge for the inputs on which optimal summaries depend

**Rigidity at saturation.** Suppose m = 2ᵇ−1 and the b-bit summary meets the criterion. Then h depends only on Hamming weight. Every maximal chain contains all 2ᵇ codes, each once. Swap two adjacent insertions in the permutation specifying a chain. The resulting chains are identical except at one position. The missing code at that position is uniquely determined by the common positions. Thus the two possible subsets at the changed level have the same code. Any equal-size subsets differing in one element occur as the two middle possibilities in such a swap. All subsets of a fixed size are connected by a sequence of such exchanges. This proves the claim.

The codes taken at ranks 0 through m must therefore form a reverse linear extension of the Boolean order on b bits. Conversely every such listing meets the criterion. For b ≥ 1 every code bit changes at some pair of adjacent ranks, since every code occurs. For each chosen input coordinate i there is a chain adding i between those ranks. Hence each summary bit depends on every input coordinate. Producing even this full dependence costs just O(m) in the weight construction. It supplies no superlinear RAM lower bound.

**Failure of stability after one spare code.** Take b ≥ 2 and m = 2ᵇ−2. Start with the 2ᵇ codes in strictly decreasing numerical order. Give each rank one successive code, except the middle rank r=m/2 which gets two successive codes. Give either code to each of the rank-r points independently. Any strictly comparable inputs have different ranks with strictly decreasing numerical codes. Hence the criterion holds. The 2^{binom(m,r)}−2 nonconstant middle-layer choices give that many distinct nonsymmetric summaries using just one spare code. This shows why a direct perturbation of the exact rigidity claim fails. The construction proves existence of a decoder and does not bound its size or the time to compute a chosen arbitrary partition.

**A bound that survives slack.** If J is a set of j summary bits, and U is the union of their input dependency sets, freeze U to any fixed assignment. On the remaining m−|U| coordinates there is a chain of length m−|U|+1 on which the j chosen bits are constant. Distinct codes along that chain require m−|U|+1 ≤ 2^{b−j}. This applies to arbitrary nonlinear preprocessing. A fast RAM can give every bit full dependency by sharing one weight computation. To revive a locality-based argument one would need a SAT family whose relevant global summaries are expensive jointly to compute, even with reusable workspace.

## Checks

Lean 4.19.0 checks the general monotone-decoder equivalence, the forced-slot exchange step, and both comparator-reversal identities in `local_summary.lean`. The full combinatorial rigidity and gate-size proofs above are on paper. Python 3's `local_experiment.py` enumerates all maps from the m-cube to two bits for m = 2,3. It finds 8 valid maps (6 symmetric) at m = 2 and 2 valid maps (both symmetric) at m = 3. The script also checks 16 middle-layer partitions at m = 6. These computations check small instances of the claims.

```sh
lean local_summary.lean
python3 local_experiment.py
```
