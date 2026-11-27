# Static cuts of a SAT computation

## 2026-11-23 · First attempt

Suppose a SAT encoding has $k$ independently variable bit positions. Hold the other positions fixed. For a bipartition $S,T$ of these positions, form the real matrix with entries $M_S(a,b)=(-1)^{f(a,b)}$, where $f$ is the satisfiability bit. A deterministic two-party protocol of cost $c$ whose leaves specify the output partitions this matrix into at most $2^c$ monochromatic rectangles. Each signed rectangle indicator has rank at most one. Thus $c$ is at least the base-two logarithm of the rank.

I tried to obtain a RAM time lower bound by forcing this communication cost on *every* partition with both parts of size at least $k/3$, then accumulating the costs. The same input word can contribute to many hypothetical protocols. The following SAT restriction realizes that failure even when every balanced partition has linear communication cost.

Take a simple bounded-degree edge expander $G$ on $k$ vertices, of maximum degree $D$, and use the Boolean function
$$
 f_G(x)=\bigoplus_{uv\in E(G)} x_u x_v .
$$
Bounded-degree expander families exist for infinitely many sizes. Starting from a bounded-degree expander multigraph also works. Delete loops and merge parallel edges. Each cut retains at least its original crossing multiplicity divided by the degree bound. [James R. Lee, *On expanders from the action of GL(2,Z)*](https://arxiv.org/abs/1301.6296)

Write $A$ for the binary crossing adjacency matrix with rows indexed by $S$ and columns by $T$. Contributions of edges internal to $S,T$ multiply rows and columns of $M_S$ by signs. The remaining row indexed by $a$ is the character $b\mapsto(-1)^{(A^\top a)\cdot b}$. Distinct characters are orthogonal. The number of distinct rows is $2^{\mathrm{rank}_{\mathbb F_2} A}$, so
$$
 \log_2\mathrm{rank}_{\mathbb R}M_S=\mathrm{rank}_{\mathbb F_2}A .
$$
The same identity occurs in the Schmidt-rank formula for graph states. [Hein, Eisert and Briegel, *Multi-party entanglement in graph states*](https://arxiv.org/abs/quant-ph/0307130)

If the cut has $e$ edges, select one crossing edge $uv$, and discard all crossing edges with an endpoint in the crossing neighborhood of $u$ or $v$. At most $2D^2$ edges are discarded in each round. The selected edges form an induced matching in the bipartite crossing graph, of size at least $e/(2D^2)$. Their endpoints give an identity submatrix. Expansion gives $e=\Omega(k)$ on every balanced cut, so every such cut has log rank $\Omega(k)$.

For the SAT embedding, use $k$ input-unit clauses in vertex order, one AND gate for each edge, a chain of XOR gates to sum the edge outputs, and a unit clause requiring the final output to equal one. Encode each gate equation by forbidding its inconsistent truth-table rows, at most four clauses of width at most three per binary gate. Repeat literals if the encoding requires three slots per clause. Keep each independent sign in a single slot by using width-at-most-three syntax for the input units, or treat a repeated unit sign as a single logical parameter. On the promised family only the input signs vary. Every gate value is forced once these signs are supplied. This formula has $O(k)$ clauses and $N=\Theta(k\log k)$ bits in fixed-width binary literal encoding.

There is one uniform promise decider for all such graphs. The formula stores its edges in the gate definitions. Read the units, evaluate the listed gates in topological order using an array of bits, and return the last gate. Scanning and accessing this word-aligned encoding costs $O(k)$ operations for words of $\Theta(\log N)$ bits. Repeated fixed signs, if present as padding, do not affect the promise. Thus the candidate inference from all balanced cut ranks to superlinear time fails even on a satisfiability restriction with a uniform evaluator. The argument gives no time upper bound for off-promise SAT.

## Second attempt · Fractional cut weights

Allow a distinct nonnegative weight $w_C$ on every static cut of the $k$ variable terminals. To account for multiple charging, require the sum of weights of cuts that separate any pair of terminals to be at most one. For every Boolean function of these terminals,
$$
 \sum_C w_C\log_2\mathrm{rank}_{\mathbb R} M_C \le k-1
 \qquad(k\ge 1).
$$
Choose any terminal as a hub and orient each cut so its side $U_C$ excludes that hub. The logarithm of the rank is at most $|U_C|$ by matrix dimension. Exchanging the two finite sums, the total is at most the sum over nonhub terminals of the load separating that terminal from the hub. Each contributes at most one. This proof allows arbitrary real weights and arbitrary preprocessing by the Boolean function. The packing hypothesis specifies exactly which class of charges this argument covers.

The linear order is attained already for $k$ even by the matching function $\bigoplus_{i=1}^{k/2}x_{2i-1}x_{2i}$. Give equal weight to all ordered balanced cuts and normalize by the number $L=2\binom{k-2}{k/2-1}$ separating a fixed pair. Every matched pair gets load one. The log rank at each cut equals the number of matching edges crossing it by the character calculation. The sum is exactly $k/2$. Evaluating this function takes linear time.

## Third attempt · Can proximity to the ceiling characterize hard inputs?

The matching gives about half the cap. I tested a stronger criterion that asks for a score within any prescribed fraction of the cap. Even a disjoint union of fixed gadgets achieves this with a linear-time promise decider.

Fix a block size $b$ and an even number $k$ divisible by $b$. Partition the input terminals into $k/b$ blocks. Within each block include every possible edge independently with probability one half and include no edges between blocks. Use the same quadratic phase and uniform weighting of balanced cuts as above. For a uniformly random such cut, the number $H$ of left vertices in any block has mean $b/2$ and variance $b(k-b)/(4(k-1))$. Hence the expected minimum of the two side sizes in that block is at least $b/2-\sqrt b/2$, by Cauchy–Schwarz.

Condition on the cut and put $h=\min(H,b-H)$. The block's crossing adjacency, transposed if necessary, is a uniform binary matrix with $h$ rows and $b-h$ columns. The expected number of vectors in its left kernel is $1+(2^h-1)2^{-(b-h)}<2$. Jensen's inequality for the logarithm gives expected left nullity less than one. Its expected rank therefore exceeds $h-1$. Crossing ranks add across blocks because the matrix is block diagonal after row and column permutations. The ratio of the number of balanced cuts to the pair load $L$ is $2(k-1)/k$. Averaging over the graph and then taking one realization gives a normalized score greater than
$$
 (k-1)\left(1-\frac1{\sqrt b}-\frac2b\right).
$$
For every fixed positive tolerance, a fixed $b$ suffices to obtain its complementary fraction of the cap at arbitrarily large $k$. The CNF lists $O(kb)$ gates, so for fixed $b$ the uniform promise evaluator still takes $O(k)$ word operations. Only the existence of good graph choices uses averaging. Their evaluation uses the graph written into the instance. Some balanced cuts respecting the blocks have zero rank. This variant attacks near-saturation of the aggregate, while the expander example attacks the requirement that every balanced cut be individually difficult.

## Fourth attempt · Require both near-saturation and large rank on every balanced cut

The block construction can satisfy both demands in the same graph. Choose $b$ even, let $B$ run through the sizes of a bounded-degree expander family, and set $k=bB$. In each block designate one center, connect it to every leaf, and sample independent fair edges between leaves. Connect centers according to the expander on $B$ vertices, of edge expansion $h_0>0$. The maximum degree is bounded by a constant depending on $b$.

Take a cut with at least $k/3$ vertices on each side. If at least $k/6$ leaves lie on the opposite side from their center, the star edges already give $k/6$ crossings. Otherwise make every leaf agree with its center. Fewer than $k/6$ vertices move, so each side then contains at least $k/6$ vertices and hence at least $B/6$ centers. The center cut, which never moved, has at least $h_0 B/6$ crossing edges. The induced-matching argument in the first attempt gives log rank $\Omega_b(k)$ for every balanced cut, for every choice of the random edges.

For the average score, delete all center rows and columns from each crossing matrix. Its rank dominates that of the remaining block diagonal leaf matrix. In each block the preceding hypergeometric and kernel estimates apply to the $b-1$ leaves, giving expected rank greater than $(b-1-\sqrt{b-1})/2-1$. For some choice of leaf edges the normalized score exceeds
$$
 (k-1)\left(1-\frac{3+\sqrt{b-1}}b\right).
$$
Thus both conditions together hold for an arbitrarily high fixed fraction of the ceiling on encoded instances with a linear-time promise evaluator. The implicit constant in the minimum cut rank may depend on that fraction. The proof uses elementary cut counting and the graph-state rank identity. Nguyen and Oum study the closely related expectation over unrestricted random vertex subsets. Their definition averages over cardinalities, whereas the pair normalization here uses subsets of size exactly $k/2$. Priority for the combined construction is unresolved. [Nguyen and Oum, *The average cut-rank of graphs*](https://arxiv.org/abs/1906.02895)

## Checks and remaining question

`python3 transcript_experiment.py` exhausts the 70 and 12,870 ordered balanced cuts of the 3-cube and 4-cube. The observed binary-rank histograms were respectively `{2:14, 4:56}` and `{4:158, 5:976, 6:5272, 7:3328, 8:3136}`. It independently checks the sign-matrix ranks by exact rational elimination for every 3-cube cut. The two normalized scores are $63/10$ and $10691/858$, below the corresponding bounds 7 and 15. These finite graphs serve as arithmetic checks.

`lean CutPacking.lean` under Lean 4.19.0 checks the finite-sum double-counting lemma for natural charges and scores. To instantiate it for rational weights, clear denominators and use the integral cut score $|U_C|$ as an upper bound for log rank. The real-weight passage is justified directly by finite sums above. The Lean file covers the counting lemma only.

An unresolved route is to force information across a succession of time-dependent boundaries *after conditioning on what earlier stages retained*. The expander algorithm retains all input bits and reuses them. Any extension must account for those stored bits at later boundaries and prove cumulative fresh work despite their availability. The static family of input cuts and the fractional packing defined here contain no such premise.
