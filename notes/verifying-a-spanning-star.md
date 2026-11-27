# An indexed read inside a minimum spanning tree and an ordinary 3-CNF

Khanna, Putterman and Song use path maxima in a comparison algorithm for minimum spanning trees. Their Theorem 1.1 gives a uniform deterministic linear-time algorithm in the number of edges, using the MST-specific comparison-to-time theorem of Pettie and Ramachandran. Checking a supplied tree was already possible in linear time. Here even the paths of a *fixed spanning star* give different costs on two computational models. A deterministic RAM verifies the star with a read-only input and constantly many registers. The list-volume theorem in the November 24 matrix multiplication preprint implies that bounded-fan-in Boolean circuits need superlinear size in the graph's encoded bit length. The same two bounds apply to one family of ordinary 3-CNFs. [DLMST, Theorem 1.1 and §3](https://github.com/Louiealbp/DLMST/blob/0072335716b145032b418760883daed2a89809db/final.pdf) · [Pettie and Ramachandran](https://www.cs.utexas.edu/~vlr/papers/optmsf-jacm.pdf) · [King on verification](https://www.cs.princeton.edu/courses/archive/fall05/cos528/handouts/A%20Simpler%20Minimum.pdf) · [Source list theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/obstruction.tex)

## A star whose weight is known before the input arrives

Let $N=2^w$ and $M=N^2-1$. There are $N$ stored words $X_i$ and $N$ claims $C_j$, all in $[0,M]$. Addresses $q_j$ are arbitrary indices in $[0,N)$. A claim is correct if $X_{q_j}=C_j$.

Use one root, two data leaves per table position, and two private query leaves per claim. The candidate tree consists of the $4N$ root spokes, always in the same public order. The two data spokes at $i$ weigh $X_i$ and $M-X_i$. The query spokes have weight zero. Add a chord from each query leaf to the data leaf of the same sign at $q_j$, of weight $C_j$ on the positive side and $M-C_j$ on the negative side. These $2N$ chords are distinct even for repeated addresses. Deleting the root leaves a disjoint union of stars and isolated vertices.

The candidate has weight $NM$. In fact, if $S_i=\{X_i\}\cup\{C_j:q_j=i\}$, then

$$
  \operatorname{OPT}=NM-\sum_{i=0}^{N-1}\bigl(\max S_i-\min S_i\bigr).
$$

Every data vertex needs an incident edge, and no edge covers two data vertices. Thus the sum of their individual minimum incident weights is a lower bound. Retain all zero query spokes and one minimizing edge per data vertex to attain it. The two minima for address $i$ sum to $M+\min S_i-\max S_i$. In particular, the star is minimum exactly when every claim is correct. The formula counts the range of values observed at an address even if many claims repeat there. The decision also works with globally distinct weights by appending a unique low-order edge ID to each weight and numbering all spokes before all chords. Each chord can then replace a heavier spoke exactly when its primary weight is smaller. The displayed numeric identity is for the primary weights.

## Where the bit-circuit cost occurs

Write $D_w(X)$ for the indicator that the $N$ records are pairwise distinct. For every $X$, over the integers and hence every finite field,

$$
 D_w(X)=\sum_{q,C}[C_0<\cdots<C_{N-1}]\, [\text{the candidate star is minimum}].
$$

An accepted summand retrieves $N$ different words at $N$ positions of an $N$-entry table. Every position is used. For a table with distinct words the sorted sequence and all its original positions exist and are unique. On a table with a repeated word there is no accepted summand. This counts decision answers once each, independently of how many minimum trees the graph has.

Each graph uses $L=\Theta(Nw)$ bits in an edge list with fixed-width endpoints and weights. Forming it from $X,q,C$ uses copies, constants and bit complements, since $M-u$ complements a $2w$-bit word. Consecutive-pair order tests on $C$ cost $O(Nw)$ bit gates. Turn a bounded-fan-in circuit for star optimality into a tensor network by encoding gate truth tables, splitting fan-outs with equality trees and pinning its output. Internal deterministic wires contribute one evaluation. Summing over the bits of $q,C$ implements the identity, with volume $O(s+Nw)$ for $s$ gates. The preprint's list theorem over a fixed finite field gives volume greater than $2Nw^{1+\sigma}$ for some $\sigma>0$. Hence $s=\Omega(L(\log L)^\sigma)$ along these lengths. The same argument on one all-correct batch output gives $\Omega(tNw^{1+\sigma})$ for $1\le t\le N$, using the exact-product theorem. A single connected graph for the batch can share the root across the disjoint blocks, with identifiers still of $O(w)$ bits. The volume theorem is an external dependency of these consequences. This project has not independently verified its proof.

There is also a version with **one chord per query and just one data spoke per address**. Give each edge a lexicographic integer key, with the last component its unique ID. The keys before the ID are $(X_i,2)$ for data spokes, $(0,0)$ for neutral query spokes and $(C_j,3)$ or $(C_j,1)$ for the private chord to leaf $q_j$. The first choice tests $X_{q_j}\le C_j$ and the second tests $X_{q_j}<C_j$. For fixed $q,C$, sum the optimality bit over the $2^N$ choices, with factor $-1$ per strict test. It factors into the product of the differences of weak and strict indicators, giving precisely the all-correct bit. The switches and signs add $O(N)$ network volume. This version has $2N+1$ vertices, $3N$ edges and distinct weights at every internal setting, including coincident values of $C$. The circuit computes one Boolean verdict on each genuine graph. The reduction performs the signed summation.

## A 3-CNF for a read discrepancy

Split each stored word or claim into two $w$-bit chunks. Use $s_i$ for a table row, $t_{jb}$ for a proposed erroneous query and chunk $b\in\{0,1\}$, and Boolean marks $A_{b,d}$ for chunk values $d<N$. Include the following binary clauses, written as implications.

$$
 s_i\Rightarrow A_{b,X_{i,b}},\qquad
 t_{jb}\Rightarrow s_{q_j},\qquad
 t_{jb}\Rightarrow\neg A_{b,C_{j,b}} .
$$

Require at least one $t_{jb}$. In any satisfying assignment it points to a genuine disagreement, because equality would force the same mark both ways. Conversely, at a disagreement select just that test and its required table row, and mark exactly the two chunks of the row in their respective banks. This satisfies every implication.

The disjunction costs linear size in ordinary 3-CNF. Order the $2N$ test bits as $f_i$, assert $u_0$ and $\neg u_{2N}$, and include $\neg u_i\lor f_i\lor u_{i+1}$ for each position. A chain with a true test can drop to false there. A chain with every test false must propagate true to the last position. Units and binary clauses can repeat literal positions or be expanded with fresh names and all signs to use three distinct variables. The total length stays $\Theta(Nw)$. Banks use consecutive indices and can be aligned at powers of two, so spelling out literal names costs $O(Nw)$ bit wiring. Only variable identifiers change across the family.

There is a second width-at-most-three encoding with only $\lceil\log_3(2N)\rceil$ non-Horn clauses. For each of that many ternary digits, require at least one of its three digit variables by one positive clause. Use a full ternary prefix tree with its root asserted and Horn rules forcing a child whenever its parent and the relevant digit are true. Map the leaves publicly onto all $2N$ tests, repeating tests if necessary, and make each leaf imply its test. At least one leaf is forced. Conversely one can select precisely the digits of a leaf naming a genuine mismatch and activate only its path. The tree has $O(N)$ nodes and the same $O(Nw)$ encoding cost. Before expanding the long disjunction the basic construction has only binary Horn clauses and a single positive clause. Pătraşcu and Williams studied SAT with a Horn part and a few unrestricted-length positive clauses, including its relation to faster exponential algorithms. [Pătraşcu and Williams, Appendix A](https://people.csail.mit.edu/rrw/cnf-sat-feasible.pdf) · [Size of cores for few non-Horn clauses](threshold-cores-with-few-non-horn-clauses.md)

The complement of SAT on this one formula is the all-correct bit in the sum above. A small decision circuit for these formulas would therefore violate the same volume theorem. Its inputs can be restricted to the promised layout and even to strictly increasing claims $C$, since the sum gives every other setting zero weight. No uniqueness promise on SAT assignments is used.

For the native algorithm each query supplies the address of an input row. Read its two chunks directly from the read-only formula and compare with the claim. There are $O(N)$ word operations and $O(1)$ writable words. For a solver required to handle arbitrary SAT, first check the fixed clause layout, field ranges and consistency of repeated fields in $O(N)$ word operations, then use a complete solver on a layout mismatch. The layout uses fixed-width records of $O(1)$ words with constant-time offset calculation. The lookup addresses depend on the explicit query fields alone. One can perform all reads regardless of previous replies and accumulate a single discrepancy bit. On a consistent template, changing the identifier of the forbidden mark for any one test to a different chunk value makes the formula satisfiable. The $2N$ edits occupy disjoint records, with a word meeting only constantly many such edits, also after expansion of the short clauses. A correct general solver must probe a word in each edit on the original rejection. This gives a matching $\Omega(N)$ bound there. Thus the native cost on this family is $\Theta(L/\log L)$.

For each fixed vector of addresses, the needed data bits can instead be connected straight to their comparisons in a circuit of size $O(L)$. The preprint-based lower bound concerns a single circuit handling the variable addresses. This example isolates the cost of changing those connections in a read-only computation with a single verdict. The unrestricted SAT time lower bounds remain open.

The Lean files verify the SAT witness equivalence, the expansion of the choice clause, and existence and uniqueness of the sorted gather witness. The executable audit independently runs Kruskal's algorithm, including strict tests, ties and repeated addresses. The graph optimum and the network-size transfer are proved above. [SAT equivalence](../lean/GatherMismatchCNF.lean) · [Sorted witness](../lean/SortedGatherWitness.lean) · [Kruskal audit](../audits/spanning_star_audit.py)
