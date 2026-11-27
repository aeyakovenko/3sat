# How much of matrix-product parity can a minimum spanning tree convey?

Khanna, Putterman and Song prove a linear comparison bound for minimum spanning forest and use the problem-specific Pettie–Ramachandran theorem to obtain a uniform linear-time algorithm. Their repository at 0072335 contains manuscripts. The theorem below uses the cycle criterion for optimality, which predates their preprint. The point of revisiting DLMST is to allow graph weights that already depend jointly on two whole matrices, and to test what survives *after* the resulting tree has been revealed. [Primary paper, §§2–4](https://arxiv.org/html/2611.31187v1) · [Pinned repository](https://github.com/Louiealbp/DLMST/tree/0072335716b145032b418760883daed2a89809db) · [Pettie and Ramachandran](https://web.eecs.umich.edu/~pettie/papers/jacm-optmsf.pdf)

Let three independent uniform binary $d\times d$ matrices be $A,B,Z$, and let $M=\mathrm{tr}(ABZ)$ in $\mathbb F_2$. Fix a connected public graph $G$ with $v$ vertices, $m$ edges and $\tau$ spanning trees. Each edge has a designated owner $AB,BZ$ or $ZA$. Its totally ordered integer key in $[0,2^w)$ can be an arbitrary function of that owner's two matrices. Include edge IDs in the keys if needed for uniqueness. Compute the minimum tree $T$. At each possible tree allow a different binary trilinear prediction $U_T$ of geometric border rank at most $s$, and arbitrary signs depending on pairs of matrices. The prediction is the product of those signs and $(-1)^{U_T}$. Put $g=(d-s^{4/9})_+$.

The absolute sign correlation with $(-1)^M$ is bounded by
$$
 \min\{1,\ \tau\,[C(w+1)]^{2(v-1)}\,2^{-\Omega(g^2)+O(1)}\}.
$$
In particular, constant success advantage with $s=d^{2+o(1)}$ requires
$$
 \log_2\tau + O(v\log_2(w+1))=\Omega(d^2).
$$
The rank estimate uses the external matrix exponent. For $s=0$ the same quadratic right side follows without that preprint. The exponent depends on the **logarithm of the key width**, even though a key itself can contain $w$ bits.

## Checking a single certificate

For a proposed tree $T$, delete one tree edge $e$. Every non-tree edge crossing the resulting cut is a potential replacement. The tree is minimum exactly when every such replacement is heavier than $e$, simultaneously for all $e$ (unique keys). Separate the replacements into the three fixed ownership groups. For each nonempty group compute the minimum replacement key. For a fixed $T,e$ this is a function of two matrices, independent of which tree is actually optimal. Thus at most two cross-owner comparisons per tree edge suffice. Checking the third, same-owner group costs one bounded function of a pair. This step works even if exponentially many different orders of the non-tree edges are possible.

For keys $x,y\in[0,Q)$, $Q=2^w$, the comparison $[x<y]$ is the interval indicator $[1,Q-1](y-x)$ on the cyclic group of order $2Q$. Expand that indicator in normalized Fourier characters. Each summand is a product of a function of $x$ and a function of $y$, both of modulus one. The sum of the absolute coefficients is at most $C(1+\log Q)$. Indeed the constant coefficient is at most one, and the geometric sum at frequency $j\ne0$ has normalized absolute value at most $1/(2Q|\sin(\pi j/(2Q))|)$, up to a universal factor of two. Summing the symmetric harmonic bound proves the assertion. Multiplying all the comparisons therefore expresses the tree indicator as a sum of products of bounded pair functions, with total absolute coefficient at most $[C(w+1)]^{2(v-1)}$.

For any such product $P$, three applications of Cauchy–Schwarz give
$$
 |\mathbb E P(-1)^{M-U_T}|^8
 \le \mathbb E(-1)^{(M-U_T)(A,B,Z)}.
$$
The eighth-power calculation takes one difference in each input block, which leaves the trilinear form evaluated on independent uniform differences. The right side is at most $2^{-\Omega(g^2)+O(1)}$ by the accompanying rank estimate. Sum over trees, which partition the inputs uniquely. Private randomness in the choice of the whole construction, sampled independently of the matrices, obeys the same bound by averaging. [Rank and correlation calculation](average-case-rank-of-binary-matrix-products.md)

For $s=0$, the right side of the box inequality is $\Pr[AB=0]=\mathbb E_A2^{-d\,\operatorname{rank} A}$. The probability that $A$ has rank below $d/2$ is at most $O(2^{-\lfloor d/2\rfloor^2})$, by counting subspaces inside its kernel. On the complementary event use $2^{-d^2/2}$. This gives the claimed elementary version.

Even arbitrary real-valued weights give a size bound. Over all binary inputs each pair-local edge has at most $2^{2d^2}$ possible keys, so replace all keys by their global order ranks. One can take $w\le \lceil\log_2(m+1)\rceil+2d^2+1$. This counting step charges no time to the parties. For a simple connected graph of polynomial size in $d$, $\log\tau\le(v-1)\log_2(em/(v-1))=O(v\log d)$ when $v>1$. Thus $v=\Omega(d^2/\log d)$ even with real weights of unrestricted precision and arbitrary computation on each pair.

## What is sharp, and what SAT would have to supply

If all edge keys separately depend on **one** matrix, every direct edge comparison already depends on at most two matrices. Then each proposed tree has a single cylinder-intersection indicator. The width term disappears entirely and the bound uses just $\tau$. This version needs no linear-comparison algorithm. Alternatively, applying DLMST's linear-comparison tree gives at most $2^{O(m)}$ such cells on the same public topology.

Quadratic tree information suffices even with one-matrix edges. Chain $d^2$ triangles at articulation vertices. In each triangle one edge is always cheapest, and the other two swap order with the corresponding bit of $A$, with public IDs breaking ties between gadgets. The minimum tree recovers all of $A$. For the decoded value $A_T$, the function $(-1)^{\mathrm{tr}(A_T BZ)}$ is an allowed function of $B,Z$ alone. This example has $\log\tau=\Theta(d^2)$ and computes the parity exactly with $s=0$. An even smaller description of the same construction uses two parallel edges per bit.

More generally, on *any* public graph with $\tau\ge2^{d^2}$ assign a distinct spanning tree to each $A$. Edges of that tree receive lower keys than all other edges. Each edge can calculate its key from $A$ alone. The resulting decoder recovers $A$ and uses just $B,Z$ as above. On a complete graph Cayley's count $v^{v-2}$ reaches this threshold at $v=O(d^2/\log d)$. Thus the unrestricted-precision, polynomial-size vertex bound is tight in order, even when each key depends on only one matrix. This is an information statement and allows expensive local calculations.

A near-linear SAT solver would give a $d^{2+o(1)}$ deterministic RAM evaluator for this parity by two explicit SAT reductions. The evaluator can compute with jointly available input blocks and generate addresses, comparisons and graphs depending on all three. The proof above applies only once the pair-local key maps, public graph and post-tree computation have been supplied. The triangle example also puts the ceiling of a tree-information argument at input scale. The conversion needed for a superlinear SAT bound remains open. [SAT reductions and encoding lengths](verifying-matrix-products-from-sat.md)

The finite audit exhausts all 720 distinct orders on the six edges of the complete four-vertex graph and checks all candidate trees using the grouped cut minimizers. It also reconstructs every comparison up to a 32-element key alphabet from the Fourier factors. Alman and Błasiok study a different connection between matrix multiplication and number-on-forehead communication, via the tensor of input consistency. Priority for the forest representation bounds here is unverified. [Finite checks](../audits/matrix_forest_certificate_audit.py) · [Alman and Błasiok](https://doi.org/10.4230/LIPIcs.CCC.2023.16) · [Length-preserving application to 3-SAT](spanning-trees-for-a-packed-sat-verdict.md)
