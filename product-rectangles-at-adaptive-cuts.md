# Uniform product inputs defeat rectangles with independently chosen cuts

Put $D=d^2$ and $\mathcal G_d=\{(A,B,C):AB=C\}$, with ordinary multiplication of binary matrices over $\mathbb F_2$. Draw $A$ and $B$ independently uniformly and set $C=AB$. Every combinatorial rectangle $R\subseteq\mathcal G_d$ across **any** partition of the $3D$ exterior bits with at least $D$ on each side has probability at most $2^{-\Omega(D)}$ in this *one fixed distribution*. Consequently even a cover in which each rectangle chooses its own balanced partition needs $2^{\Omega(D)}$ rectangles. Ordinary decomposable negation normal forms (DNNFs) and adaptive read-once branching programs for the product graph have exponential size in the actual number of bits. There is no fixed order, prescribed common decomposition tree or ambiguity bound in the rectangle theorem.

## The two cross maps after fixing a matrix

Write the sides of a partition as $L,R'$. Start with a nonempty rectangle $P\times Q$ contained in the product graph. On the $P$ side, $C_L$ is a function of the local $(A_L,B_L)$. Otherwise fix any member of $Q$ and obtain two distinct products of the same input matrices. The same holds on the $Q$ side. Thus the rectangle's projection onto the input coordinates is precisely the product of its two local projections, and a uniform $A,B$ contributes its unique product triple to the rectangle exactly when it belongs to this projection.

Fix the entire matrix $B$. The allowed $A_L$ and $A_{R'}$ still vary independently, over two fibers of the projections. If either fiber is empty the conditional mass is zero. Otherwise fix any member of the right fiber. The right-side output $C_{R'}$ is unchanged when the left fiber varies. Hence differences within the left fiber belong to the kernel of the linear map $A_L\mapsto(A_L B)_{R'}$, treating zero as the fill outside the indicated $A$ coordinates. Analogously, the right fiber lies in a coset of the kernel of $A_{R'}\mapsto(A_{R'}B)_L$. If the two ranks are $r_{LR}(B)$ and $r_{RL}(B)$, the conditional mass of the rectangle is at most
$$
        2^{-r_{LR}(B)-r_{RL}(B)}.
$$
These ranks are exact sums of submatrix ranks. For row $i$ let $I_i$ be the set of column indices of its left $A$ entries, and $J_i$ the set of column indices of its right $C$ entries. Different $A$ rows have disjoint domains and ranges, so
$$
 r_{LR}(B)=\sum_i\operatorname{rank} B[I_i,J_i],\qquad
 r_{RL}(B)=\sum_i\operatorname{rank} B[I_i^c,J_i^c].
$$
Fixing $A$ and varying the $B$ columns gives the two vertical cross maps and the identical bound with transposed roles. Lean checks the local output uniqueness and the kernel identity at each right-side coordinate. The rank and probability estimates below are manuscript arguments. [Lean lemmas](ProductRectangleFibers.lean)

## Averaging the ranks without independence

Let $h$ be the expected fraction of crossing $A$–$C$ pairs when $B$ is specialized to a uniformly chosen permutation matrix. Define $v$ analogously for vertical $B$–$C$ pairs. Every balanced partition has $\max(h,v)\ge\rho=(3\sqrt3-5)/2$ by the [balanced-cut calculation](balanced-cuts-of-the-binary-product-graph.md). Permutations serve only to measure the cut. The source distribution still uses two independent uniform full matrices.

For a uniform binary $k\times l$ minor $U$ of $B$,
$$
 \mathbb E\, 2^{-2d\operatorname{rank}(U)}
 \le (d+1)2^{-kl}.
$$
Indeed at rank $r$ there are at most $2^{(k+l)r}$ possible matrices by factoring through $r$ coordinates, and $k+l\le2d$. The inequality includes an empty minor. There are $2d$ minors across the two orientations of the row maps. Hölder's inequality bounds the expectation of their product of factors $2^{-\operatorname{rank}(U)}$ by the product of the $2d$-th moments above, each raised to the power $1/(2d)$. The minors can overlap. The sum of their areas $kl$ equals $h d^3$, since the mean number of crossing pairs in row $i$ under a uniform permutation is $(|I_i||J_i|+|I_i^c||J_i^c|)/d$. Hence the mass is at most $(d+1)2^{-hD/2}$. The vertical maps give the analogous estimate with $v$ in place of $h$. The final bound is
$$
 \Pr[(A,B,AB)\in P\times Q]\le(d+1)\,2^{-\rho D/2}.
$$
This estimate uses one input distribution for all rectangles, even when their balanced partitions differ. Summing their masses proves the cover bound.

As a small independent check, at $d=1,2$ the largest positive balanced rectangles contain respectively **3 of 4** and **112 of 256** correct products. For $d=2$ one maximizing side consists of $A_{00},A_{10},B_{00},B_{01}$. To reproduce, generate all $2^{2D}$ true triples and enumerate the balanced partitions up to swapping their sides (3 and 1,749 respectively). For each partition let $N(x)$ be the column-neighbor mask of row $x$ in the truth matrix. Start with no masks. On seeing a row, add its mask and its intersections with all earlier candidate masks. For each nonempty resulting mask $Y$, the largest rectangle with exactly these columns and all compatible rows has cardinality $|Y|\cdot|\{x:Y\subseteq N(x)\}|$. Every maximal nonempty rectangle occurs this way. These checks exercise small cuts in a regime where the asymptotic constants in the proof are weak.

## Consequences and the role of the verdict

The balanced rectangle theorem for DNNFs turns a DNNF of size $s$ into a balanced multi-partition cover of polynomial size in $s$ and the number of variables. It applies to the graph because all $3D$ bits are relevant. Thus every DNNF for $[AB=C]$ has size $2^{\Omega(D)}$. Decomposability requires disjoint input variables at an AND gate; OR gates may overlap or branch nondeterministically. A syntactic read-once branching program converts to a DNNF with linear overhead: at each bit query expand into the OR of the two replies, each conjoined with the respective literal; the queried bit never appears downstream on that path. Public nondeterministic branches become OR gates. In particular the lower bound applies to free binary decision diagrams with unrestricted adaptive variable order and to nondeterministic syntactic read-once branching programs. These representation implications use established results. [Bova, Capelli, Mengel and Slivovsky, *Knowledge Compilation Meets Communication Complexity*](https://florent.capelli.me/publi/kc_meets_cc.pdf)

In the other direction $[AB\ne C]$ has a syntactic nondeterministic read-once branching program of size $O(d^3)$. Choose any index $(i,j)$ and evaluate its $d$-term dot product against $C_{ij}$, querying the distinct entries in that row and column. Per term a constant-size control updates the parity and remembers one operand until the other arrives. Accept if this dot product disagrees. Multiple erroneous entries can give multiple accepting paths. This is also a polynomial DNNF for the complement. Deterministic read-once programs can exchange their two verdicts, so the exponential deterministic lower bound holds on either side.

Memory in an unrestricted RAM can keep the entries, and later reads can revisit them. The rectangle proof gives no bound on the number of times that general computation steps through overlapping sets of input bits. Closely related read-once lower bounds for integer multiplication and decomposable representations precede this analysis. Priority for the uniform full-product rectangle bound for this exact verification predicate has not been established. [Bryant and the subsequent read-once integer multiplication lower bound of Ponzio](https://doi.org/10.1137/S0097539795290349) · [SAT reduction, tensor conventions and time exponents](list-and-matrix-costs-for-ram-and-tapes.md)
