# Optimal ordered read-once width for verifying promised binary matrix products

Let $A,B,C$ be $d\times d$ matrices over $\mathbb F_2$, put $D=d^2$, and let $E=AB-C$. An ordered binary decision diagram (OBDD) can choose any fixed order of the $3D$ source bits. Each path queries a subsequence of this order. Write $W$ for the smallest attainable maximum number of nodes labeled by any one variable. The bounds also hold under the convention that every path queries every variable, with width measured at a layer. Off-promise inputs can receive either verdict. Logarithms are base two.

**Theorem.** For deciding $E=0$ under a Hamming-weight or rank promise, the following bounds have absolute implied constants, uniformly over the indicated integer parameters.

| Promise | Optimal $\log_2 W$ |
| --- | --- |
| $\mathrm{wt}(E)\le1$ | $\Theta(1)$ |
| $\mathrm{wt}(E)\le K$, $2\le K\le D$ | $\Theta(K\log_2(eD/K))$ |
| $\operatorname{rank}(E)\le r$, $1\le r\le d$ | $\Theta(rd)$ |

The statements are asymptotic in $d$. With zero allowed errors only the equality verdict occurs. Complementing the verdict preserves width.

## One order suffices for all upper bounds

For a specified family $\mathcal E$ of possible errors containing zero, fix $t=O(\log(2+|\mathcal E|))$ pairs of binary vectors $(u_\ell,v_\ell)$ such that the scalar measurements $u_\ell^\mathsf T E v_\ell$ detect every promised nonzero $E$. One proof chooses $u,v$ independently uniformly. For any nonzero $E$, $Ev$ is nonzero with probability at least $1/2$, after which its dot product with $u$ is one with probability $1/2$. The union bound on $t$ independent tests fixes a list. The [linear-size circuit construction](sparse-product-verification-bit-circuits.md) gives measurements with extra structure for efficient gate evaluation.

For each $k$ in increasing order read column $k$ of $A$ and then row $k$ of $B$. After these $2D$ queries read all entries of $C$ in any fixed order. For each measurement maintain a running parity $z_\ell$ and the two current parities

$$
x_\ell=\bigoplus_i u_{\ell,i}A_{ik},\qquad
y_\ell=\bigoplus_j B_{kj}v_{\ell,j}.
$$

On the last input of block $k$, fold $x_\ell y_\ell$ into $z_\ell$ and clear the two local accumulators. While reading $C$, toggle $z_\ell$ by each $u_{\ell,i}C_{ij}v_{\ell,j}$. The layer determines all indices and coefficients. At the end the $z_\ell$ are exactly the measurements of $E$; their joint zero status determines the answer. Three bits per check give width at most $2^{3t}$. Here cost is the number of states, so a layer transition can update all parities simultaneously.

There are at most $\sum_{i=0}^K\binom Di$ error patterns of weight at most $K$. Its logarithm is $O(K\log(eD/K))$, by the binomial bound for $K\le D/2$ and the full cube bound $2^D$ otherwise. For $K=1$, the single all-ones pair suffices, since parity detects the only possible nonzero weight. A rank-$\le r$ matrix factors through $r$ binary coordinates and has at most $2^{2dr}$ possible values, giving $t=O(rd)$.

## Matching lower bounds at a common query position

Fix any order and cut it after $\lfloor3D/2\rfloor$ bits. By the [balanced crossing lemma](balanced-cuts-of-the-binary-product-graph.md), one can fix either $A$ or $B$ to a permutation matrix so that at least $m\ge\rho D$ of the remaining source bits are paired with their output bit across the cut, where $\rho=(3\sqrt3-5)/2>0$. Indeed each specialization makes $AB$ a permutation of the entries of the other factor; averaging over permutations in the two possible directions gives the crossing bound. Each selected pair has a distinct output coordinate.

Fix all entries of noncrossing pairs to zero. In the $m$ crossing pairs put $x_s$ on the prefix side and $y_s$ on the suffix side. Whether the output bit appears on the prefix side or the suffix side, the error at the corresponding coordinate is $x_s\oplus y_s$. The resulting inputs with $x=y$ are all accepted. For the rank proof we may also discard additional pairs by fixing both their bits to zero.

Suppose $S\subseteq\{0,1\}^m$ is such that all mixtures $(x,y)$ for $x,y\in S$ meet the promise. Distinct $x,x'\in S$ need distinct states at the cut, since suffix $y=x$ requires opposite verdicts for these two prefixes. This also bounds width when paths may skip levels. Pinning constants bypasses nodes and never increases the number labeled by a remaining variable. In the restricted diagram, the accepting path on $(x,x)$ must query the first free suffix bit because flipping just that bit gives one erroneous entry and remains promised. Hence the first node reached after the prefix on this path is labeled by that same suffix variable for every $x$. Its identity is determined by $x$ alone. The distinguishable states are therefore nodes at a *single* remaining variable.

For $2\le K<m$, take $S$ to be the radius-$\lfloor K/2\rfloor$ Hamming ball at zero. All pairwise distances are at most $K$. With $s=\lfloor K/2\rfloor\ge K/3$ we have

$$
\log_2 W\ge\log_2\binom ms\ge s\log_2(m/s)=\Omega(K\log_2(eD/K)).
$$

The last comparison uses $m\ge\rho D$ and $m/K\ge1$. For $K\ge m$ the entire $m$-cube is allowed and gives $\log W\ge m=\Omega(D)$, which covers this range. For $K=1$ retain one crossing pair and fix all others. Both choices for its prefix bit require distinct states at its suffix bit.

For the rank promise, select the $r$ rows of $C$ that together contain the most crossing output sites. These contain at least $rm/d$ sites by averaging. Keep all pairs in these rows and pin all other pairs. Every mixture then has errors supported on these $r$ rows, so its rank is at most $r$. The full cube on the retained pairs gives at least $2^{rm/d}$ distinguishable states. This works for both possible permutation specializations, since the chosen rows refer to coordinates of $C$.

## Consequences for SAT on a fixed DIMACS template

The [compact mismatch projection](compact-bit-projection-of-matrix-mismatch.md) places each matrix bit in exactly one distinct input position, fixes every other bit of the file, and gives exactly $\mathrm{wt}(E)$ satisfying assignments. On this image SAT is the complement of product equality. Any OBDD on the file restricts to a source OBDD by pinning public bits and relabeling the other nodes. Conversely the source order and its transitions lift directly to file positions. Under a complete-layer convention the fixed positions may be processed in dummy layers. Thus the optimal widths on the promised template image agree in both directions. In particular the transition from one allowed assignment to two takes the optimal width from constant to $2^{\Theta(\log D)}$.

An OBDD for all SAT files with at most $K$ satisfying assignments must also work on this template, so the lower bound carries over at its encoded length $N=\Theta(D)$. The upper bounds apply to the template image, where the varying input positions and their matrix coordinates are public. Rank is an additional promise on the matrices represented by that template. The read-once state bound holds for one order shared by all runs of an OBDD. It leaves unrestricted random-access running time unresolved. The prefix-state method is the standard connection between OBDDs and one-way communication. Priority for these promise-sensitive matrix width formulas has not been established. [Wegener, *Branching Programs and Binary Decision Diagrams*, Section 4.1](https://doi.org/10.1137/1.9780898719789)
