# Recovering a hidden binary product from projected equality tests

Suppose the only access to a hidden $d\times d$ binary matrix $C$ is the bit telling whether $CR=M$, for arbitrary adaptively chosen binary matrices $R,M$ of compatible shapes. Exactly $d(2^d-1)$ queries are necessary and sufficient in the worst case to recover $C$. Even the optimal distribution of the number of negative replies on a uniform matrix is explicit. When the left and right projections in $LCR=M$ must have respective ranks $\ell,r$, the worst-case complexity is $\Theta(2^{\ell r}+d\,2^\ell+d\,2^r+d^2)$. This distinguishes scalar, partial-vector, and whole-vector verification.

These are classical query bounds. In an actual search reduction given public factors $A,B$, information computed from the factors can replace queries. The advice bound below quantifies how much such information is needed. Every hidden $C$ in the query problem is realizable as a binary product, including $I\cdot C$.

## Adaptive affine queries over a finite field

Let $K$ be a finite field of size $q$, and consider an unknown $x\in K^m$. A query asks whether $x$ belongs to any specified affine subspace. On any nonempty set of possible inputs, answer **no whenever some remaining possibility is outside the queried set**. Otherwise answer yes. A yes is already forced by earlier answers, so it removes no candidates. If a deterministic procedure identifies every point, at termination its no queries cover all original candidates except the surviving $x_*$. Empty queries can be discarded. For each nonempty no query take an affine hyperplane containing its flat and missing $x_*$. The product of the defining affine forms is zero at every eliminated point and nonzero at $x_*$.

On the whole grid $K^m$ a polynomial isolating $x_*$ has degree at least $m(q-1)$. Reduce modulo $x_i^q-x_i$ without increasing the total degree. A polynomial with each variable of degree less than $q$ is uniquely determined by its evaluations on the grid, by induction and the univariate root bound. The reduced polynomial is thus a nonzero multiple of $\prod_i(1-(x_i-x_{*,i})^{q-1})$, whose total degree is $m(q-1)$. There must have been at least $m(q-1)$ no replies. Coordinate-by-coordinate enumeration uses at most $q-1$ queries per coordinate, inferring the last value without asking. The punctured-grid hyperplane bound is classical. [Alon and Füredi, *Covering the Cube by Affine Hyperplanes*](https://kam.mff.cuni.cz/~ksemweb/clanky/AlonFuredi-covering_the_cube.pdf)

For the matrix application identify each binary column with a field element in $K=\mathbb F_{2^d}$ using a fixed binary basis. The $d$ columns are the variables $x_1,\ldots,x_d$. A whole-column linear combination is $\sum_j R_{ji}x_j$ in $K$, since $R_{ji}$ is zero or one. An exact equality $CR=M$ therefore cuts out an affine $K$-flat or the empty set, even when the query has many columns. Exhausting the $2^d$ possible values of an individual column uses allowed queries $R=e_i$. The affine result proves the exact worst-case bound in the introduction.

## An exact distributional bound with side information

Put
$$
     H_q(m,h)=\#\{\alpha\in\{0,\ldots,q-1\}^m:\textstyle\sum_i\alpha_i\le h\}.
$$
For a uniform hidden point, any adaptive search procedure using at most $b$ bits of arbitrary advice has
$$
 \Pr[\text{correct output and at most }h\text{ negative replies}]
       \le \min\{1,2^b H_q(m,h)/q^m\}.                                  \tag{1}
$$
This holds for randomized search by conditioning on its coins independently of the hidden point. Advice can arrive online: an adviser knowing the point and the coins can record the chronological sequence of the actual side replies at the start, padding to a fixed $b$ bits. As usual the algorithm and its other publicly fixed information are common to the candidates.

Fix the coins and one advice string. Suppose the successful, low-cost set $X$ in this advice class has more than $H_q(m,h)$ points. Consider the evaluation matrix on $X$ of all reduced monomials of total degree at most $h$. Its rows indexed by points have a nonzero linear dependence over $K$. On the support $Y$ of that dependence no degree-at-most-$h$ polynomial can isolate even one point: evaluating it against the dependence would leave a single nonzero summand. Run the no-if-possible adversary on $Y$. Every candidate there must halt correctly after at most $h$ negative replies, so the simulation halts as well (the finitely many correct runs on $Y$ have a finite maximum length). The product of the negative-query forms isolates the survivor in $Y$, a contradiction. Summing over the advice classes proves (1).

When $b=0$, coordinate-by-coordinate enumeration attains equality in (1) for every $h$ simultaneously. In any fixed order of guesses the number of negative replies for one coordinate is uniform on $\{0,\ldots,q-1\}$. Independent coordinates have independent counts. Thus the minimum expected number of negative replies for zero-error search on the uniform input is $m(q-1)/2$, and the lower bound describes the full distribution even when unsuccessful executions are permitted.

For the matrix case $q=2^d$, $m=d$. From $H_q(d,h)\le {h+d\choose d}\le(e(h+d)/d)^d$, a procedure correct everywhere must have a run with
$$
                  h\ge (d/e)2^{d-b/d}-d.
$$
For any fixed $0<\epsilon<1$, advice of $\epsilon d^2$ bits still leaves $\Omega(d\,2^{(1-\epsilon)d})$ tests on some run. Revealing $\lfloor b/d\rfloor$ bits of every column and testing the remaining column possibilities matches this order. With only polynomially many whole-vector equality queries, constant success on a uniform matrix needs at least $d^2-O(d\log d)$ side bits. This measures the information supplied about the hidden product, regardless of what it cost to compute each bit.

## What left projections buy

Let a query be $LCR=M$ and let $\ell=\operatorname{rank}L$. At the end of the same adversarial run fix the surviving $C_*$. For each negative query choose a column $v$ of $R$ and corresponding column $y$ of $M$ with $LC_*v\ne y$. Any matrix accepted by this query has $Cv$ among the at most $2^{d-\ell}$ preimages of $y$ under $L$. For each such value $u$, the equation $Cv=u$ is one $K$-hyperplane in the hidden column variables, and none contains $C_*$. Empty sets contribute no hyperplanes. This proves, on a single worst-case execution correct on every matrix and with no advice,
$$
          \sum_{i\, :\, \mathrm{no}} 2^{-\operatorname{rank}L_i}
                    \ge d(1-2^{-d}).                                      \tag{2}
$$
Applying the same covering proof to transposes yields the same inequality with $\operatorname{rank}R_i$ in place of $\operatorname{rank}L_i$, on that execution. The proof of (1) also applies with the number of negative replies replaced by the sum of their integer weights $2^{d-\operatorname{rank}L_i}$.

For a fixed rank $1\le\ell\le d$ on the left, (2) and the binary decision-tree bound $d^2$ give a worst-case lower bound of order $d\,2^\ell+d^2$. For the matching upper bound process one column at a time. First compare $\ell$ selected coordinates to each of $2^\ell-1$ proposals to learn their actual values. For each remaining coordinate compare that bit and $\ell-1$ already known bits with the proposal consisting of those known bits and a zero in the new position. Its yes/no reply determines the new bit. Every comparison uses a rank-$\ell$ left projection and an ordinary basis vector on the right, for at most $d(2^\ell-1+d-\ell)$ queries. If both ranks are fixed, with $1\le\ell,r\le d$, the sharp order is
$$
                       \Theta(2^{\ell r}+d\,2^\ell+d\,2^r+d^2).
$$
For the extra lower bound use the same worst-case path. Every consistent queried coset has at most $2^{d^2-\ell r}$ binary matrices, by the rank of $C\mapsto LCR$. Its negative queries must together cover $2^{d^2}-1$ candidates. Together with (2), its transpose and the information bound, this proves the claimed order. For the upper bound first enumerate the contents of one $\ell\times r$ coordinate block. Keeping those $r$ columns fixed, learn their entries in each other row, by padding that row with $\ell-1$ known rows and enumerating at most $2^r-1$ proposals. These $r$ columns are now known in full. For each additional column, learn its entries on the first $\ell$ rows by padding it with $r-1$ known columns and enumerating at most $2^\ell-1$ proposals. Finally learn each remaining entry by choosing a block with its row, its column, $\ell-1$ known rows of that column and $r-1$ known columns. All but the target bit of that block are known, so one comparison suffices. Every query realizes the specified ranks.

## A projective search consequence

Héger, Patkós and Takáts define $A(n,q)$ as the minimum worst-case adaptive number of projective-subspace tests to recover a point of $\mathrm{PG}(n-1,q)$. Their Theorem 1.3 gives the upper bound $(n-1)(q-1)+1$, and their Theorem 1.1 establishes equality at $n=3$. The affine adversary yields the matching lower bound for **every** $n\ge2$. The first proper tested subspace is contained in some projective hyperplane. Answer no and keep its entire affine complement $K^{n-1}$ as the possible hidden points. Every subsequent projective subspace restricts there to an affine flat or the empty set. The affine lower bound requires $(n-1)(q-1)$ further tests. Useless constant queries can only increase the total. For the upper bound, query which of the $n$ homogeneous coordinates vanish. Normalize one nonzero coordinate as a pivot. Each further nonzero coordinate is determined by at most $q-2$ tests of its ratio to the pivot, giving at most $n+(n-1)(q-2)$ queries. [Héger, Patkós and Takáts, *Search Problems in Vector Spaces*](https://arxiv.org/abs/1309.6731)

The general projective equality follows by combining the classical affine punctured-grid bound with this adversary. A search through the original paper, its indexed citing literature and related finite-geometry results located no later priority reference for that deduction or the distributional form (1). Priority remains unconfirmed.

An independent finite minimax calculation gives optimal projective depths 3, 4 and 5 for $\mathrm{PG}(2,2)$, $\mathrm{PG}(3,2)$ and $\mathrm{PG}(2,3)$. For all binary $2\times2$ matrices the optimal depths for projection ranks $(1,1),(1,2),(2,1),(2,2)$ are respectively 4, 6, 6 and 15. The calculation also checks the entire success profile (1) without advice on three small affine grids. [Reproducible finite minimax audit](projected_equality_search_audit.py)

## Consequence for decision-to-search under linear SAT

The mismatch-to-SAT reduction gives deterministic verification of a binary matrix product in $d^2\operatorname{polylog}d$ time under the linear SAT hypothesis. One can test arbitrary trial products of projected matrices as part of a search. The estimates above constrain a classical extractor whose product-dependent information is exhausted by these reply bits and its measured side information. They do not charge the cost of computing with the public factors. For example, when $A=I$, a direct read of $B$ already reveals $C$. Algorithms can also request scalar parities of the product: these have $d^2$-bit rather than whole-vector enumeration complexity. [Explicit SAT verification and arbitrary trilinear contraction](verifying-matrix-products-from-sat.md) · [Earlier transcript and scalar-query bound](matrix-products-from-a-sat-trace.md)

There is a genuine one-query extraction in the quantum model. The phase oracle $|Z\rangle\mapsto(-1)^{\langle C,Z\rangle}|Z\rangle$, applied to the uniform superposition of binary masks and followed by Hadamards, returns $|C\rangle$ with certainty. This is the known Bernstein–Vazirani reduction from matrix multiplication to the trilinear form. Charging the cost of a fast SAT-derived scalar algorithm for this quantum call requires an implementation supporting coherent memory access at that cost. The reduction supplies no deterministic RAM extraction of the public product. [Theorem 3 of *A Note on Fine-Grained Quantum Reductions for Linear Algebraic Problems*](https://arxiv.org/abs/2509.19528)
