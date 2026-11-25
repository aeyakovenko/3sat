# What remains of a matrix-product rectangle bound inside a time interval

Let $D=d^2$. In the compact DIMACS family the varying bits describe three binary matrices $A,B,C$, and the file is unsatisfiable exactly when $AB=C$ over $\mathbb F_2$. Every balanced partition of the $3D$ bits requires $2^{\Omega(D)}$ positive rectangles for this equality verdict. Nevertheless, on a fixed distribution retaining this bound, the sum of the conditional log-cover bounds over any chronological interval tree can be only $O(D)$ bits. The same ceiling holds for overlapping intervals under the pair-congestion condition below. [Compact DIMACS construction](compact-bit-projection-of-matrix-mismatch.md) · [Uniform rectangle bound](product-rectangles-at-adaptive-cuts.md)

Draw $A,B$ independently and uniformly from the invertible binary matrices and set $C=AB$. This is the full-product distribution conditioned on an event of probability at least $1/16$. Indeed, the probability a uniform binary matrix is invertible is $\prod_{j=1}^d(1-2^{-j})\ge 1/4$, by bounding the product after its first factor below by one minus the sum of the remaining $2^{-j}$. Thus the positive mass of every balanced rectangle **contained in the full product graph** is still $2^{-\Omega(D)}$. The file language includes triples with singular operands. Conditioning affects only the choice of the genuine UNSAT file.

## A sharp bound for adding isolated sibling costs

Order the private input bits by bank, first $A$, then $B$, then $C$, in any order within each bank. For a true triple from the stated distribution and adjacent nonempty intervals $L,R$ of this order, fix every coordinate outside $L\cup R$ to the value in the triple. Let $c(L,R)$ be the base-two logarithm of the minimum number of positive $L\mid R$ rectangles covering the resulting equality predicate. Every candidate filling of $L\cup R$ is evaluated using the full product graph.

Give each adjacent cut a nonnegative weight $w_{L,R}$. Suppose that for every $i<j$ the sum of the weights over cuts with $i\in L$, $j\in R$ is at most one. The cuts and weights may depend on the genuine input. Then
$$
             \sum_{L,R}w_{L,R} c(L,R)\le 2(3D-1).
$$
If the union lies in one bank, its only true filling is the original one. With $B,C$ fixed we have $A=CB^{-1}$, with $A,C$ fixed we have $B=A^{-1}C$, and $A,B$ always determine $C$. A singleton is one rectangle, so its log-cover cost is zero.

For each other union choose one of the two boundary positions it contains, either the last $A$ bit or the last $B$ bit. Write $z$ for that position. Every Boolean predicate has a cover with one rectangle per possible string on its smaller side, so $c(L,R)\le\min(|L|,|R|)$. When $z\in L$, pay this bound by assigning at most one unit to each pair $(z,j)$ with $j\in R$. When $z\in R$, use $(i,z)$ with $i\in L$. After multiplying by weights, each pair receives at most one unit. At most $3D-1$ pairs touch each boundary position. This proves the bound. In a tree of adjacent intervals each pair is split at just one node, so unit weights qualify. Conversely the single root cut $A\mid (B,C)$ has log-cover cost exactly $D$ on the full graph. Pinning $B$ to the identity leaves equality on two $D$-bit strings, and listing all left strings attains that lower bound.

This order occurs in legitimate SAT computations. In the compact projection, place the input-dependent clauses in bank order, with the other clauses public. An initial sequential scan gives that first-disclosure order before running any correct solver. It costs $O(N)$ native steps for an $N=\Theta(D)$-bit file and preserves a hypothetical linear time bound. Order bits within one physical word by increasing offset when writing its disclosures. The ceiling applies to the method that fixes all original data outside two adjacent groups and sums their log-cover lower bounds. A machine's existing work cells, later input rereads and inconsistent alternate histories may carry information outside that conditional experiment. [General fractional cut accounting](dynamic-cuts.md) · [Earlier exact calculation for linear codes](balanced-cuts-of-one-sat-run.md)

## The exact distance to another UNSAT file on the projection

For arbitrary binary operands define
$$
  b(B)=\min_{x\ne0}\bigl(|x|+|xB|\bigr),\qquad
  a(A)=\min_{y\ne0}\bigl(|y|+|Ay|\bigr),
$$
using row vectors $x$, column vectors $y$ and binary Hamming weight $|\cdot|$. In the full $3D$-bit face the distance from $(A,B,AB)$ to its nearest other product triple equals $\min(b(B),a(A))$. Changing one row of $A$, or one column of $B$, gives the upper bounds. For any other triple write its differences as $E,F,G$, in that order, so $G=EB+AF+EF$. If a row $e$ of $E$ is nonzero, the corresponding row of $G$ agrees with $eB$ outside the nonzero columns of $F$. Consequently $|eB|\le |G|+|F|$, while $|e|\le |E|$. If $E=0$, then $F\ne0$ and any nonzero column $y$ of $F$ satisfies $|y|+|Ay|\le |F|+|G|$. This proves the reverse bound. On the compact files all private bits occupy distinct ASCII low bits, so this is also their physical Hamming distance within the face.

For uniform independent $A,B$, this distance divided by $d$ converges in probability to $\delta_*=2H_2^{-1}(1/2)\approx 0.22005573$, using the inverse of binary entropy on $[0,1/2]$. To see this for $b(B)$, let $Z$ count nonzero $x$ with $|x|+|xB|\le t$. Each such fixed $x$ has $xB$ uniform. Thus
$$
  \mathbb E Z=2^{-d}\left(\sum_{j\le t}\binom{2d}{j}-\sum_{j\le t}\binom{d}{j}\right),
$$
where $j$ ranges from zero. For $t/d$ a fixed amount below $\delta_*$ the expectation is exponentially small by the Hamming-ball estimate. A fixed amount above $\delta_*$ and sufficiently near it, the expectation is exponentially large, since the first binomial sum has exponential rate $2H_2(t/(2d))>1$ per $d$ and the subtracted sum is at most $2^d$. Distinct nonzero binary vectors are linearly independent in pairs, so $xB,x'B$ are independent and $\operatorname{Var}Z\le\mathbb EZ$. Markov's and Chebyshev's inequalities give both tails. Apply the same argument to $a(A)$ and use monotonicity for larger $t$. Conditioning both matrices to be invertible preserves events of probability tending to one.

In particular, for every fixed $0<\epsilon<\delta_*$, almost every sampled UNSAT file has just one legal UNSAT filling inside **every** set of at most $(\delta_*-\epsilon)d$ private bits when all other bits are fixed to that file. The set can be chosen after inspecting the file or its RAM execution. This local conclusion holds without a bank-order assumption. It describes conditional rectangles on the projection and leaves the unrestricted SAT running-time question open.
