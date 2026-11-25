# Binary rank-one constraints for verifying matrix products with witnesses

Every exact existential rank-one constraint system for the graph of $d\times d$ matrix multiplication over $\mathbb F_2$ requires
$$
                 s\ \ge\ \left\lceil\frac{3d^2-\lfloor d^2/4\rfloor-1}{2}\right\rceil
                     \ =\ \frac{11}{8}d^2+O(1)
$$
nonlinear constraints. The verifier can use arbitrarily many Boolean witnesses and arbitrarily many free affine equations in all its variables. Each counted constraint has the form $\ell m=n$ for any three affine forms in the public and witness bits. Two honest products suffice to force a large affine space of pairwise commuting matrices. The Schur–Jacobson theorem bounds its dimension.

For incomplete systems put $D=d^2$, $G=\{(A,B,AB)\}$, and $K_0=48(d+1)$. Suppose that the accepted public set is a nonempty subset $T\subseteq G$ of density $\eta=|T|/2^{2D}$, and let $b=\log_2(1/\eta)$. Common differences of three honest points give the following coverage bounds, proved below.
$$
 \begin{aligned}
       (85/16)s+7b &\ \ge\ 6D-\log_2 K_0, \\[-1pt]
       (19/8)s+(9/2)b &\ \ge\ 3D-\tfrac32\log_2 K_0.                  \tag{1}
 \end{aligned}
$$
In the first inequality the coefficient of $b$ can be reduced to $5$ when $b<d$. The second becomes $(19/8)s+3b\ge3D-1-\log_2 K_0$ when $b\le d-1$. If at most $2^L$ individually sound systems of cost at most $s$ collectively cover $G$, at least one covers density $2^{-L}$ or greater. Thus the inequalities also give lower bounds with $L$ in place of $b$. A separate two-point argument retains the $11/8$ coefficient with a loss depending on the density. [Partial coverage by two witnesses](partial-coverage-for-binary-product-witnesses.md)

## The zero and identity products

Let $E$ be the affine solution space of all the free equations. Its projection to the public $(A,B,C)$ coordinates has dimension $3D$ under exact completeness. Indeed the whole graph lies in this projection. The graph contains $(0,0,0)$, $(A,0,0)$, and $(0,B,0)$, and subtracting these last two from $(A,B,AB)$ puts every $(0,0,AB)$ in the linear span. Taking $A=I$ gives every output matrix there.

Choose a satisfying lift of $(0,0,0)$ and one of $(I,I,I)$. For each nonlinear constraint its two triples $(\ell,m,n)$ lie in the four-point graph $S=\{(x,y,xy):x,y\in\mathbb F_2\}$. If they differ, the affine line through them consists of just these two points. If they agree, choose any other point of $S$ as the second endpoint. Constrain each gate triple to its chosen line. Each preimage imposes at most two affine equations on $E$. Their joint preimage contains both lifts and its public projection $W$ has dimension at least $3D-2s$, since imposing $2s$ affine equations lowers the dimension of any linear image by at most $2s$ when the intersection is nonempty. Every point in that projection satisfies the verifier, so $W\subseteq G$. It is a linear space since it contains zero.

For $(a,b',c)\in W$, the graph gives $c=ab'$. The additional point $(I+a,I+b',I+c)\in W$ then gives $a=b'$. Thus $W$ consists of $(a,a,a^2)$, and its dimension equals that of the matrix space of its first coordinates. Linearity forces $(a+a')^2=a^2+(a')^2$ and hence $aa'=a'a$ for every two matrices in this space. They generate a commutative matrix algebra. By the Schur–Jacobson theorem over an arbitrary field its dimension is at most $\lfloor d^2/4\rfloor+1$. Comparing dimensions gives the claimed bound. The matrix-space estimate itself is attained: take $a=\lambda I+U$ where $U$ is supported on the upper-right $\lfloor d/2\rfloor\times\lceil d/2\rceil$ rectangle. This gives a flat containing both prescribed points. [Jacobson, *Schur's theorems on commutative matrices*, 1944](https://doi.org/10.1090/S0002-9904-1944-08169-X) · [Mirzakhani's short proof](https://old.maa.org/sites/default/files/pdf/pubs/mirzakhani.pdf)

In fact *every* pair of graph points belongs to a flat of dimension at least $\lfloor D/4\rfloor+1$. Let $(X,Y)$ be the pair's factor differences. Choose a middle subspace $J\subseteq\mathbb F_2^d$ of dimension $m=\lfloor d/2\rfloor$. Start with the $D$-dimensional split direction space $a|_J=0$, $\operatorname{im}b'\subseteq J$, and impose $aY+Xb'=0$. If $r=\operatorname{rank}(X|_J)$ and $t=\operatorname{rank}(Y\bmod J)$, the rank of this last map is $d(r+t)-rt$, by the column-space and row-space computation below. Its kernel has dimension $(d-r)(d-t)\ge(d-m)m$. Adjoin $(X,Y)$ if absent. If it is already in the kernel then $r=t=0$ and the kernel already has dimension $D$. On the enlarged direction space the polar expression $ab''+a'b'$ vanishes for every two directions. Therefore $(a,b')\mapsto ab'$ is additive there over $\mathbb F_2$. Translating the directions to the first graph point gives the claimed graph flat through both points. The opposite zero and identity points give the smallest possible maximum flat dimension among pairs. This identifies the ceiling of a proof using only the span of the graph and the largest flat through two prescribed points.

## Eliminating the witness from two differences

Let $E$ be the affine space in public and private variables imposed by all free affine equations, $\pi$ its public projection, and $\Gamma:E\to\mathbb F_2^{3s}$ the map recording every triple $(\ell,m,n)$. A lift in $E$ satisfies the full verifier exactly when its recorded triples belong to $S^s$, where
$$
                   S=\{(0,0,0),(0,1,0),(1,0,0),(1,1,1)\}.
$$
Write $P=\{z:T+z=T\}$ for the vector space of translation periods of the accepted public set. If a direction $v$ of $E$ has $\Gamma_{\rm lin}(v)=0$, translating by $v$ permutes the satisfying lifts and therefore $\pi_{\rm lin}(v)\in P$. Consequently the public projection modulo $P$ factors *affinely* through $\Gamma$ on $E$. This is elementary linear factorization after choosing any origin of $E$. Multiple witnesses for one public point cause no difficulty.

For three tuples write $\mathcal D(u_0,u_1,u_2)=(u_1+u_0,u_2+u_0)$. Sample three independent uniform points $g_j\in T$ and choose one satisfying lift by a fixed rule for each sampled point. The public pair of differences $\mathcal D(g_0,g_1,g_2)$ modulo $P$ in each coordinate is a linear function of the differences of the recorded gate triples. Hence, by subadditivity and data processing, its base-two Shannon entropy is at most the sum over the gates of the entropies of their own difference pairs. Each gate sees three independent copies of its own marginal distribution on $S$. Dependence between different gates is unrestricted.

## One Boolean multiplication

The six unordered pairs of distinct points of $S$ have six distinct nonzero differences. Thus for uniform samples from $S$, the output of $\mathcal D$ has the following probabilities per pattern.

| Number of distinct samples | Number of patterns | Probability of each pattern |
|---|---:|---:|
| One | $1$ | $4/64$ |
| Two | $6\cdot 3=18$ | $2/64$ |
| Three | $4\cdot 3\cdot 2=24$ | $1/64$ |

For three distinct samples, the two differences specify two distinct unordered edges, whose intersection recovers the origin. With two distinct samples the used edge and the positions of the nonzero differences specify the pattern, with two choices for the origin. This explains all the multiplicities.

For an arbitrary common marginal $p=(p_1,\ldots,p_4)$, upper-bound the output entropy by its cross-entropy relative to this uniform-sample output law. If $J$ counts the distinct samples, the result is at most
$$
                   6-\Pr[J\le2]-\Pr[J=1]\ \le\ 6-5/8-1/16=85/16.    \tag{2}
$$
Indeed, $\Pr[J=1]=\sum_i p_i^3\ge1/16$ by convexity. Also $\Pr[J=3]=6\sum_{i<j<k}p_ip_jp_k\le 3/8$. To see the maximum, averaging two coordinates with their sum fixed increases their product, and all terms involving exactly one of them have fixed total. Equivalently apply the arithmetic mean bound for the third elementary symmetric mean. Equality in (2) holds at the uniform marginal.

## The same two differences on honest products

First sample the three graph points uniformly and independently from all of $G$. Write the factors of the origin as $(A,B)$ and those of point $i$ as $(A+X_i,B+Y_i)$ for $i=1,2$. The six matrices $A,B,X_1,Y_1,X_2,Y_2$ are independent uniform. Conditional on the four input differences, the two output differences are
$$
                     A Y_i+X_i B+X_iY_i,\qquad i=1,2.
$$
For fixed input differences define the linear map $L(U,V)=(U Y_i+X_i V)_{i=1,2}$. A specified pair of graph differences has at most $|\ker L|$ preimages in $G^3$, since the unknown origin lies in one affine fiber of this map.

For any fixed $U,V$ of ranks $r,t$, the image of $(X,Y)\mapsto UY+XV$ has dimension $d(r+t)-rt$. The first summand ranges over all matrices with columns in $\operatorname{im}U$, and the second over all matrices with rows in the row space of $V$. Their intersection has dimension $rt$, as is immediate in independent bases of the output and input spaces. Hence the probability that $(U,V)\in\ker L$ is $2^{-2(d(r+t)-rt)}$.

There are at most $4\cdot2^{(2d-r)r}$ matrices of rank $r$. Factor a rank-$r$ matrix through $\mathbb F_2^r$, allowing at most $2^{2dr}$ factorizations in total and exactly $|\mathrm{GL}_r(2)|$ factorizations of each rank-$r$ matrix. The product formula gives $|\mathrm{GL}_r(2)|\ge 2^{r^2}/4$ since $\prod_{j=2}^r(1-2^{-j})\ge1-\sum_{j=2}^r2^{-j}\ge1/2$. The same count applies to $t$. Summing the probabilities over the candidate pairs gives
$$
           \mathbb E|\ker L|\le16\sum_{r,t=0}^d2^{-(r-t)^2}\le48(d+1).       \tag{3}
$$
The last step uses $\sum_{j\ge1}2^{-j^2}\le1$.

For independent uniform points of $T$, the same first moment costs a factor of at most $2^{2b}$. Fix $(U,V)$ of ranks $(r,t)$, and let $k=d(r+t)-rt$. The linear map $(A,B)\mapsto AV+UB$ has rank $k$. Its fibers on all factor pairs have size $2^{2D-k}$. Thus under uniform sampling from $T$, its largest atom has probability at most $2^{b-k}$. The condition $(U,V)\in\ker L$ says that all three sampled points have the same value of this map. The triple collision probability $\sum_z p_z^3$ is at most $(\max_z p_z)^2\le 2^{2b-2k}$. Summing as in (3) gives $\mathbb E_T|\ker L|\le 2^{2b} K_0$.

The entropy of the three accepted points is $3\log_2|T|=6D-3b$. Given their two public differences, the logarithm of the kernel size bounds the entropy of the remaining choice of origin. The chain rule followed by Jensen's inequality gives
$$
            H(\mathcal D(g_0,g_1,g_2))\ge6D-5b-\log_2 K_0.            \tag{4}
$$

## The cost of translation periods

Projection $P\to\{(a,b')\}$ onto the two input-factor coordinates is injective, since a translation in the claimed product alone cannot preserve a nonempty subset of a function graph. Denote the image by $V$. For each period $(a,b',c)$ and each accepted input pair $(A,B)$, the graph identity gives $c=Ab'+aB+ab'$. Subtract this identity at two accepted input pairs differing by $(X,Y)$, to obtain $Xb'+aY=0$. Taking matrix trace exhibits all input differences of $T$ in the orthogonal complement of $V$ for the nondegenerate pairing
$$
                       ((X,Y),(a,b'))\ \longmapsto\ \mathrm{tr}(Xb'+aY).
$$
Thus $|T|\le2^{2D-\dim V}$ and $\dim P=\dim V\le b$. Quotienting a pair of differences in the public space by $P$ in both coordinates loses at most $2\dim P$ bits of entropy. Equations (2) and (4) prove the first inequality of (1).

In the denser case $b<d$, $P$ is zero. In fact the correct graph points lying also in a translate by $(a,b',c)$ solve one affine matrix equation in $(A,B)$, of rank $d(r+t)-rt$ for $r=\operatorname{rank}a$ and $t=\operatorname{rank}b'$. This is at least $d$ if either rank is positive. A nonzero translation in $C$ alone has disjoint support. A set containing more than a $2^{-d}$ fraction of $G$ cannot admit any such period. Using (4) directly gives the stated coefficient of $5$. [Related fixed-space argument](affine-certificates-on-the-binary-product-graph.md) · [Lean verification of the local gate counts](TetrahedronTripleDifferences.lean)

## Common shifts of three lifts

Let $a_T=\dim\operatorname{aff}T$, and take the same three independent points of $T$ with their fixed lifts. Let $h$ count gate coordinates seeing at most two distinct symbols among their recorded triples. By the single-gate calculation above, $\mathbb E h\ge5s/8$. In each of these $h$ coordinates choose a nonzero local shift which keeps all three recorded symbols in $S$ when added. For two distinct symbols use their difference. For one symbol use its difference with any other symbol. Independent choices to apply or omit each shift give an $h$-dimensional vector space $U$ in $\mathbb F_2^{3s}$ of common allowable shifts.

The preimage of $U$ under $\Gamma_{\rm lin}$ has codimension at most $3s-h$ in the direction space of $E$. Since the public projection of $E$ contains $T$ and has dimension at least $a_T$, the public image of this preimage has dimension at least $a_T-3s+h$. Translating the three chosen lifts by any direction in this preimage yields three satisfying lifts. Every resulting public shift preserves their two differences and sends the origin to a genuine graph point. Distinct shifts give distinct origins, so the fiber bound above gives $a_T-3s+h\le\log_2|\ker L|$. Taking expectations,
$$
                    a_T\le (19/8)s+2b+\log_2 K_0 .                 \tag{5}
$$
Both differences of points of $T$ lie in the direction space of its affine hull, so their joint entropy is at most $2a_T$. Equation (4) gives $a_T\ge3D-\tfrac52 b-\tfrac12\log_2 K_0$, proving the second inequality in (1).

For $b\le d-1$ one can use a stronger bound on $a_T$. Every nontrivial binary linear character on positive triples has expectation of absolute value at most $2^{-d}$. Indeed a character involving only $A,B$ has zero mean. If its coefficient on $C$ is a nonzero matrix $Z$, average first over $B$ at fixed $A$. This vanishes unless the coefficient matrix of $B$ cancels the one induced by $AB$, a linear equation on $A$ of rank $d\operatorname{rank}Z$. It holds with probability at most $2^{-d}$. Now an affine space of codimension $t=3D-a_T$ has indicator equal to $2^{-t}$ times the signed sum of its $2^t$ normal characters. Its probability under a uniform graph point is at most $2^{-t}+2^{-d}$. It contains $T$, whose density is $2^{-b}\ge2^{1-d}$. Thus $2^{-t}\ge2^{-b-1}$, or $a_T\ge3D-b-1$. Substitution in (5) yields the stated coefficient of $3$.

## Scope and related work

The estimate concerns the number of rank-one equations in a fixed binary verifier. Ordinary XOR–AND computations of a product yield such verifiers by guessing all intermediate words bitwise and enforcing each AND output with one equation. The constant-factor lower bound above applies with arbitrary cyclic dependencies and unrestricted witness multiplicity. It gives no superlinear RAM time lower bound for SAT. The mismatch-to-SAT reduction produces formulas of length $d^2\operatorname{polylog}d$, and a word RAM step can act on many bits. [Matrix-product mismatch reduction](verifying-matrix-products-from-sat.md)

Rank-one constraint satisfiability is established as a model of computation verification. Earlier coding-theoretic multiplicative-complexity bounds concern Boolean circuits, including depth-three restrictions for the strong nonlinearity-based bounds. Existing verification work analyzes matrix-product algorithms and lower bounds for classes of linear-algebraic algorithms. Shannon entropy of sums and differences is a classical tool in additive combinatorics. A search of these lines located no prior statement of the two-point or coverage bounds here for witness-unrestricted binary matrix-product verifiers. Historical priority remains unverified. [R1CS formulation, Zhang, Kan and Wang](https://doi.org/10.1016/j.tcs.2022.06.005) · [Boyar and Find on vector-valued multiplicative complexity](https://arxiv.org/abs/1407.6169) · [Bennett et al. on matrix-product verification](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2024.42) · [Tao on sumset entropy](https://arxiv.org/abs/0906.4387)
