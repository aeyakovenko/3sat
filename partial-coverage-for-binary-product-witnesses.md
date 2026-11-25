# How many correct products can a short witness system cover?

Write $D=d^2$ and $G=\{(A,B,AB): A,B\in\mathbb F_2^{d\times d}\}$. Consider any system of $s$ equations of the form $\ell m=n$ on binary public and witness variables, with arbitrary affine forms and arbitrarily many additional affine equations. A public triple is accepted when some witness satisfies the system. Suppose the accepted set $T$ is nonempty and contained in $G$, and put $b=\log_2(|G|/|T|)$. Then

$$
 2s + 4b \ \ge\ 3D-\lfloor D/4\rfloor-1-2\log_2(3/2).
$$

In particular, if $s\le(11/8-\delta)D$ with fixed $\delta>0$, a sound system accepts at most a $2^{-\delta D/2+O(1)}$ fraction of the correct products. The same estimate applies separately to every member of a menu, even with overlapping witness domains. A covering menu at this cost needs at least $2^{\delta D/2-O(1)}$ systems. For $b=0$ the additive $2\log_2(3/2)$ term can be removed. For $0\le b\le d-1$ there is a sharper bound $2s+b\ge 3D-\lfloor D/4\rfloor-2$.

## A flat through any two accepted points

Let $E$ be the affine space defined by all free equations, before imposing the $s$ product checks. Let $a$ be the affine dimension of $T$ in the $3D$ public coordinates. Fix satisfying lifts of any two members of $T$. At each check the two triples of values lie in the four-point set $S=\{(x,y,xy):x,y\in\mathbb F_2\}$. They lie on an affine line contained in $S$, choosing another point if they coincide. A binary affine line consists of just two points. Requiring the gate triple to lie on this line adds at most two affine equations to $E$. The resulting set of lifts contains the chosen pair and projects to an affine flat $F\subseteq T$. Since projection can lose at most $2s$ dimensions relative to the original public projection, $\dim F\ge a-2s$. This argument uses the actual acceptance equations. The weaker observation that $G$ is the affine image of an arbitrary subset of $S^s$ could never give more than $\lceil3D/2\rceil$ checks by itself: projecting the first two coordinates from each triple covers an entire $3D$-bit cube at that cost.

## Finding a pair with almost full-rank differences

For $b<D$, put $u=\lfloor b/d\rfloor$. Identify the middle $d$-bit vector space with $K=\mathbb F_{2^d}$ using a common basis. The matrices for the linear maps
$$
                 x\longmapsto \sum_{j=0}^u c_j x^{2^j},\qquad c_j\in K,
$$
form a binary space $Q$ of dimension $d(u+1)$. A nonzero polynomial here has at most $2^u$ roots. Hence evaluation is injective on coefficient vectors, and every nonzero member of $Q$ has corank at most $u$. Partition all pairs of input factors into cosets of $\{(R,R):R\in Q\}$. The mean number of accepted input pairs per coset is $2^{d(u+1)-b}>1$. Some two points of $T$ therefore have factor differences $X=Y=R\ne0$ with both coranks at most $u$. These codes are classical maximum-rank-distance codes. [Delsarte on rank distance](https://doi.org/10.1016/0097-3165%2878%2990015-8)

## How much of the graph can an affine space contain?

For any affine space $S$ of codimension $h$ in public triples, its fraction of the graph is at most
$$
                \Pr_{A,B}[(A,B,AB)\in S]\le (3/2)2^{-h/2}.          \tag{1}
$$
Only this estimate on $S=\operatorname{aff}(T)$ is needed below. It gives $a\ge3D-2b-2\log_2(3/2)$ without any hypotheses on certificates. The factor in front of $2^{-h/2}$ can in fact be taken to be $1+O(2^{-d/2})$ uniformly in $h$. The exponent is attained at $h=2dj$ by setting $j$ rows of $A$ and the corresponding rows of $C$ to zero.

Let $p$ be the codimension of the projection of $S$ onto $A$, and $2D-g$ the dimension of its direction subspace over zero change in $A$. Thus $h=p+g$. For each fixed $A$ the permitted $B$ with $(A,B,AB)\in S$ form an affine space or the empty set. Put $X_t=\{A:\text{this fiber is nonempty of dimension at least } D-t\}$ for integers $t\ge0$. Each $A\in X_t$ gives at least $D-t$ directions $(b,Ab)$ in the same $(2D-g)$-dimensional space. For $A,A'\in X_t$ the intersection has dimension at least $g-2t$. Every common $b$ satisfies $(A-A')b=0$, so
$$
                   d\operatorname{corank}(A-A')\ge g-2t .
$$
If $g-2t>D$, the fiber condition already forces $X_t$ empty, since even equal $A,A'$ violate this inequality. For $0<g-2t\le D$ put $v=\lceil(g-2t)/d\rceil$. The space of linearized polynomials of degree at most $2^{v-1}$ used above has binary dimension $dv$. Its nonzero matrices have corank at most $v-1$. Each of its cosets contains at most one member of $X_t$. Thus in all cases
$$
                  \Pr_A[A\in X_t]\le\min(2^{-p},2^{-g+2t}).
$$
A nonempty fiber of codimension $t_0$ has density $2^{-t_0}=\sum_{t\ge t_0}2^{-t-1}$. Multiply this last bound on $X_t$ by $2^{-t-1}$ and sum. Each term is at most $2^{-1-h/2}2^{-|t-(g-p)/2|}$. The sum of $2^{-|t-x|}$ over all integers is at most $3$ for every real $x$ (sum the geometric tails on the two sides). This proves (1).

For the sharper factor, write $p=jd+r$, $0\le r<d$. For $t\ge (g-jd)/2$ use the bound $2^{-p}$. For $i\ge1$ in the interval $(g-(j+i)d)/2\le t<(g-(j+i-1)d)/2$, the rank-code bound on $X_t$ is at most $2^{-(j+i)d}$, including when the set is empty. The sum of $2^{-t-1}$ over nonnegative integers at least $x$ is at most $2^{-x}$. The resulting total divided by $2^{-h/2}$ is at most
$$
                      2^{-r/2}+\frac{2^{-(d-r)/2}}{1-2^{-d/2}} .
$$
The expression is convex in $r$, so it is bounded by its larger endpoint value on $[0,d]$, which is $1+O(2^{-d/2})$.

## The restriction to commuting directions

Take a graph flat $F$ through these points as above. The product output increment for a direction $(p,q)$ at base $(A,B)$ is $Aq+pB+pq$. The same direction at the other base must have the same output increment. Consequently $Xq+pY=0$ on the projected directions. For any two directions, linearity of the increments also gives $pq'+p'q=0$. Projection to the two factor coordinates is injective on $F$.

Complete $X,Y$ to invertible matrices $X',Y'$ by corrections of rank at most $u$, extending a basis of each image. Restrict the directions by imposing $(X'-X)q=0$ and $p(Y'-Y)=0$. Each costs at most $du$ dimensions, since a rank-$u$ matrix multiplied by an unrestricted matrix has image dimension at most $du$. Now $X'q=pY'$. Write $p=X'H$ and $q=HY'$. The polar identities say $HH'=H'H$ for every two matrices in the resulting space of $H$'s. By the Schur–Jacobson theorem its dimension is at most $\lfloor D/4\rfloor+1$ over $\mathbb F_2$. Thus
$$
             a-2s\le \dim F\le\lfloor D/4\rfloor+1+2du.
$$
Since $du\le b$, the claimed estimate follows. For $b\ge D$ the claimed inequality follows from $s\ge0$. [Mirzakhani's proof of the commutative matrix bound](https://old.maa.org/sites/default/files/pdf/pubs/mirzakhani.pdf)

When $b=0$ the affine span of $G$ is the entire ambient space. A linear functional constant on $G$ vanishes on the two input factors separately by putting the other factor equal to zero. Products attain every matrix, so the remaining output functional also vanishes. For $b\le d-1$ we have $u=0$ and the affine codimension $h=3D-a$ satisfies $h\le b+1$. Indeed, the average of a nontrivial binary parity on the uniform graph is at most $2^{-d}$ in absolute value. If its coefficient on $AB$ has rank $r>0$, averaging first over $B$ enforces a system of $dr$ independent linear conditions on $A$. With zero coefficient on $AB$, a nonconstant linear parity on the factors has mean zero in sign representation. Expanding the indicator of an affine codimension-$h$ space as an average of $2^h$ signed parities gives $2^{-b}\le 2^{-h}+2^{-d}$. This gives the sharper dense bound. For each $0\le h\le d$ the maximum affine-section density is exactly $2^{-h}+(1-2^{-h})2^{-d}$. The character average just used supplies that upper bound with the trivial character separated. Set the first $h$ entries of one output row to zero to attain it. The corresponding input row of $A$ is zero with probability $2^{-d}$. Otherwise its inner products with the $h$ independent columns of $B$ are independent fair bits. At $2D\le h\le3D$, any section contains at most $2^{3D-h}$ points, attained by taking a subspace of the graph flat $A=C=0$. The two-point commuting estimate itself is sharp as a bound on a single flat through the origin and $(I,I,I)$. Take $p=q$ in the space spanned by the identity and by matrices in one strictly upper off-diagonal rectangular block of size $\lfloor d/2\rfloor\times\lceil d/2\rceil$. These matrices commute and $p\mapsto p^2$ is binary-linear on their span.

For $d=2$ the exact maximum numbers of graph points at codimensions $0$ through $12$, in order, are
$$
                 256,160,112,80,64,40,28,20,16,8,4,2,1 .
$$
To check every affine section, project it onto its affine $A$-space $P$. At each $A$ the permitted pairs $(B,C)$ form a translate of the same direction space $V$. Its intersection with the linear graph of $B\mapsto AB$ has size at most the intersection with $V$ itself. The single affine section $P\times V$ attains these simultaneous upper bounds. Translating $A$ by an origin $A_0$ of $P$ and applying the linear shear $C\mapsto C+A_0B$ reduces $P$ to a linear space while retaining this product form. The census therefore exhausts 67 choices of linear projection and 417,199 choices of fiber space. [Exact section census](binary_product_section_census.cpp)

## Applying the estimate to a hypothetical fast SAT program

For a fixed $d$, the explicit mismatch formula has $N=O(d^2\log d)$ bits, each a constant or a function of one input bit. A fixed deterministic SAT program taking $O(N^c)$ steps for $c\ge1$ therefore gives a binary positive witness for any *correct* product: certify its rejecting computation on the mismatch formula. The bounded RAM computation has an existential verifier of $O(N^c\log^2 N)$ bounded-fan-in Boolean gates on the word instruction set specified in the journal. Replace each AND by one rank-one equation, guess all gate results and enforce the affine wiring. This is a single sound system covering every correct product, so its nonlinear budget is at least $(3D-\lfloor D/4\rfloor-1)/2$. If a simulation is instead described by several individually sound branches, their count must obey the covering inequality above. [Ordinary SAT mismatch formula](verifying-matrix-products-from-sat.md) · [Bounded RAM encoding](packed-band-transfer.md)

There is also a limit to shortening just the formula by preprocessing. An affine encoding of the public triple into $N$ bits that determines the verdict must have rank $3D$. A direction $(X,Y,Z)$ in its kernel preserves the graph, giving $Z=XB+AY+XY$ for every $A,B$, hence $X=Y=Z=0$. More generally suppose that producing an $N$-bit code is certified by $s_0$ rank-one checks, and that a downstream decision depending only on the code gives exact existential verification of the product. Fix each accepted codeword by free affine equations. The resulting at most $2^N$ systems are individually sound and collectively complete, so $2s_0+4N\ge3D-\lfloor D/4\rfloor-1-2\log_2(3/2)$. Nonlinearity spent on the encoding contributes to this inequality.

At $c=1$ the available upper bound is $O(d^2\log^3 d)$. The proved lower bound is linear in $D$, the number of entries of one matrix. A contradiction through this compilation would require a lower bound exceeding every constant multiple of $d^2\log^3 d$ along some sequence of dimensions, or a different consequence of the hypothesized solver. At $c=2,3$, even an ordinary multiplication algorithm supplies a verifier well under the size allowed by this compilation. Lean checks the two-origin polarization and normalization to commuting directions using the ring laws. The geometric bound on dimensions and the rank-code counting argument are written proofs. Historical priority of the witness-cost and density bounds is unverified. [Polar identities in Lean](BinaryProductWitnessLines.lean)
