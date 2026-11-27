# Quadratic correlation of the trace of a binary matrix product

Let $A,B,C$ be independent uniform $d$-square matrices over $\mathbb F_2$. Put $D=d^2$, $T(A,B,C)=\operatorname{tr}(ABC)$ and $\chi(b)=(-1)^b$. Define
$$
 M_d=\max_{\deg Q\le 2}\left|\mathbb E\,\chi(T+Q)\right|,
$$
where $Q$ is any Boolean quadratic in all $3D$ entries. Then
$$
 \boxed{\quad \log_2 M_d=-3d^2/4+O(d).\quad}
$$
The constant predictor attains the leading exponent. Quadratic cross terms and quadratic terms internal to each of the three matrices can all occur in the same predictor. The proof uses the repeated matrix index through a cyclically graded centralizer. The matrix dimension $d$ may grow.

## The derivative and its radical

Write $V=V_0\oplus V_1\oplus V_2$ with each summand of dimension $d$ and indices taken modulo three. Let $E_j$ consist of endomorphisms that map $V_i$ to $V_{i+j}$. Each $E_j$ has dimension $3D$. Represent $x\in E_1$ by the arrows $x_0=C$, $x_1=B$, $x_2=A$. Each diagonal block of $x^3$ has trace $T(x)$ by cyclicity. Thus $T(x)=\operatorname{tr}_V(x^3)$, since $3=1$ in the field.

For $u\in E_1$ let $C_j(u)=\{v\in E_j:uv=vu\}$ and $c_j=\dim C_j(u)$. The polar form of the quadratic $x\mapsto D_u(T+Q)(x)$ is
$$
 P_u(v,w)=\operatorname{tr}_V\big((uv+vu)w\big),\qquad v,w\in E_1.
$$
Indeed the third difference of $T$ sums the six ordered trace products of $u,v,w$. Each cyclic orbit has size three in this expansion and contributes one copy in characteristic two. The third difference of $Q$ is zero. The ordinary trace pairing identifies $E_2$ with $E_1^*$, so the radical is precisely $C_1(u)$. In particular the polar rank is $3D-c_1(u)$.

For any Boolean quadratic of polar rank $r$, the absolute mean of its sign is at most $2^{-r/2}$. Square its mean and average the affine first derivatives over all shifts. Every shift outside the radical contributes zero. Applying this bound after squaring the correlation gives
$$
 M_d^2\le 2^{-3D/2}\,\mathbb E_{u\in E_1}2^{c_1(u)/2}.                 \tag{1}
$$

## A bound for the centralizer on each orbit

For every $u\in E_1$, one has $c_2=c_0$ and $c_1\le 2c_0$. For the equality, the commutator $E_0\to E_1$ and the commutator $E_2\to E_0$ are adjoint for the trace pairings. This follows by moving one factor around inside the trace. They have the same rank and their domains have the same dimension.

For the inequality, let $t_i=\dim(V_i/uV_{i-1})$ and $s_i=\dim\ker(u:V_i\to V_{i+1})$. Equal vertex dimensions give $s_i=t_{i+1}$. Multiplication by $u$ maps $C_j(u)$ into $C_{j+1}(u)$. Its kernel consists exactly of maps $v$ with both $uv=0$ and $vu=0$. These factor independently at each vertex through $V_i/uV_{i-1}$ into $\ker(u:V_{i+j}\to V_{i+j+1})$. Its dimension is therefore $k_j=\sum_i t_i s_{i+j}$. On a cycle of length three,
$$
 k_1=\sum_i t_it_{i+2}=\sum_i t_it_{i+1}=k_0 .
$$
Consequently $c_1\le c_2+k_1=c_0+k_0\le 2c_0$.

Let $G=\prod_i\mathrm{GL}(V_i)$ act by conjugation. The stabilizer of $u$ consists of the invertible elements of $C_0(u)$. In coordinates on this binary vector space, their indicator is the determinant of the full block diagonal endomorphism. This has degree at most $3d$ and is one at the identity. A nonzero Boolean polynomial of degree $h$ has density at least $2^{-h}$, since the coefficient of a monomial of largest degree survives any fixing of variables outside it. The orbit thus contains at most $2^{3D-c_0+3d}$ points. Its total contribution to the normalized expectation in (1) is at most $2^{3d-c_0+c_1/2}\le 2^{3d}$.

There are at most $2\cdot6^{3d}$ orbits. For completeness, decompose $V$ into the stable kernel and image of a large power of $u$. Both are graded. On the image each arrow is invertible, and each vertex has a common dimension $a$. Bases can identify the first two arrows with identities, leaving one $a$-square invertible matrix up to similarity. Its invariant factors are determined by positive degrees summing to $a$ and by monic polynomials of those degrees. There are at most $4^a$ choices, including the empty list when $a=0$.

The nilpotent part has a basis of homogeneous Jordan chains. To see this, filter $\ker u$ by the graded spaces $F_j=\ker u\cap\operatorname{im}u^{j-1}$ for $j\ge1$. Choose homogeneous bases of complements of $F_{j+1}$ in $F_j$ and lift each chosen bottom vector homogeneously through $u^{j-1}$. The resulting chains are independent. In any relation, apply a power of $u$ that takes the terms of greatest remaining chain length to their independent bottom vectors and kills the shorter terms. They span because the number of chain vectors is $\sum_j\dim F_j$, which telescopes to the dimension of the nilpotent part by rank-nullity on the successive images. A chain is described by its length and its starting vertex. Even an ordered list of such chains of total length $m=3(d-a)$ has at most $6^m$ possibilities, by composing $m$ and assigning one of three colors per part. Summing $4^a6^{3(d-a)}$ gives the orbit bound. This agrees with the standard classification of the oriented cyclic quiver. [Hennecart, §3.5.2](https://www.maths.ed.ac.uk/~lhenneca/thesis.pdf)

Substitution into (1) gives the explicit upper bound
$$
 M_d\le\min\{1,\;\sqrt{2}\,12^{3d/2}2^{-3D/4}\}.
$$

## The lower bound and an exact subclass

Averaging over $C$ first gives the constant correlation
$$
 \beta_d=\Pr[AB=0]=\mathbb E_A 2^{-d\operatorname{rank} A}.
$$
The probability that $A$ has rank $r$ lies between $\kappa^2 2^{-(d-r)^2}$ and $\kappa^{-1}2^{-(d-r)^2}$, where $\kappa=\prod_{j\ge1}(1-2^{-j})>0$. This follows by factoring a rank-$r$ matrix as a full column-rank matrix times a full row-rank matrix and dividing by $|\mathrm{GL}_r(2)|$. Since $(d-r)^2+dr=3D/4+(r-d/2)^2$, summing the Gaussian tail and taking a term nearest $d/2$ give $\beta_d=\Theta(2^{-3D/4})$. Bhrushundi, Harsha, Hatami, Kopparty and Kumar already obtain the leading exponent for the constant predictor. Their correlation theorem for random multilinear forms has a different quantifier and degree range. The sources reviewed here leave priority for the all-quadratics estimate unverified. [Bhrushundi et al., §§3 and 4.3](https://sites.math.rutgers.edu/~sk1233/multilinearforms.pdf)

When $Q$ is affine in $C$ for fixed $A,B$, the exact maximum equals $\beta_d$. Indeed the coefficient paired with $C$ is $L(A)+H(B)+K$ for linear maps $L,H$ and a constant matrix $K$, with the matrix trace pairing understood. Summing out $C$ bounds the correlation by $\Pr[AB=L(A)+H(B)+K]$. Expand this equality indicator in characters indexed by matrices $Z$. For fixed $Z$, the bilinear form $(A,B)\mapsto\operatorname{tr}(ZAB)$ has rank $d\operatorname{rank}Z$ between its two blocks. Adding an affine function leaves its absolute bias at most $2^{-d\operatorname{rank} Z}$, by summing first over either block. Averaging this over $Z$ gives $\beta_d$. The same conclusion holds with any one of the other blocks in the role of $C$. Whether $M_d=\beta_d$ in every dimension is left open by (1). In fact the right side of (1) is at least $\kappa^3 2^{-3D/2+d/2}$. With probability at least $\kappa^3$ every arrow is invertible, and then $C_1$ has the dimension of the ordinary centralizer of the composed $d$-square matrix. This dimension is at least $d$, since the independent polynomials on each companion block of its rational canonical form already supply $d$ commuting maps. Thus the passage to absolute polar-rank bounds in (1) itself loses at least $d/4-O(1)$ in the logarithm compared with the constant predictor. A constant-error estimate would have to retain additional information about the derivative phases.

## Rectangular products

The same leading estimate holds for arbitrary shapes. Order the three vertex dimensions as $a\le b\le c$ using cyclicity and, if necessary, transpose all maps and reverse the arrows. Set $c'=\min(c,a+b)$. For $x$ a uniform triple around this cycle and $Q$ ranging over all quadratics in its entries,
$$
 \log_2\max_Q|\mathbb E\chi(T(x)+Q(x))|
    =-g+O(a+b+c'),\qquad
 g=ab-\frac{(a+b-c')^2}{4}.                                          \tag{3}
$$
In particular the error depends only on $a+b$ when the longest side exceeds the sum of the other two. The estimate identifies the leading exponent whenever this error is lower order than $g$.

Here is the centralizer inequality needed for unequal vertex dimensions:
$$
                        c_1\le c_0+c_2 .
$$
On the invertible summand multiplication by $u$ identifies all three centralizers. A map commuting with $u$ preserves its stable kernel and image. It suffices to prove the inequality on its graded nilpotent chains. For a source chain with starting grade $i$ and length $s$, and a target chain with starting grade $j$ and length $t$, a commuting map is determined by the image of the source generator. It has one basis map at each target offset $h$ with $\max(0,t-s)\le h<t$, of degree $j+h-i$ modulo three. Write $m=\min(s,t)$. If $m\ge2$, at most $\lceil m/3\rceil\le m/2$ of the $m$ maps have degree one. Each such ordered pair contributes a nonnegative number to $c_0+c_2-c_1$.

Let $z_i$ be the number of length-one chains beginning in grade $i$. All ordered pairs of length-one chains together contribute $\sum_i z_i^2$, because the two nonzero grade shifts have equal totals. Pair the two orders between a length-one chain starting at $i$ and a longer chain starting at $j$ of length $t$. There are two maps, one in each order. Their combined contribution can be negative only when both have degree one. The equations $i-j=1$ and $j+t-1-i=1$ modulo three force $j=i-1$ and $3\mid t$. The total negative contribution is therefore bounded below by $-2\sum_i z_i L_{i-1}$, where $L_j$ counts longer chains starting at $j$ with lengths divisible by three. Each ordered pair counted among these longer chains contributes $m/3\ge1$, since then $3\mid m$. Combining the disjoint classes of pairs gives a total of at least
$$
 \sum_i z_i^2-2\sum_i z_iL_{i-1}+\left(\sum_i L_i\right)^2
 \ \ge\ \sum_i(z_i-L_{i-1})^2\ \ge\ 0.
$$

First assume $c\le a+b$ and put $N=ab+bc+ca$, $S=a^2+b^2+c^2$. Here $\dim E_1=\dim E_2=N$, $\dim E_0=S$. Trace adjointness gives $c_2-c_0=N-S$. Thus $c_1\le2c_0+N-S$. The orbit size is at most $2^{S-c_0+a+b+c}$ by the same determinant argument. The invertible parts have a common vertex dimension $h\le a$. The same chain and invariant-factor count bounds the number of orbits by $\sum_{h=0}^a 4^h6^{a+b+c-3h}\le2\cdot6^{a+b+c}$. In (1) the ambient derivative dimension is now $N$. Summing the orbit contributions gives
$$
 \log_2 M^2\le -N/2+(S-N)+(N-S)/2+O(a+b+c)
             =-(2N-S)/2+O(a+b+c).
$$
Since $(2N-S)/4=ab-(a+b-c)^2/4$, this is the required upper bound. For $c>a+b$, fix the entries incident to the extra $c-(a+b)$ basis vectors at that vertex. All terms with an extra index have two fixed factors, so they restrict to an affine function. The remaining unfixed inputs have the boundary shape $(a,b,a+b)$. The same upper bound on every slice gives (3).

For the matching constant-phase bound choose as first factor a uniform $a\times b$ matrix of rank $r$. Its rank probability is within fixed universal constant factors of $2^{-(a-r)(b-r)}$, by the same count as for the square case. Its product with a uniform $b\times c$ matrix is zero with probability $2^{-cr}$. The smallest exponent $(a-r)(b-r)+cr$ over real $0\le r\le a$ is $g$, attained at $(a+b-c')/2$. Rounding to the nearest integer costs at most $1/4$ in the interior and zero at the boundary. The sum over $r$ is bounded by a constant times its largest term by quadratic decay. Thus the constant predictor has correlation $\Theta(2^{-g})$, uniformly in the three sizes. The rounded exponent $\lceil g\rceil$ also appears in the established formula for the geometric rank and border subrank of the rectangular multiplication tensor. The character-sum estimate in (3) applies over the fixed binary field and permits arbitrary quadratic perturbations. [Kopparty, Moshkovitz and Zuiddam, Theorem 6.1](https://arxiv.org/abs/2002.09472)

### Exact answer when one vertex has dimension one

For the shape $(1,b,c)$, write $T=x^\top H y$ with $x\in\mathbb F_2^b$, $y\in\mathbb F_2^c$. Then for arbitrary quadratics on all entries,
$$
 M_{1,b,c}=\Pr[xy^\top=0]=2^{-b}+2^{-c}-2^{-(b+c)}.
$$
The last expression is the constant predictor's bias, by averaging over $H$. Consider a derivative in direction $(u,v,W)$ ordered as the two vectors and the matrix. Summing out $H$ requires $(x+u)(y+v)^\top=xy^\top$. The remaining phase is $(x+u)^\top W(y+v)$. If $u,v$ are both nonzero, the only solutions are $(x,y)=(0,v),(u,0)$. Indeed an equality of nonzero rank-one matrices over the binary field identifies both factors, and equality with both sides zero gives the two displayed pairs. Both phases are zero. If exactly one of $u,v$ is nonzero the opposite input vector must vanish, and again every surviving phase is zero. If both shifts vanish, the mean sign of the residual $x^\top W y$ is $2^{-\operatorname{rank} W}$. The signed mean of each derivative is therefore strictly positive.

A binary quadratic with nonzero mean sign has absolute mean exactly $2^{-r/2}$ for polar rank $r$. On its radical $R$, the derivative in direction $v\in R$ has constant value $q(v)+q(0)$, a linear functional of $v$. The squared mean is $2^{-r}$ times the mean sign of this functional, hence equals either zero or $2^{-r}$. Thus each derivative of $T$ already attains its polar upper bound with positive sign. Every $T+Q$ has the same derivative polar ranks, proving the exact formula. For comparison, at $(2,2,2)$ the squared constant bias is $841/16384$ and the derivative-rank average is $850/16384$, so this pointwise saturation argument already loses something.

The minimum worst-case depth of an adaptive deterministic quadratic-query decision tree for this shape is exactly $b+1$ when $b\le c$. A signed depth-one tree is a constant or a signed quadratic phase. At larger depths expand each branch indicator as $(1\pm\chi(Q))/2$ and use induction, obtaining absolute coefficient sum at most $2^{t-1}$ in quadratic phases at depth $t\ge1$. At $t=b$ its correlation with $T$ is at most $2^{b-1}(2^{-b}+2^{-c}-2^{-(b+c)})<1$. Reading the $b$ bits of $x$ and then asking the quadratic $x^\top H y$ attains the claimed depth.

## Consequence for runs of the evaluator supplied by fast SAT

Suppose $b$ quadratic tests along an execution restrict the matrix inputs to a nonempty fiber. Suppose its verdict on this fiber is a quadratic plus a sum of $k$ products of three arbitrary affine forms. The inputs, the tests and the affine forms may be chosen separately for each execution. Then
$$
 2b+k\log_2(4/3)\ \ge\ 3d^2/4-(3d/2)\log_2 12-1/2.                    \tag{2}
$$
The indicator of the fiber is a convex combination of signed quadratic phases. Each additional cubic product can be expanded in signed quadratic phases with absolute coefficient sum $4/3$. For $p(y)=y_1y_2y_3$ on three bits, the identity $\chi(p(y))=\frac16\sum_v\chi(p(y+v)+p(y))$ proves this even after substituting dependent affine forms. Thus every exact fiber has density at most $(4/3)^k M_d$. Its indicator is also a nonzero Boolean polynomial of degree at most $2b$, with density at least $2^{-2b}$. This proves (2). For one fixed adaptive strategy, the proportion reaching such a terminal fiber with at most $b$ tests and at most $k$ cubic terms is at most $2^b(4/3)^k M_d$, by prefix-freeness. In particular $k=o(d^2)$ forces at least $(3/8-o(1))d^2$ tests on each execution, and at least $(3/4-o(1))d^2$ tests with probability tending to one under a common strategy, taking a diverging margin in the exponent. [Quadratic explanations of actual runs](quadratic-explanations-of-packed-sat-runs.md)

A near-linear deterministic SAT algorithm would produce a $d^2\operatorname{polylog}d$-time binary RAM evaluator for this scalar verdict through the verification reduction. Inequality (2) applies to any exact quadratic explanation of its instructions on its actual inputs. Revealing the operands of a constant-arity word instruction can require $O(\log d)$ test bits when the register and addressed-cell bits have quadratic representatives on the current fiber. At this generic rate (2) only yields $\Omega(d^2/\log d)$ native steps for $k=0$. Even revealing every entry of $A$ in $d^2$ queries leaves the verdict quadratic in $B,C$. A contradiction at the near-linear SAT clock therefore requires a further argument about the *cost of producing* the tests or residual functions. The leading correlation estimate alone leaves all three unrestricted SAT clocks open. [SAT to matrix verification and scalar evaluation](verifying-matrix-products-from-sat.md)

The exhaustive audit constructs the centralizers from binary commutators and independently computes each derivative polar matrix from the truth table. It checks all 6,536 shifts across five shapes, including every shift at $(2,2,2)$. Lean verifies the dimension arithmetic for the equal-vertex kernel identity and the rectangular chain count. The orbit classification, character sums and asymptotic conclusions are manuscript proofs. [Finite audit](../audits/cyclic_matrix_centralizer_audit.py) · [Lean lemmas](../lean/CyclicMatrixCentralizer.lean)
