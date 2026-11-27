# Which inputs admit the shortest quadratic certificate?

Let $K=\mathbb F_{2^m}$ for even $m\ge4$, $q=2^m$, $t=m/2$, and $F(u,v,w)=\operatorname{Tr}_{K/\mathbb F_2}(uvw)$. A certificate for $x\in K^3$ gives the actual answers at $x$ to a list of Boolean quadratic questions. Every other field triple consistent with the answers must have the same value of $F$. This permits adaptive questions and a nondeterministic choice of questions: on the fixed successful path the list is fixed.

**Every nonempty monochromatic transcript of at most $t$ questions is exactly one of the three planes $u=0$, $v=0$, $w=0$.** Each occurs. In particular the minimum number of questions certifying the answer at an individual input is

$$
 C_F(u,v,w)=
 \begin{cases}
 t & uvw=0\text{ in } K,\\
 t+1 & uvw\ne0\text{ in } K .
 \end{cases}
$$

The distinction matters on a negative answer: a nonzero field product can still have zero binary trace. The fraction of uniform inputs with a $t$-question certificate is exactly $1-(1-1/q)^3$.

The companion proof rules out a positive transcript at depth $t$. It also proves that no nonempty monochromatic transcript of either sign can use fewer questions. Here we classify the zero transcripts at depth $t$. [Positive certificate, low-weight reduction and physical SAT transfer](trace-product-positive-certificates.md)

## Shapes that remain after the weight bound

The indicator of a transcript is the product $P$ of its $t$ quadratic equality indicators over $\mathbb F_2$. A monochromatic transcript has mass at most $(2q-1)/q^2<2/q$, by the correlation of $(-1)^F$ with quadratic phases. The minimum weight bound for a nonzero Boolean polynomial therefore gives $\deg P=m=2t$. The Kasami–Tokura classification applies to this strict sub-double-minimum weight. The density argument on the quadratic normal form in the companion proof excludes three or more independent quadratic pairs for either monochromatic sign: the absolute correlation bound used there is symmetric in the sign. Thus the remaining support is either one affine flat of binary dimension $2m$, or the symmetric difference $U\mathbin{\triangle}V$ of two such flats whose nonempty intersection has binary codimension $\mu\ge2$ in each. In the two-pair normal form $\mu=2$. In the other family the common leading product fixes $m-\mu$ variables and each disjoint tail product fixes another $\mu$, so the overlap has dimension $2m-\mu$. [Kasami and Tokura](https://doi.org/10.1109/TIT.1970.1054545) · [Explicit statement of both normal forms, Theorem 4](https://www.esat.kuleuven.be/cosic/publications/article-414.pdf)

There is a general restriction from the individual queries. If their common solution set is $U\mathbin{\triangle}V$, each equation $Q_i=c_i$ holds throughout $U\setminus V$. On $U$ the degree-at-most-two polynomial $Q_i+c_i$ is supported within $U\cap V$. For $\mu\ge3$ this subflat occupies at most an eighth of $U$, whereas a nonzero quadratic occupies at least a quarter. Thus all the equations hold on all of $U$, incorrectly including $U\cap V$ in the same transcript. This excludes the entire Kasami–Tokura family with two disjoint tail products of length $\mu\ge3$, independently of $F$ and of how many quadratic questions were used.

Conversely, at even degree $r\ge2$, every form in the other Kasami–Tokura family is the indicator of a transcript of $r/2$ quadratic questions. Its $r-2$ independent affine preconditions can be checked in pairs by asking if their product equals one. One more question tests the indicated sum of products of disjoint pairs. An invertible affine change of coordinates preserves quadratic degree. Thus among nonzero polynomials of even degree $r$ and relative weight strictly below $2^{1-r}$, the sum-of-pairs family gives exactly the supports realizable by intersections of quadratic queries.

More generally, suppose any number of equations is allowed and the cost is their maximum degree. The minimum degree defining the symmetric-difference form above is exactly $\mu$. On $U$ every equation that holds on $U\setminus V$ extends across the omitted codimension-$\mu$ subflat if its degree is less than $\mu$, by the same minimum-weight bound. Degree $\mu$ suffices by asserting the common affine preconditions and that the two $\mu$-fold products sum to one. For the sum-of-pairs form, affine equations suffice at $\mu=1$ and degree two is necessary and sufficient at $\mu\ge2$. In the latter case its size inside its ambient flat is a power of two times $2^\mu-1$, which is not a power of two. A nonempty conjunction of affine equalities always has power-of-two size. For quadratics the extension principle also has a direct local proof. Around any omitted point choose three directions independent modulo the intersection. The other seven corners of their cube are in $U\setminus V$. Every quadratic true there is true at the eighth corner. [Lean check of the punctured-cube rule for whole families of equations](../lean/TraceProductPositiveCertificates.lean)

## A restriction of the cubic on a flat

Suppose $U$ has binary dimension $2m$, with direction $W$, and $F|_U$ vanishes outside a codimension-$\mu$ subflat for some $\mu\ge2$. In relative affine coordinates $y$ make the subflat $y_1=\cdots=y_\mu=1$. The unique multilinear polynomial of the restricted function is

$$
 F|_U(y)=y_1\cdots y_\mu\,g(y_{\mu+1},\ldots,y_{2m}).
$$

The right-hand side agrees everywhere when $g$ is the subflat restriction. Uniqueness and the disjoint variables give $g=0$ or $\deg g\le3-\mu$. For $\mu>3$ the restriction vanishes. For $\mu=3$ its degree-three part is zero or a product of three independent linear forms. For $\mu=2$ its degree-three part is $y_1y_2 L$ for a linear form on the remaining coordinates. Consequently for any shift $z\in W$ the polar bilinear form of $D_z(F|_U)$ has rank at most two. Indeed the third difference of a product of three linear forms is their determinant on the three directions. At fixed $z$ this is the pullback of an alternating form on a three-dimensional bit space, of rank at most two. Lower-degree terms make zero contribution to the third difference.

On the ambient space the same polar form is $(s,h)\mapsto\operatorname{Tr}(\det(z,s,h))$. For $z\ne0$ its radical is $Kz$, so factoring by $Kz$ leaves a binary symplectic space of dimension $2m$. Write $d_z=\dim_{\mathbb F_2}(W\cap Kz)$. The image of $W$ in the quotient has dimension $2m-d_z$. Its radical has dimension at most $d_z$, the dimension of its ambient symplectic orthogonal complement. The restricted rank is at least $2(m-d_z)$. Thus $d_z\ge m-1$ for each nonzero $z\in W$. [Ambient derivative rank and affine restrictions](quadratic-table-coefficient-cost.md)

If $W$ spans $K^3$ over $K$, choose three $K$-linearly independent vectors $z_1,z_2,z_3\in W$. Their three field lines form a direct sum. Hence $W$ contains a binary subspace of dimension at least $3(m-1)>2m$ for $m\ge4$, a contradiction. Its field span must be a $K$-plane, since a $K$-line has only $m$ binary dimensions. This plane and $W$ have the same binary dimension, making them equal. Therefore $U$ is a translate of a $K$-plane. The same conclusion holds if $F$ vanishes on all of $U$, since then it vanishes outside any chosen subflat there.

## Why the symmetric difference cannot be a transcript

Only $\mu=2$ remains. If $F=0$ on $U\mathbin{\triangle}V$, the support of $F|_U$ lies inside $U\cap V$, and likewise on $V$. Both are therefore translates of $K$-planes by the restriction argument. They are distinct and intersect. Two distinct intersecting affine planes in $K^3$ meet in a $K$-line, of binary dimension $m$. Yet $U\cap V$ has dimension $2m-2>m$, a contradiction. This excludes the last symmetric difference.

## Which single planes survive?

It remains to identify the affine $K$-planes $U$ on which $F=0$. Permuting the three field coordinates, any affine plane is a graph $w=au+bv+c$. For every $u,v\in K$ the zero-trace condition reads

$$
 0=\operatorname{Tr}(au^2v+buv^2+cuv)
  =\operatorname{Tr}\big(v[au^2+(bu)^{q/2}+cu]\big).
$$

The second equality uses invariance of the absolute trace under the $q/2$ power and $v^q=v$. By nondegeneracy of the trace pairing, $au^2+b^{q/2}u^{q/2}+cu$ vanishes for every $u$. The degrees $2,q/2,1$ are distinct for $m\ge3$ and are all below $q$, so the polynomial is identically zero and $a=b=c=0$. Restoring the coordinate permutation gives exactly the three stated planes.

Each plane has a certificate of depth $t$: for each pair $s_1,s_2$ of coordinate bits in the chosen field element, require $(1+s_1)(1+s_2)=1$. For any other input, give its first field element $u_0$, use $t$ questions to check its bits against $u_0$ in pairs, and use one more quadratic question for $\operatorname{Tr}(u_0vw)$. This proves the asserted pointwise minimum for all inputs. A procedure seeking a short certificate can choose the questions for its particular input. Finding or verifying the underlying native verdict without the granted quadratic answers remains a separate computational requirement. Historical priority for this equality classification has not been established.

The same extremal leaves persist if the oracle may inspect any additional binary variables independent of the field coordinates and the target ignores those variables. For each fixed assignment of the extra bits, the sliced transcript is empty or one of the three plane indicators already classified. Consider only the degree-$m$ monomials supported on the $3m$ field bits in the multilinear expression for $P$. These coefficients are unchanged by fixing the extra bits: a mixed monomial that contained the same $m$ field bits and at least one extra bit would exceed total degree $m$. Each plane indicator has a different degree-$m$ part, namely the product of all $m$ bit variables in its own coordinate block; the empty indicator has none. Consequently a nonempty leaf has the same plane on every slice. It is exactly that coordinate plane times the entire set of extra assignments.

## The exceptional even dimension

For $m=2$ every zero answer has a one-question certificate, including when $uvw$ is nonzero. If $u$ or $v$ vanishes its coordinate plane suffices. Otherwise the existence of $b\in\mathbb F_4$ with $w=b^2u+bv$ is equivalent, on substituting $b=(v/u)y$, to $y^2+y=uw/v^2=uvw$, since $v^3=1$. The image of $y\mapsto y^2+y$ is exactly the trace-zero set: its kernel has size two and its image has zero trace. Each plane $w=b^2u+bv$ has trace product identically zero, also at the points with $uv=0$. Its two binary affine equations are checked in one quadratic question. A zero-query certificate is impossible since $F$ takes both signs, and the companion proof gives minimum two questions for a positive answer. The coincidence of the powers $2$ and $q/2$ in this field explains the extra planes.
