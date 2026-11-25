# Extracting a tensor from arbitrary word lookups on one affine fiber

On an affine fiber $x_0+L$ of binary matrix triples suppose the following expression gives the correct verdict $F=\operatorname{tr}(ABC)$ on every point:
$$
       F(x)=Q(x)+\sum_j g_j(P_j x).
$$
All sums are binary. The quadratic $Q$, the affine tests defining the fiber, the affine maps $P_j$ and the Boolean truth tables $g_j$ may depend on the fiber. Write $r_j$ for the rank of the linear part of $P_j$ restricted to $L$, and $b$ for the codimension of $L$ in the original $3d^2$ bits. Put $S=\sum_{j:r_j\ge3}2^{r_j}$. Then
$$
  \underline R(M_{(d-\lfloor\sqrt b\rfloor)_+})\ \le\ S.
$$
Consequently $b\ge(d-S^{4/9})_+^2$ using the external $9/4$ exponent. For instance, if the expression has $d^{2+o(1)}$ tables of rank at most $(1/4-\epsilon)\log_2d$ for a fixed $0<\epsilon<1/4$, it needs $(1-o(1))d^2$ independent affine answers on every input. All the source bits may mix within each table. [Affine restriction theorem and external exponent](affine-restrictions-of-one-large-matrix-product.md)

## From an arbitrary truth table to a trilinear tensor

Fix a single binary basis $v_1,\ldots,v_m$ of $L$ and base point $x_0$. For each lookup make a three-index array by taking its eight-corner sums along ordered triples of basis vectors. A high-degree table need not have trilinear differences as functions of arbitrary directions. We use only these sampled coefficients. Adding all the arrays gives precisely the coefficient tensor in the chosen basis of the cubic's third derivative, since $Q$ has zero third differences. Thus a per-table geometric border-rank bound for its array suffices. Inputs to the lookup may be identified with $r$ bits after an affine change on its image. For $r\le2$ the whole truth table is a quadratic and its contribution vanishes.

Over $K=\overline{\mathbb F}_2$ take the group algebra of the binary additive group of dimension $r$:
$$
 E=K[t_1,\ldots,t_r]/(t_1^2,\ldots,t_r^2),\qquad
 e_u=\prod_{i:u_i=1}(1+t_i).
$$
The $e_u$ form a basis (their expansions in squarefree monomials are triangular), with $e_u e_v=e_{u+v}$. Let $u_i$ denote the lookup signature of $v_i$, and absorb the lookup's base-point offset into its truth table $g$. Define the linear functional $\lambda(e_u)=g(u)$. For entries $i,j,k$ the array is
$$
       \lambda\big((1+e_{u_i})(1+e_{u_j})(1+e_{u_k})\big).
$$
Indeed its expansion runs over the eight translated inputs with their correct multiplicities, including repeated directions. The array is therefore a linear restriction of the trilinear form $(X,Y,Z)\mapsto\lambda(XYZ)$ on $E$.

Replace each relation $t_i^2=0$ by $t_i^2=z t_i$ for one parameter $z$. The squarefree monomials are a basis for the whole family over $K[z]$, by successive division by monic polynomials. Multiplication in that basis is polynomial in $z$. Extend $\lambda$ by keeping its values on this basis fixed. For $z\ne0$, evaluating polynomials on $\{0,z\}^r$ identifies the algebra with $K^{2^r}$ with coordinatewise multiplication. Any linear functional in evaluation coordinates is a sum of weighted coordinates, so this trilinear form has rank at most $2^r$. Taking $z=0$ gives the bound on geometric border rank. Summing the restricted arrays gives border rank at most $S$, by subadditivity. Combine with the affine-fiber theorem. This explicit family is an instance of the algebra-smoothing method. [Bläser and Lysikov, *On Degeneration of Tensors and Algebras*](https://doi.org/10.4230/LIPIcs.MFCS.2016.19)

## How expensive can one lookup be?

For every $r\ge3$ there is a single table of rank-$r$ affine inputs whose sampled array has flattening rank $2^r-r-2$. Use one source basis direction for every nonzero $u\in\mathbb F_2^r$, send it to $u$, take base point zero, and use the AND of all $r$ address bits. In the squarefree basis, $\lambda$ is the coefficient of $t_1\cdots t_r$, since this coefficient in $e_u$ is precisely the AND of $u$. The $1+e_u$ for nonzero $u$ are a basis of the augmentation ideal $I=(t_1,\ldots,t_r)$. They belong to $I$, and linear independence follows from the group-element basis.

The kernel of the first flattening on $I^3$ consists of $X\in I$ for which $\lambda(X I^2)=0$. All monomials of degrees $r-1$ and $r$ belong to this kernel. For a monomial of degree at most $r-2$ with nonzero coefficient in $X$, multiply by its complementary monomial. The latter belongs to $I^2$ and isolates precisely that coefficient in top degree. Thus the kernel has dimension $r+1$, and the rank is $(2^r-1)-(r+1)$. This gives an exponential obstruction to reducing the extraction cost of each arbitrary lookup in isolation. At $r>3$ the single-gate example has Boolean degree greater than three. Cancellations among several gates of a globally cubic expression remain a possible way to improve extraction.

The fixed-layout SAT reduction supplies the exact scalar answer. A near-linear RAM program may compose many word operations and use addresses of full logarithmic width. To use this theorem against such a program would require controlling the ranks and additive organization of its surviving lookups on a large affine fiber. No such conversion has been proved. [Reduction](verifying-matrix-products-from-sat.md) · [Earlier separate-input extraction](separate-word-inputs-to-a-trilinear-verdict.md) · [Finite audit](affine_matrix_lookup_audit.py)

## When the exponent in the per-table charge can be avoided

Suppose the dual address spaces on $L$ have dimensions at most $w$ and are the leaves of a subcubic tree. For each edge intersect the two spans of the leaves on either side. Let $k$ be the maximum dimension of these intersections and $r$ the dimension of the total span. For **any globally cubic Boolean function** equal to the XOR of the tables plus a free quadratic, its third derivative has ordinary tensor rank at most $3r\max(w,2k)$.

Translate the fiber to the origin and subtract the free quadratic. At each internal vertex add a zero table on the sum of its three incident edge intersections. This sum has dimension at most $2k$. Indeed, writing the incident components' spans as $U,V,W$, any vector in $U\cap(V+W)$ is the sum of a vector in $V\cap(U+W)$ and one in $W\cap(U+V)$. The same holds cyclically. Across each original cut the bags on either side lie in their original side's span. For an internal vertex on that side, two of its three branches are wholly on that side and their two edge intersections span its bag. The two endpoint bags both contain the edge intersection.

Peel a leaf of the current bag tree. Let $J$ be its current scope, $R$ the span of the remaining scopes and $B=J\cap R$. Then $B$ lies in the neighboring bag: by the original cut property it is contained in the old edge intersection and the neighbor retains its full scope when a new table is absorbed. Choose a linear projection on dual forms fixing $R$ and killing a complement to $B$ in $J$. Pullback on Boolean functions by the corresponding primal linear map preserves degree. If $f$ is the current cubic sum and $h$ the leaf table, then $f+\pi f=h+\pi h$. This is cubic, depends only on $J$, and vanishes when its $p=\dim J-\dim B$ private coordinates vanish. The projected sum $\pi f$ is again cubic. Absorb $\pi h$, which depends only on $B$, into the neighbor's table. At the last node take $R=0$.

In coordinates adapted to $B$, every degree-three monomial of $h+\pi h$ contains a private variable. Assign each to its first private variable and factor, giving at most $p$ products of a linear variable with a quadratic on $J$. In the third difference of each product there are three choices for the direction assigned to that variable; the bilinear polar of the quadratic has matrix rank at most $\dim J$. The emitted derivative costs at most $3p\dim J$ ordinary rank. Each peel drops the total span dimension by exactly $p$, so these costs sum to at most $3r\max(w,2k)$. This handles nonlinear tables of logarithmic width with a small interface between the two sides of each cut. A separate argument gives a stronger width lower bound for the particular cubic $\operatorname{tr}(ABC)$. [Subspace arrangement model](https://arxiv.org/abs/1711.01381) · [Matrix-product separators](matrix-product-lookup-separators.md)
