# Algebraic degree when the product verifier sees both factors

Let $G_d(A,B,C)=[AB=C]$ for three independent $d$-square binary input matrices, where multiplication uses $\mathbb F_2$. Write $D=d^2$, and interpolate the Boolean verdict by its unique multilinear polynomial in all $3D$ input bits. Its coefficient at the monomial of **all** bits is exactly $2^{2D-d}$ over the integers. Hence the degree is $3D$ in every characteristic other than two. Over any field of characteristic two its degree $L_d$ satisfies
$$
 D+\lceil 3D/4\rceil \ \le\ L_d\ \le\
 2D-\max\!\left\{d-1,\left\lceil\frac{\lfloor D/4\rfloor}{2}\right\rceil\right\}.
$$
The values for $d=1,2,3,4$ are $2,7,16,28$. The asymptotic constants in these two characteristic-two estimates are $7/4$ and $15/8$. The estimates measure computation on the actual factor and proposal bits, including computations that mix the three banks in one parity query.

Consider exact field-weighted sums of adaptive decision trees. Charge the maximum number of queries on any branch and allow any number of trees. With coordinate queries the cost is exactly the multilinear degree. Each transcript indicator is a product of queried literals, and each monomial itself has a coordinate-query tree of depth its degree. Over a characteristic-two field this equality continues to hold for parity queries involving arbitrary subsets of all three banks. Each answer bit and its complement are affine polynomials over that field. In odd characteristic the coordinate conclusion applies as stated; a single parity per term can represent arbitrary Boolean functions by Walsh expansion when the sum size is unlimited. Thus a proposed superquadratic bound in $d$ cannot follow from weighted query depth on these inputs. Counting the number of terms or the network implementing them is a separate question. [Earlier hidden-product query model](parity-and-forbidden-entries-in-the-binary-product-graph.md) · [Carlet on Boolean algebraic normal forms and graph indicators](https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf)

## The signed integer coefficient

Write $|X|$ for Hamming weight. By Boolean Möbius inversion the full coefficient is
$$
 (-1)^{3D}\sum_{A,B}(-1)^{|A|+|B|+|AB|}.
$$
Let $u_k$ be the parity of column $k$ of $A$ and $v_k$ the parity of row $k$ of $B$. The three weight parities in the exponent add to $\sum_k(u_k+v_k+u_kv_k)$. Each choice of the $2d$ parity bits has $2^{2D-2d}$ preimages. The signed sum on each pair is $-2$. Since $3d^2+d$ is even, the stated positive power of two follows.

## A characteristic-two coefficient is a product of submatrix rank tests

Specify the support of a monomial in the entries of $B,C$. In column $j$ let its selected row indices be $T_j$ in $B$ and $U_j$ in $C$, with sizes $t_j,u_j$. Its coefficient, before expanding in the entries of $A$, is the Boolean function
$$
 H(A)=\prod_{j=1}^d [\operatorname{rank} A_{\overline{U_j},T_j}=t_j].
$$
Indeed Möbius inversion in characteristic two sums the verdict on inputs whose ones lie in the respective selected positions. For fixed $A$ and one column, the admissible pairs consist of $b$ supported on $T_j$ with $(Ab)_{\overline{U_j}}=0$, and the uniquely determined $c=Ab$. The count is a power of two with odd parity exactly when the kernel is zero. The choices for distinct columns are independent.

For any $p$-by-$t$ matrix $M$ of binary variables, the full column rank test has a polynomial of degree at most $p$. A representing expression is
$$
 \sum_{v\in\mathbb F_2^t}\ \prod_{i=1}^p (1+(Mv)_i).
$$
It counts the kernel modulo two. This degree bound still applies after substituting affine forms for the entries of $M$.

## A monomial from disjoint diagonals

Choose the $d$ longest diagonals parallel to the main diagonal of the $d$-square array, breaking the last tie arbitrarily. Their lengths sum to $m=D-\lfloor D/4\rfloor=\lceil3D/4\rceil$. Indeed the full list of lengths is $d,d-1,d-1,\ldots,1,1$. For each chosen diagonal use one output column $j$. Let $T_j$ be its column index set and $\overline{U_j}$ its row index set. Then $t_j+u_j=d$, and $H(A)$ is a product of the corresponding square minors. The $B,C$ monomial already has degree $D$.

Order the $A$ variables lexicographically in row-major order with the earlier variable larger. The leading monomial of each ordinary minor is its diagonal product, by taking the smallest available column in each successive row. The leading monomial of the product of minors is the product of those leading terms. It has degree $m$ and is squarefree because the selected diagonals are disjoint. Every ordinary term of the product has degree $m$. Reduction on binary inputs can only turn a nonsquarefree term into a monomial of strictly smaller degree, so the leading squarefree monomial survives. This proves the lower bound.

## Averaging over square-zero shears

Fix a full ANF monomial with nonzero coefficient. Let $\alpha$ and $\beta$ be the numbers of omitted $A$ and $B$ bits and $u=\sum_j u_j$ the number of selected $C$ bits. Its degree is $2D-\alpha-\beta+u$. Since $H$ is nonzero, each $t_j+u_j\le d$, hence $\beta\ge u$. The direct kernel formula gives $\deg H\le D-u$. A nonzero monomial on $D-\alpha$ entries of $A$ therefore has $\alpha\ge u$.

Its coefficient is the parity of the sum of $H(A)$ over all $A$ vanishing at the $\alpha$ omitted positions. Stratify this sum by $\ker A$ and $\operatorname{im} A$, including all dimensions. In a stratum of rank $k$, choose bases present throughout that stratum. The induced isomorphism from the quotient by $\ker A$ to $\operatorname{im} A$ has one variable matrix $X\in\mathrm{GL}_k(2)$. Every entry of $A$ is linear in $X$. The condition on its $\alpha$ omitted entries thus has an indicator of degree at most $\alpha$ in $X$.

If the quotient map kills a nonzero vector on the coordinate span of some $T_j$, the entire stratum contributes zero. Otherwise its image is a fixed $t_j$-plane $V_j$ in the quotient. In the chosen image coordinates, write $W_j$ for the intersection of $\operatorname{im} A$ with the span of the coordinate axes in $U_j$. The rank test is precisely $XV_j\cap W_j=0$. This is the full column rank test for the map
$$
 W_j\ \xrightarrow{\ X^{-1}\ }\ \mathbb F_2^k
       \ \longrightarrow\ \mathbb F_2^k/V_j .
$$
In fixed bases its matrix has $k-t_j$ rows, with entries linear in $X^{-1}$. Thus all rank tests together have a representation in the entries of $X^{-1}$ of degree at most $\sum_j(k-t_j)=\beta-d(d-k)$.

Split $k=p+q$ as evenly as possible. The subgroup of block matrices with identity diagonal blocks, zero lower-left block and arbitrary upper-right $p$-by-$q$ block is a binary cube of dimension $pq=\lfloor k^2/4\rfloor$. Each element is its own inverse. On each left coset both $X$ and $X^{-1}$ are affine functions of the $pq$ block bits. The summed indicator therefore has degree at most $\alpha+\beta-d(d-k)$ on the cube. Its parity over a whole coset is zero if this degree is smaller than $pq$, because every lower-degree monomial omits a free bit. At least one coset in some stratum has odd parity. Consequently
$$
 \alpha+\beta\ \ge\ d(d-k)+\lfloor k^2/4\rfloor\ \ge\ \lfloor d^2/4\rfloor .
$$
The last inequality follows from $(d^2-k^2)/4\le d(d-k)$. Since $u\le\min(\alpha,\beta)$, the degree loss $\alpha+\beta-u$ is at least half this bound, rounded up.

There is also a small-size improvement. Write $n_0$ for the number of columns with $t_j=d$. Such a column has $u_j=0$ and contributes exactly $\det A$ to $H(A)$. Multiplying its indicator by itself has no effect on binary inputs. The direct rank degree bound becomes $\deg H\le D-u-d(n_0-1)_+$, so the loss is at least $\beta+d(n_0-1)_+$. Also $\beta\ge d-n_0$. This gives loss at least $d-1$ at every $d$ and yields the displayed upper bound.

## Closing the one-degree gap at side four

For $d=4$ the bounds leave 28 and 29. If degree 29 occurred, the loss would be 3. The repeated-determinant bound requires $n_0=1$ and $\beta=3$. Indeed $n_0=0$ forces $\beta\ge4$, $n_0\ge2$ costs at least four by repetition, and $n_0=1$ gives $\beta\ge3$ and loss at least $\beta$. Thus one column contributes $\det A$ and each other $T_j$ omits exactly one coordinate. Also $\alpha=u\le3$ since loss equals $\beta$. The sum is confined to invertible matrices. Each remaining column with $u_j=0$ contributes one. With $u_j=1$ its minor is the single entry of $A^{-1}$ in the omitted column and row order, by the cofactor formula and $\det A=1$. The coefficient therefore belongs to the span of mixed moments over $\mathrm{GL}_4(2)$ of at most three entries of $A$ and at most three entries of $A^{-1}$. Here the factors that require a pinned entry of $A$ to vanish are $1+A_{ij}$.

The audit enumerates the 20,160 invertible matrices, checks their inverses by multiplication and computes every one of the $697^2=485,809$ mixed moments by binary parity. Every moment vanishes, excluding degree 29. The disjoint-diagonal certificate attains degree 28. This last exclusion is a finite computational proof.

The audit computes the full coefficient function for every multiset of column supports through side three and applies an independent Möbius transform in $A$. It also evaluates the odd-field integer coefficient by summing over every factor pair through side three, and computes the entire graph ANF by direct truth-table inversion at sides one and two. These bounds concern an unrestricted input domain and a restricted measure of implementation cost. A RAM running time or a tensor network volume does not equal its weighted query depth. [Exact audit](../audits/direct_product_graph_degree_audit.py)
