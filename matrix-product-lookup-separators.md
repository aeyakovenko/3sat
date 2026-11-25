# A quadratic separator bound for binary matrix-product lookups

Write H for triples of binary d by d matrices, N=dim H=3d², and F(A,B,C)=tr(ABC). Consider any identity on the whole binary input space

$$
 F(x)=Q(x)+\sum_j h_j(P_jx+a_j)
$$

where Q is any Boolean polynomial of degree at most two, the sum is XOR, the h_j are arbitrary Boolean functions, and P_j are linear. The scope of a lookup is the row space of P_j. Its width is that space's dimension. Put all the lookups at the leaves of an arbitrary subcubic tree. On an edge, let U and V be the sums of the scopes on the two sides and put k_e=dim(U∩V).

**Theorem.** Either a lookup has width at least N/2, or an edge has k_e≥2N/9=2d²/3. No limit on the number of lookups is needed. The bound has the largest possible asymptotic order, since all the scopes lie in an N-dimensional space. The proof also holds on affine fibers of codimension o(d²) with an o(d²) loss. It uses no matrix multiplication exponent bound.

This width is the branchwidth of a subspace arrangement for a prescribed tree. Earlier tensor-network work relates contraction cost to the width of a tensor network. Here the scopes may mix entries of all three matrices linearly, each leaf's function can be arbitrary, and the cost measure is the intersection of the linear spans. Priority for this specific bound has not been established. [Jeong, Kim and Oum, *Finding Branch-Decompositions of Matroids, Hypergraphs, and More*](https://doi.org/10.1137/19M1285895) · [Austrin, Kaski and Kubjas, *Tensor Network Complexity of Multilinear Maps*](https://arxiv.org/abs/1712.09630).

## An edge and its private directions

The argument includes the full-space and affine-fiber statements at once. Suppose the identity holds for all x in x₀+L, a fiber of dimension aN, with a=1−δ and codimension b=δN. Restrict the dual scopes to L*. For the moment suppose U+V=L*. Define X=V^⊥ and Y=U^⊥ inside L, p=dim X/N, q=dim Y/N, and κ=k_e/N. Then p+q=a−κ. Differences in an X direction leave every lookup on side V fixed; differences in a Y direction leave side U fixed. A third difference removes Q. Thus

$$
\Omega(X,Y,L)=0, \qquad \Omega=\Delta^3 F .
$$

Here the third finite difference (in three potentially distinct directions) is a trilinear alternating form independent of the base point. For three pure matrix units of different colors, its value is one exactly when they make a composable triangle A_ij,B_jk,C_ki. All evaluations on other unit triples vanish.

## Simultaneously degenerating three subspaces

Extend the scalars of X,Y,L and Ω to the algebraic closure of the binary field. A diagonal change of basis in each of the three index spaces acts on triples by

$$
 (A,B,C)\mapsto(D_1 A D_2^{-1},D_2 B D_3^{-1},D_3 C D_1^{-1}).
$$

It preserves F and Ω. Its characters on the matrix units are all distinct: they are the oriented differences between two labeled basis coordinates of consecutive index spaces. Choose integer weights for the diagonal variables avoiding all the finitely many equal-weight hyperplanes, and substitute powers of a common z. Echelon bases in the resulting weight order, rescaled by their pivot powers, limit at z=0 to coordinate bases. Apply the same action to all three spaces. The limiting spaces X′,Y′,L′ keep their respective dimensions and satisfy Ω(X′,Y′,L′)=0 by trilinearity, either by taking these limits of the individual basis evaluations or by closedness. The argument only needs their dimensions after the limit; it allows X′ and Y′ to overlap.

Now put a vertex at each of the N matrix units. Join differently colored vertices if they extend to a composable triangle. Each edge has a unique completing third vertex. Each vertex completes precisely 2d directed edges from the other two colors. Let e(X′,Y′) count directed edges from the coordinate set of X′ to that of Y′. All their completions miss L′, hence

$$
 e(X′,Y′)\le 2db .
$$

## The mixing calculation

This undirected graph has degree 2d. Its normalized adjacency T has operator norm at most 1/2 on the orthogonal complement of the global constants, over the reals. To verify the spectrum, split each real table on a color into its grand mean, the zero-mean functions of its row alone and of its column alone, and the tables with every row and column sum zero. The latter go to zero under T. For each shared index, the two spaces of zero-mean functions that use it at the ends of its adjacent colors are swapped with multiplier 1/2. On the three grand means T is the normalized adjacency of a triangle, with eigenvalues 1,−1/2,−1/2.

Subtract the means from the indicators of X′,Y′ and apply Cauchy–Schwarz with uniform vertex measure. This gives

$$
 pq-\tfrac12\sqrt{p(1-p)q(1-q)}\le \frac{e(X′,Y′)}{2dN}\le\delta.
$$

In the full-space case it yields 3pq≤1−p−q=κ. More generally, if pq>δ, squaring and dividing by pq gives 3pq≤1−p−q+8δ−4δ²/(pq)≤κ+9δ. If pq≤δ the same final bound follows directly. This is a finite-dimension constraint on *every* cut.

## A balanced edge

The scopes on a fiber need not span L*. Adjoin a basis of a complementary subspace as one-dimensional scopes of identically zero lookups. Attach their subcubic tree by subdividing an old edge, or use a common attachment vertex for a lone original leaf. The new scopes are independent of each other and of the old span. They preserve every old edge width under subdivision, and edges entirely separating new leaves have width zero. On the whole input space the complement is unnecessary: a direction annihilating all scopes would be in the radical of Ω, and testing two pure complementary matrix units retrieves each coordinate of that direction.

Select a basis of L* from the union of the scopes and assign each vector to a leaf containing it. Give a leaf its number of assigned basis vectors as weight. With all leaf weights below aN/2, a weighted centroid lies at an internal vertex. Indeed, start anywhere and move into a component of weight greater than half until no such component remains. At the final internal vertex the largest incident component has between aN/3 and aN/2 basis weight because the degree is at most three. Its edge divides the tree into sides of basis weights at least aN/3 each. Thus both dim U and dim V are at least aN/3. In particular

$$
 \min(p,q)\ge a/3-\kappa,\qquad p+q=a-\kappa.
$$

For κ<a/3 their product is at least (a/3−κ)(2a/3). With 3pq≤κ+9δ this proves

$$
 \kappa\ge \frac{2a^2/3-9\delta}{1+2a}.
$$

This last bound also follows trivially when κ≥a/3. If the right hand side is positive, this edge has positive width and corresponds to an original edge. For a fiber with dim L>2 the dummy leaves have width below dim L/2 and cannot violate the leaf hypothesis. Therefore either an original scope has width at least dim L/2 or the displayed separator bound holds when the right side is positive. In particular, subquadratic leaf width and b=o(N) force k_e≥(2/9−o(1))N. Taking L=H gives the claimed unconditional full-space theorem.

## Why this does not yet exclude a linear SAT solver

A near-linear deterministic SAT algorithm would yield a near-quadratic deterministic evaluator for the single bit tr(ABC). The proof above would preclude such an evaluator if its computation were an XOR of functions of small affine projections, with small intersections along a tree, on even one high-dimensional affine fiber. Native instructions compose nonlinearly, and assigning auxiliary variables to their outputs guarantees identity only on valid traces. Their constraint set need not contain the required fiber. Even the relation t=u·v loses validity under a projection that changes t while fixing u and v. The graph bound gives an obstruction to that missing representation theorem. [Reduction to the scalar matrix contraction](verifying-matrix-products-from-sat.md).

The finite audit verifies the unique third vertex for every edge and the integer adjacency identity A³−d²A=2dJ for 1≤d≤5, where J is the all-ones matrix. It checks every zero-edge pair at d=1,2 by maximizing the second set for each first set. It also checks sampled fiber edge counts and the squared mixing inequality in exact integer arithmetic. [Finite graph audit](matrix_product_lookup_separator_audit.py).

## Arbitrary two-party protocols on a fixed linear split

There is also a communication lower bound with unrestricted local Boolean computation. Fix a public point $x_0$, and two binary subspaces $X,Y$ of the triple-matrix space, with $L=X\oplus Y$. Give Alice $x\in X$ and Bob $y\in Y$; they must compute $F(x_0+x+y)$. Write $p=\dim X/N$, $q=\dim Y/N$, and $\delta=1-p-q$. If $p,q$ are bounded away from zero and $\delta=o(1)$, every deterministic exact protocol needs $\Omega(d^2)$ bits for large $d$, even with an arbitrary public quadratic added to the verdict. The statement holds for each public point separately. The players can share any preprocessing independent of $x,y$.

To see this, let $r$ be the maximum rank over the algebraic closure of the bilinear form $\Omega|_{X\times Y\times\{z\}}$ as $z$ ranges over the scalar extension of $L$. Having maximum rank at most $r$ is a closed condition on the triple of subspaces of fixed dimensions: in local bases it is the simultaneous vanishing of every coefficient of the $(r+1)$-minors in the coordinates of $z$. Apply the diagonal degeneration above to $X,Y,L$. In the three resulting coordinate sets at least
$$
2dN\bigl(pq-\tfrac12\sqrt{p(1-p)q(1-q)}-\delta\bigr)
$$
directed edges between the first two sets have their completing coordinate in the third set. Under the hypotheses the bracket is bounded below by a positive constant (at $p+q=1$ it is $pq/2$). Some ordered pair of matrix colors accounts for at least a sixth of these good edges. In the remaining color choose a uniformly random permutation matrix and erase its entries outside the third coordinate set. Each good edge of the chosen colors survives with probability $1/d$. In the corresponding pair of pure blocks the resulting bilinear coefficient matrix is a partial permutation: with the shared index fixed, a chosen permutation pairs each outer index to at most one other. Its rank is precisely its surviving edge count. Thus a choice has rank $\Omega(d^2)$, and closedness gives that lower bound for the original $r$.

A nonzero $r$-minor over the algebraic closure need not stay nonzero at a binary point. To get a binary shift, view this minor as a nonzero polynomial of degree $r$ in coordinates for $z$ in a binary basis of $L$. At a bit point where the matrix has rank $t$, the minor vanishes to multiplicity at least $r-t$ if $t<r$, by constant row reduction of its specialized square matrix. The multiplicity form of Schwartz–Zippel bounds the average multiplicity on the binary grid by $r/2$. Consequently some binary shift gives rank at least $r/2$. [Dvir, Kopparty, Saraf and Sudan, Lemma 8](https://www.cs.princeton.edu/~zdvir/papers/DKSS09.pdf)

Write this shift as $z=x'+y'$ in the two private spaces. Running a protocol twice, on $(x,y)$ and on $(x+x',y+y')$, computes the directional derivative with twice its communication plus constant output overhead. This derivative is quadratic. Its cross term is the binary bilinear matrix just obtained; its two unmixed parts and constant cost at most a constant number of bits. A bilinear phase of rank $t$ has a real sign matrix of rank $2^t$, by restriction to an invertible minor and orthogonality of the resulting distinct characters. A deterministic protocol with $C$ bits partitions into at most $2^C$ monochromatic rectangles under the public-output convention, so $C\ge t$. This proves the claim. Adding any quadratic to $F$ changes its first derivative only by an affine term.

The input itself has $N$ bits, and a player can send its entire input in $O(N)$ bits. The lower bound matches that order across every balanced complementary linear split. An unrestricted RAM can bring the two groups of words into one workspace, and this communication statement alone gives no bound beyond the cost of transferring the input. Priority for the arbitrary mixed-linear-split version is unverified.
