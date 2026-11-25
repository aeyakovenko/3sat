# Determinant pencils and local matching gadgets for three-hole repair

Two simple cubic instances with the **same** auxiliary data can have opposite verdicts while agreeing on every coefficient of the following formal determinant over the integers:

$$
                    \det(\operatorname{diag}(x_0,\ldots,x_{q-1})+uP+vQ).
$$

Here $P,Q$ denote permutation matrices in the row-to-column convention. The equality includes the diagonal variables independently, so it gives equality of the corresponding weighted principal minors on every subset. Both instances can be promised to have at most one solution. A separate local obstruction below applies to weighted perfect-matching gadgets with independent invertible binary basis changes at every edge, including after contraction of the entire identity matching.

## A transpose with the same three holes

Take the following row arrays on 15 labels:

$$
\begin{aligned}
P&=(2,6,8,9,0,7,13,3,1,5,4,14,11,10,12),\\
Q&=(6,0,11,10,2,12,14,9,7,8,13,5,1,4,3).
\end{aligned}
$$

Put $A=I+P+Q$ and compare $A$ with the instance $I+P^{-1}+Q^{-1}=A^{\mathsf T}$. In both instances the vector $y$ with $y_0=-1$, $y_1=\cdots=y_6=1$ and all other values zero satisfies the integer equations with right side $\mathbf1$. In both, $T=\{1,2,10,14\}$ is a packing covering every row except $\{5,7,9\}$. The only perfect cover of $A$ is $\{1,2,3,5,13\}$, which removes two members of $T$. The transpose has none. These finite verdicts can be reproduced by trying the $\binom{15}5=3003$ possible selections of five labels in each orientation. Transposing the symbolic matrix proves the determinant identity without any finite-field sampling.

The identity survives independent indeterminates on the colored *unordered* endpoint pairs. Replace a marked $P$ entry at $(i,j)$ by $u_{\{i,j\}}$, and a marked $Q$ entry by $v_{\{i,j\}}$. The matrix for the inverse arrays is again exactly the transpose. The displayed $P$ has cycle lengths $8,4,3$ and $Q$ has cycle lengths $12,3$, so neither has a two-cycle. Consequently every nonzero entry in the connected example receives its own independent variable, even with this consistent identification across the two orientations. This comparison is of the full weighted determinant and all its principal minors. Labeling weights by ordered source and target supplies extra orientation data outside this comparison.

For arbitrarily large sizes, add disjoint six-label blocks with row arrays $(1,3,4,5,2,0)$ and $(5,2,1,4,0,3)$ to the primal instance and their inverses to the transpose. In both directions each block has just one exact cover, $\{2,5\}$, by checking the fifteen possible pairs. Append this common selection to both supplied packings and both signed solutions. The holes, the single negative coordinate, and the unique-versus-zero verdict persist. The two base instances are connected; the padded examples are disjoint unions. The [executable census](cover_pencil_audit.py) checks connectivity, every candidate cover, the two supplied vectors and the hole labels.

Thus even the complete pencil, the signed vector, the chosen partial packing and the identities of the uncovered rows leave this decision ambiguous. The actual arrays remain available to an ordinary solver. For example, swapping left and right reverses the order in noncommutative products of $P$ and $Q$.

## A local obstruction independent of planarity

The weighted matching signature of a graph with ordered external vertices is indexed by the subset removed before taking the weighted sum of perfect matchings. Its support has one Hamming parity because every remaining matched graph has even order. This necessary condition holds in all fields and for nonplanar graphs as well. Planar matchgates satisfy additional identities. We use only the parity condition. [Cai and Choudhary, *Some Results on Matchgates and Holographic Algorithms*](https://eccc.weizmann.ac.il/report/2006/048/)

The bipartite tensor network of exact cover has a copy tensor $C=|000\rangle+|111\rangle$ on variable vertices and an exact-one tensor $W=|100\rangle+|010\rangle+|001\rangle$ on clause vertices. Summing the product over shared bits counts covers. To include arbitrary one-variable weights, it is necessary in particular to handle all weights one. A one-wire basis change replaces the two ends of an edge by actions of $T$ and $T^{-\mathsf T}$ for invertible $2\times2$ matrix $T$. The choices may be different at every edge and may depend on the supplied packing.

Over characteristic different from two, one parity is the eigenspace of $Z^{\otimes n}$ for eigenvalue $+1$ or $-1$, with $Z=\operatorname{diag}(1,-1)$. At a copy vertex put $G_i=T_i^{-1}ZT_i$. Parity of its transformed tensor would mean $G_1\otimes G_2\otimes G_3$ fixes the line spanned by $C$. Across its first axis, its two slices span $\langle|00\rangle,|11\rangle\rangle$. The only rank-one lines in this space are the two displayed coordinate lines, since $\det(\operatorname{diag}(a,b))=ab$. The action on the two slice legs must preserve them both or interchange them. Looking at each choice of the sliced axis forces all three $G_i$ to be diagonal or all three antidiagonal in the original basis. In the diagonal case their eigenvalues on $|0\rangle$ and $|1\rangle$ are opposite on each leg, so the two copy terms acquire opposite signs. Thus every $G_i$ is antidiagonal. The dual pulled-back action at the clause end of each wire is $G_i^{\mathsf T}$, again antidiagonal. Their tensor product takes $W$ to a tensor supported on weight two, so it cannot fix its line. No choice of these bases makes all vertices parity-pure.

For characteristic two there is a different test. If a transformed tensor is supported on one parity, the sum of the single-leg actions of $\operatorname{diag}(0,1)$ has it as an eigenvector: on a basis string the eigenvalue is its Hamming weight in the field. Pull these operators back through the basis changes to matrices $D_i$ each of trace one. Whenever the original tensor's nonzero support strings are pairwise at distance at least two, only the diagonal entries of $D_i$ contribute at a supported string $b$. Dividing by that nonzero tensor entry gives the multiplier $\sum_i(D_i)_{00}+|b|$ in the field. Mixed-parity support therefore forbids every such basis change. This already applies to $C$ alone. Direct enumeration over $\mathbb F_2$ confirmed mixed parity for all $6^3=216$ copy transformations and all $6^4=1296$ transformations of the contracted signature below.

## Contracting the identity matching first

A variable and its neighboring exact-one clause paired along the identity incidence contract to the four-leg tensor

$$
             F=|00\rangle\bigl(|01\rangle+|10\rangle\bigr)+|11\rangle|00\rangle.
$$

This *single* signature fails the parity test after any four independent invertible binary basis changes, over every field. In characteristic two its three support strings have mixed parity and pairwise distance at least two, so the preceding argument applies immediately.

In other characteristics group its first two and last two legs. In the left slice space the two displayed rank-one lines must be preserved or interchanged as above. Interchanging them would require the right pair action to exchange the rank-one and rank-two lines spanned by $|00\rangle$ and $|01\rangle+|10\rangle$, respectively. Invertible local maps preserve matrix rank, so the left actions are diagonal. Each left matrix is conjugate to $Z$. Their product gives the *same* scalar on $|00\rangle$ and $|11\rangle$ because there are two left legs. The right product must therefore act by a single common scalar on $|00\rangle$ and $|01\rangle+|10\rangle$. Fixing the first line forces the right matrices to be upper triangular. If their first diagonal entries are $a,b\ne0$, their second entries are $-a,-b$. The coefficient on $|00\rangle$ in its own image is $ab$, whereas each of the $|01\rangle,|10\rangle$ coefficients in the other image is $-ab$. Equality is impossible in characteristic different from two.

The obstruction applies to exact local signature realization on a single binary wire per incidence. It does not presume that general formulas are planar. A uniform procedure using global matrix entries or a different encoding would require a separate analysis. The [weighted generating-polynomial result](weighted-exact-covers-with-three-holes.md) addresses exact symbolic computation; the [three-hole repair reduction](path-augmentations-with-three-uncovered-points.md) states the unweighted RAM problem.
