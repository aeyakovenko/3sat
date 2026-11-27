# Affine certificates on the graph of binary matrix multiplication

Write $D=d^2$, $d\ge2$, and let $\mathcal G=\{(A,B,AB):A,B\in\mathbb F_2^{d\times d}\}$. An affine subspace lying in $\mathcal G$ has dimension at most $D$. If its dimension exceeds $D-(d-1)$, it lies in a full $D$-dimensional affine subspace of a specific form. The threshold is sharp. A quantitative version below applies at every deficit. These assertions concern an entire set of accepted inputs, so they apply equally to a completed parity-query transcript and to the projection of a linear system with arbitrary auxiliary witness bits.

## Classifying the large subspaces

Projection of an affine subset of the graph onto $(A,B)$ is injective. Denote the direction of the projected set by $V$, and a point of it by $(A_0,B_0)$. The change in the product along $(a,b)\in V$ is

$$
                   A_0b+aB_0+ab.
$$

It must be linear on $V$. In characteristic two this is equivalent to

$$
                       ab'+a'b=0\qquad((a,b),(a',b')\in V).
$$

Here $ab$ need not vanish by itself. The polar identity ensures additivity, which over $\mathbb F_2$ is linearity.

Let $P$ be the first projection of $V$, let $K=\bigcap_{a\in P}\ker a$ in the middle vector space, and put $U=\mathbb F_2^d/K$, $m=\dim U$. The space $Q$ of $b$ with $(0,b)\in V$ consists of maps into $K$, by the polar identity. View $P$ as a subspace of $\operatorname{Hom}(U,\mathbb F_2^d)$ of codimension $u$. Then

$$
 \dim V=\dim P+\dim Q\le dm-u+d(d-m)=D-u.
$$

For a pair over $a$ the induced map $b\bmod K$ is well defined independently of the choice of $b$. Denote it by $H(a):\mathbb F_2^d\to U$. For fixed $v$ set $L_v(a)=H(a)v$ and $t_v=\operatorname{rank} L_v$. Every $a'\in\ker L_v$ kills $\operatorname{im}L_v$, since $a'L_v(a)=aL_v(a')=0$. Thus

$$
                dm-u-t_v=\dim\ker L_v\le d(m-t_v),\qquad
                (d-1)t_v\le u .
$$

In particular, when $D-\dim V<d-1$, all $L_v$ vanish. The entire $V$ lies in the space

$$
       V_K=\{(a,b):aK=0,\ \operatorname{im} b\subseteq K\}.
$$

This space has dimension $D$ and has $ab=0$ identically. Through the same base point, adjoining all the directions $(a,b,A_0b+aB_0)$ for $(a,b)\in V_K$ gives the promised full affine subset of the graph. If the deficit is $h=D-\dim V$ without restriction, evaluating $H$ on a basis of $d$ vectors gives $\operatorname{rank}H\le du/(d-1)$. The given affine set and this full affine set therefore have common direction of dimension at least $D-h-dh/(d-1)\ge D-3h$.

For sharpness impose $a e_1=\lambda e_1$ and $b=\lambda e_1e_1^\mathsf T$, leaving the other columns of $a$ free. The product is $\lambda^2 e_1e_1^\mathsf T=\lambda e_1e_1^\mathsf T$. The resulting affine graph subspace has dimension $D-d+1$. The common kernel of its $a$'s is zero, while some $b$ is nonzero. It lies in no $V_K$ translate lifted to the graph.

## The information in the actual parity questions

An exact parity-query algorithm for product equality must query at least $2D$ independent bits on **every correct product**. Its actual accepting transcript is an affine coset in $3D$ variables contained in $\mathcal G$. Asking all $D$ bits of $A$ and then the $D$ parities $C_{ij}+(AB)_{ij}$ with $A$ fixed attains this bound. Below $2D+d-1$ independent questions the unobserved directions necessarily have the structure above. The explicit SAT mismatch formula makes correct products ordinary unsatisfiable formulas. [SAT encoding](verifying-matrix-products-from-sat.md)

There is a sharp fixed-space estimate. Draw $A,B$ independently uniformly and set $C=AB$. Let $S$ be any prespecified subspace of allowable parity questions on $(A,B,C)$, of codimension $w$. The probability that an exact algorithm's entire set of actual questions lies in $S$ is zero for $w>D$. For $0\le w\le D$ it is at most

$$
                              2^{-d\lceil w/d\rceil}.
$$

Indeed the whole coset of $S^\perp$ through any such input must be contained in the graph. If there is one such coset, then $S^\perp$ projects injectively to a $w$-dimensional space $V$ of $(a,b)$ directions. Fix one such base point. Every other possible base point differs in its first two coordinates by a pair $(X,Y)$ satisfying

$$
                         Xb+aY=0\qquad((a,b)\in V).
$$

This follows by subtracting the two actual product increments on the common directions. Conversely this condition suffices for the second graph coset with the same direction. The matrix constraints on $(X,Y)$ have at least $d\lceil w/d\rceil$ independent scalar equations. To see this, embed $\mathbb F_{2^d}$ in the $d$-square matrices via its regular representation. For each $R$ in this field, test the trace of $R(Xb+aY)$. Relative to the nondegenerate pairing $\langle(a,b),(X,Y)\rangle=\operatorname{tr}(aY+Xb)$, these tests have vectors $(Ra,bR)$ for $(a,b)\in V$. The maps $(a,b)\mapsto(Ra,bR)$ define a vector space action of the embedded field, since its matrices commute. The span of the tests includes the field span of $V$, of binary dimension divisible by $d$ and at least $w$. This proves the bound.

Equality can be attained for each $w$. Take $j=\lceil w/d\rceil$ and choose a $w$-dimensional coordinate subspace of $a$ supported on $j$ middle columns, using at least one unit from each, with $b=0$. Lift it with zero output component to form $S^\perp$. The needed and sufficient condition on an input of the graph is that the corresponding $j$ rows of $B$ vanish. Its probability is $2^{-dj}$. Query a basis of $S$, accept on graph-contained cosets, and complete the remaining cases with the other parities. This construction only gives a parity-query algorithm. A native RAM pays for obtaining arbitrary dense parities.

For any fixed prefix-free descriptions of allowable spaces, a union bound now gives a pointwise tradeoff. If a description of length $\ell$ contains all the questions actually asked and leaves $w$ dimensions unqueried, then $\ell\ge d\lceil w/d\rceil-j$ for all such descriptions except on a set of honest inputs of probability at most $2^{-j}$. This permits the description to be chosen after the run. Both a single fixed space and adaptive choices can thus be measured on genuine executions.

The finite audit enumerates all binary $2\times2$ graph directions, including all 54 nonsplit examples at the first threshold, and a shifted formula for which every data bit is sensitive at every honest input. The argument above is its own finite-dimensional proof. Historical priority for the quantitative stability and the fixed-space bound has not been established. [Finite enumeration](../audits/boolean_product_flats_audit.py) · [Use in lower bounds with existential witnesses](binary-witness-cost-of-matrix-products.md)
