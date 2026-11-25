# Quadratic correlation of matrix multiplication up to a polynomial factor

Let $M_d$ be the largest absolute correlation of $\operatorname{tr}(ABC)$ with a quadratic Boolean polynomial on all entries of three independent uniform binary $d$-square matrices. There are absolute constants $c,C>0$ such that
$$
 c\,2^{-3d^2/4} \ \le M_d\le\ C(d+1)^{97}2^{-3d^2/4}.                 \tag{1}
$$
The power $97$ is a coarse bound. The proof uses a necessary condition for a derivative to have nonzero bias. Replacing the derivative by its polar-rank bound alone incurs an exponential loss in $d$, even on invertible shifts. [Polar forms, graded centralizers and the constant lower bound](quadratic-correlation-for-one-large-matrix-product.md)

## A normalized sum over shift types

Use the three-cycle grading of the companion proof. Write $T(x)=\operatorname{tr}_V(x^3)$ for the cyclic arrow triple $x$ and fix a quadratic $Q$. If $u$ is a shift, put $c_j=\dim\{v\in E_j:vu=uv\}$. Write $I_Q(u)=1$ if $D_u(T+Q)$ has nonzero mean sign, and zero otherwise. Then
$$
 |\mathbb E\chi(T+Q)|^2\le 2^{-3d^2/2}
                   \mathbb E_{u\in E_1} 2^{c_1(u)/2} I_Q(u).           \tag{2}
$$
For $I_Q(u)=1$ and every $v\in C_1(u)$, the second difference $D_vD_u(T+Q)(0)$ must vanish. Indeed every such $v$ belongs to the polar radical of the quadratic derivative, and a nonzero constant difference reverses every sign.

The group $G=\mathrm{GL}_d(2)^3$ acts by grading-preserving change of bases. The contribution of an orbit with representative $u$ to the expectation in (2) is at most
$$
 \frac{2^{c_1(u)/2}}{|\operatorname{Aut}(u)|}\,
          \Pr_{g\in G}[I_Q(gug^{-1})=1],                                \tag{3}
$$
because $|G|/|E_1|\le1$ and uniform $g$ gives the uniform orbit distribution. The stable nilpotent and invertible parts of $u$ are graded. A commuting homogeneous map preserves both, regardless of its degree. The factor $2^{c_1/2}/|\operatorname{Aut}(u)|$ consequently splits across these parts. On the invertible part all three spaces have the same dimension and $c_1=c_0$, by multiplication by $u$.

There are two kinds of blocks to count. On the nilpotent part they are graded Jordan chains, specified by starting grade and length. On the invertible part two arrows can be identified with identities and the monodromy on the third has its ordinary primary decomposition. A nonconstant monic irreducible $p\ne X$ of degree $e$ with partition $\lambda$ represents the modules $\mathbb F_2[X]/p^\ell$ for the parts $\ell$ of $\lambda$. Homogeneous degree-zero endomorphisms there are precisely the endomorphisms commuting with the monodromy. Distinct primary parts have no intertwining maps, by Bézout, and $u$ transports this assertion to degree one.

In either description $|\operatorname{Aut}|=2^{c_0}$ times an explicit unit fraction. For each multiplicity $m$ of identical blocks the factor in this fraction is $\prod_{j=1}^m(1-q^{-j})$, where $q=2^e$ in an invertible primary part and $q=2$ for graded nilpotent chains. To see this, reduce an endomorphism on the top of each chain, modulo $p$ in the primary module and modulo $u$ in the graded nilpotent case. Invertibility of the induced map on the quotient by $p$ or $u$ is equivalent to invertibility of the whole map, by iterating surjectivity down the finite filtration. Maps from a shorter chain into a longer one are zero on that target top, so the top map is triangular when ordered by length. For a given length and type, its diagonal is a uniform $m$-square matrix over the residue field, independently of the other diagonal blocks. In the graded nilpotent case different starting grades have separate diagonals. These diagonal entries can be lifted independently to chain maps. Each factor is at least $\kappa=\prod_{j\ge1}(1-2^{-j})>1/4$.

## Nilpotent chains and nonsimple primary parts

On the nilpotent part the vertex dimensions are equal after subtracting the common invertible dimension. Hence $c_2=c_0$ and
$$
 2^{c_1/2-c_0}=2^{-H/2},\qquad H=c_0+c_2-c_1 .
$$
The chain-pair proof in the companion note gives the sharper estimate $H\ge\sum_{\ell\ge12}\ell m_\ell/6$, where $m_\ell$ counts all chains of length $\ell$. Here are the charges explicitly. Each ordered pair of nonsimple chains contributes at least zero. If both lengths are divisible by three, reserve one unit from its contribution to cover pairs involving a simple chain as in the companion proof. The reserved units and all the simple-chain pairs have nonnegative total by the displayed sum of squares there. For the self-pair of each individual chain of length $\ell\ge12$, at least $\ell-2\lceil\ell/3\rceil-1\ge\ell/6$ remains after the possible reservation. These self-pairs are distinct even when the chains are isomorphic. [The chain-pair inequality](quadratic-correlation-for-one-large-matrix-product.md#rectangular-products)

There are $33$ possible starting-grade and length types below length $12$. Their multiplicities each have at most $3d+1$ possibilities, and their inverse unit fractions cost at most $\kappa^{-33}$. For each of the three types at a fixed length $\ell\ge12$, summing over its multiplicity and charging its inverse unit fraction when nonzero costs at most $1+\kappa^{-1}\sum_{m\ge1}2^{-\ell m/12}$. The product of these costs over $\ell\ge12$ converges. Thus the sum of the nilpotent weights over all admissible chain types is $O((d+1)^{33})$. Extending the resulting nonnegative majorant to unbalanced chain types is legitimate after the bound on each balanced type has been proved.

In an invertible primary part call $\lambda=(1)$ simple, and all $|\lambda|=m\ge2$ nonsimple. On a nonsimple part $c_0\ge em$, since independent multiplication by elements of each cyclic module supplies that many commuting maps on its own diagonal. The weight $2^{c_1/2}/|\operatorname{Aut}|$ for this part is at most $q^{-m/2}\kappa^{-r(\lambda)}$, where $r(\lambda)\le\sqrt{2m}$ is the number of distinct part lengths. For $q\ge256$, the sum over nonsimple partitions is at most
$$
 \sum_{m\ge2}(8/\sqrt q)^m\le128/q,
$$
using the composition count $2^m$ and $\kappa^{-r(\lambda)}\le4^m$. For each of the finitely many $p$ of degree less than eight, the sum is finite uniformly in $d$. Indeed the partition numbers $P(m)$ satisfy $P(m)\le K_t t^{-m}$ for every $0<t<1$ by the convergent product $\prod_{k\ge1}(1-t^k)^{-1}$. Taking $t=2^{-1/8}$ makes $P(m)\kappa^{-\sqrt{2m}}2^{-m/2}$ summable. For each $e$ there are at most $2^e/e$ monic irreducibles of degree $e$, by counting their distinct roots in $\mathbb F_{2^e}$. Including the option that a given irreducible is absent, the aggregate nonsimple weight is at most a constant times
$$
 \prod_{8\le e\le d}(1+128/2^e)^{2^e/e}
      \le \exp\left(128\sum_{e=1}^d1/e\right)=O((d+1)^{128}).          \tag{4}
$$

## Testing the radical on simple field summands

Fix the nonsimple and nilpotent parts and the number $h_e$ of simple parts of each degree. Allocate a labeled vertex subspace to each simple factor, identified at all vertices with $K_i=\mathbb F_{q_i}$, $q_i=2^{e_i}$. A simple factor contributes $\sqrt{q_i}/(q_i-1)$ to the orbit weight before the probability in (3). Each choice of distinct admissible irreducibles gives one orbit for this fixed data. We bound the sum of their probabilities in (3) while retaining the denominators for permutations and for different roots.

On the labeled vertices represent a simple triple by multiplication by $a_i,b_i,c_i\in K_i^*$ on its three successive arrows. Its monodromy is multiplication by $a_i b_i c_i$. If a simple orbit has polynomial $p$ at this place, it has $e_i$ distinct roots in $K_i$ and each root has exactly $(q_i-1)^2$ such factorizations. All resulting triples on the fixed spaces are in the same $G$-orbit, by the classification of the monodromy. Permuting the distinct simple polynomials at places of the same degree gives a further $h_e!$ copies. The average of $I_Q$ over $g\in G$ is invariant under these choices of representative. Thus one may sum over all representatives just described and divide by $\prod_e h_e!\prod_i e_i(q_i-1)^2$.

For each representative take a fresh uniform $s_i\in K_i$ and form $v_s$ by multiplying each of its three scalar arrows by $s_i$, putting zero on the fixed complementary part. This is a grade-one map commuting with $u$, as is its conjugate with the conjugated $u$. The second difference $D_{gv_sg^{-1}}D_{gug^{-1}}(T+Q)(0)$ is binary-linear in $s$, since these directions are in the radical. Consequently the average of its sign over $s$ is an indicator, and it upper bounds $I_Q(gug^{-1})$. This indicator remains nonnegative when roots repeat, when a root belongs to a subfield, or when a scalar is zero. We can therefore enlarge the sum to all scalar triples, including those choices. The former orbit weights are held fixed throughout this upper bound.

For each fixed $g,s$ the second difference on the enlarged parameter space equals
$$
 \sum_i\operatorname{Tr}_{K_i/\mathbb F_2}
        ((s_i^2+s_i)a_i b_i c_i)\ +\ Q_{g,s}((a_i,b_i,c_i)_i),          \tag{5}
$$
where $Q_{g,s}$ has Boolean degree at most two. The trace part follows by multiplying commuting arrows on each field summand and using the matrix trace of field multiplication. The other term is the bilinear polar form of $Q$ on $gug^{-1}$ and $gv_sg^{-1}$. For fixed $g,s$ both arguments are affine in the scalar parameters, so cross terms between distinct fields are included.

For a single field $K$ of size $q$ and a nonzero coefficient $t$, the derivative polar rank of $\operatorname{Tr}(tabc)$ in a nonzero direction $z\in K^3$ is $2\log_2 q$. Its polar form is $\operatorname{Tr}(t\det(z,v,w))$; its binary radical is $Kz$ because a nonzero determinant functional in $w$ ranges over the whole field. For a sum of independent such trace forms the derivative polar ranks add pointwise. After squaring the mean as in (2), the rank bound for the correlation against *any joint quadratic* therefore factors over active $i$. Inactive variables can be fixed first. Each active factor contributes at most
$$
 L(q_i)=\sqrt{q_i^{-3}+(1-q_i^{-3})/q_i}\le\sqrt{2/q_i}.
$$
A coefficient in (5) is zero for two values of $s_i$. Averaging over the independent $s_i$ consequently costs at most $\prod_i(2/q_i+L(q_i))\le\prod_i4/\sqrt{q_i}$. This applies uniformly in $g$ and in the fixed complementary parts. [Field derivative calculation](trace-product-quadratic-correlation.md#the-one-query-value-was-known)

The enlarged sum has $\prod_i q_i^3$ scalar triples. Combining its normalized bound, the division for roots and permutations, and the simple orbit weights gives the total simple contribution at most
$$
 \frac{1}{\prod_e h_e!}\prod_i
 \frac{\sqrt{q_i}}{q_i-1}
 \frac{q_i^3}{e_i(q_i-1)^2}
 \frac{4}{\sqrt{q_i}}
       \ \le\ \prod_{e=1}^d \frac{(32/e)^{h_e}}{h_e!}.                 \tag{6}
$$
Distinctness from the nonsimple factors can be discarded in the enlarged sum. Summing (6) over all multiplicities gives at most $\exp(32\sum_{e=1}^d1/e)=O((d+1)^{32})$. Multiplying by (4) and the nilpotent bound produces $O((d+1)^{193})$ in (2). Taking the square root proves (1).

The constant predictor has order $2^{-3d^2/4}$, so the remaining uncertainty in its logarithmic optimality is $O(\log d)$. In the certificate bound of the companion note this improves the additive loss from $O(d)$ to $O(\log d)$. Revealing the $d^2$ entries of one factor still suffices to leave a quadratic residual. The missing implication from unrestricted fast SAT concerns the native cost of its computation. Priority for the uniform all-quadratics estimate has not been established.

The companion finite audit evaluates the proposed radical test directly as a second difference and independently through (5), for sampled joint quadratics and every scalar tuple and mask in field-degree lists $(2)$, $(1,2)$ and $(3)$. It also checks the root and permutation denominators for one degree-two summand and two distinct simple summands of degrees three or four. The orbit sum and its asymptotic estimates above are manuscript proofs. [Simple-field orbit audit](radical_field_orbit_audit.py)
