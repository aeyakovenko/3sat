# The degree needed to check a table with distinct tags

**Research journal, 24 November 2026.** A source table has exactly one record for each of the $2^s$ binary tags of length $s$, with at least one data bit per record. A candidate contains the same number of records and can contain repeated tags. Consider families of polynomial checks over $\mathbb F_2$ that give the same answer under any permutation of the candidate's records. The minimum possible maximum Boolean degree that separates **every** such source from every different candidate multiset is exactly $s+1$. This is a worst-case degree bound. The separating family can use any number of tests.

The lower bound holds under a weaker condition. A polynomial need only give a layout-independent answer on the translations of **every** fully tagged Boolean data assignment. It can be position-dependent on all other layouts. At degree at most $s$, even the sources having data zero everywhere and one everywhere give identical answers.

## A separating family

For each tag $a$, let $I_a(x)=\prod_{j=1}^s(1+x_j+a_j)$. This equals one exactly at $a$. For a table of pairs $(x_i,y_i)$, use all of
$$
 \sum_i I_a(x_i),\qquad \sum_i I_a(x_i)y_{i,b}
$$
over tags $a$ and data-bit coordinates $b$. These are symmetric in the rows and have degrees at most $s$ and $s+1$. If the first checks agree with the source, every tag occurs an odd number of times. There are $2^s$ tags and $2^s$ rows, so each count is exactly one. The remaining checks now recover its data bits separately for each tag. The table size is essential for this upper bound.

## A lower bound on translated layouts

Write $G=\mathbb F_2^s$. Index the physical lanes by $i\in G$. For any Boolean data assignment $f:G\to\{0,1\}$ and shift $z\in G$, put the record $(i+z,f(i+z))$ in lane $i$. Freeze any extra data fields to constants. Let $P$ be a polynomial of total Boolean degree $d$ in all lane fields, and assume its value on this input is a common function $H(f)$ for every $z,f$. Global permutation invariance implies this hypothesis. Constancy under translating just the two constant assignments would be insufficient.

Use the unique multilinear representation $H(f)=\sum_{K\subseteq G} H_K\prod_{j\in K}f(j)$. After setting the tag in lane $i$ to $i+z$, leave the lane data $Y_i$ free. The coefficient $a_J(z)$ of $\prod_{i\in J}Y_i$ has degree at most $d-|J|$ in $z$. Indeed each remaining tag bit is affine in $z$, and reducing Boolean powers cannot increase degree. Because $Y_i=f(i+z)$ ranges over all assignments at each shift, uniqueness gives
$$
 a_J(z)=H_{J+z}.
$$
For a nonempty $J$ of size $k\le d$, let $U=\{z:J+z=J\}$ have dimension $u$. The set $J$ is a union of $U$-cosets, so $2^u\le k$ and $u\le k-1$. A linear complement $V$ of $U$ enumerates each member of the translation orbit exactly once. If $d\le s$, then $d-k<s-u=\dim V$. The sum of $a_J(z)$ on $V$ vanishes because in linear coordinates every monomial of degree less than the dimension omits a free bit. Thus the coefficients $H_K$ sum to zero on this orbit. For $k>d$ they vanish individually. Summing over all nonempty orbits gives $H(1)-H(0)=0$. The upper bound is attained on this pair by $\sum_i y_i\prod_j x_{ij}$, since the all-ones tag occurs once. Appending an arbitrary fixed background multiset preserves the lower bound for globally symmetric checks, since we can specialize its lanes first and translate the remaining ones. The same reasoning applies to any check satisfying the translation hypothesis after that specialization.

More precisely, for a given nonzero Boolean $H$ the minimum degree of a translated-layout representation is
$$
 \max_{J:a_J\ne 0}\bigl(|J|+\deg a_J\bigr),\qquad a_J(z)=H_{J+z}.
$$
The coefficient bound proves necessity. For sufficiency, the tag in lane zero is $z$. Evaluate the unique Boolean polynomial for each $a_J$ on that tag and sum $a_J(z)\prod_{i\in J}Y_i$. The formula allows arbitrary size and claims correctness on the translated layouts.

## Grids over finite fields

Over a field containing $\mathbb F_q$, restrict the tag entries of both tables to $\mathbb F_q$ and take $q^s$ lanes with all source tags in $G=\mathbb F_q^s$. The same sharp threshold on translated layouts is $s(q-1)+1$. For the lower bound restrict the one varying data field to zero and one. Multilinear expansion in these Boolean data values is unique over any field. Tag entries $i+z$ are affine, so $a_J(z)=H_{J+z}$ still has a polynomial representative of degree at most $d-k$. For $k>d$ this coefficient vanishes.

For a nonempty $J$ let its additive stabilizer be $U$ of size $m\le k$. We need a polynomial $b(z)$ of degree at most $m-1$ whose sum on each affine $U$-coset is one. Work in an extension field and choose a linear form $\ell$ injective on $G$, for example by using $s$ coefficients linearly independent over $\mathbb F_q$. Let $h(t)$ be the univariate Lagrange indicator of zero on $\ell(U)$, of degree at most $m-1$. The polynomial $\sum_{v\in\ell(U)}h(t+v)$ equals one at all $m$ points of $\ell(U)$, and consequently everywhere. Thus $b(z)=h(\ell(z))$ has the required coset sums. This also covers $m=1$.

Since $a_J$ is constant on those cosets, its sum over distinct orbit elements is $\sum_{z\in G}a_J(z)b(z)$. The summand has degree at most $d-k+m-1\le d-1$. When $d\le s(q-1)$, its grid sum vanishes. Each monomial has an exponent less than $q-1$ in some coordinate, and the corresponding one-variable power sum is zero, including exponent zero since $q=0$ in the field. This proves $H(1)=H(0)$. For the upper bound use $I_a(x)=\prod_j(1-(x_j-a_j)^{q-1})$. Matching tag counts equal one modulo the characteristic, hence each is positive, and the known total forces all counts to equal one. Gating the data by $I_a$ then recovers even field-valued data at each tag. This extension changes the tag alphabet. On the original binary cube the degree-one sum of the flipped data differs by $2^s$ in odd characteristic and characteristic zero.

## Relation to RAM logs and prior work

On a load/store RAM, take a counted loop with a single memory load per iteration, always at the same initially zero address, and keep the loop counter in a register. The $2^s$ load-event ordinals give the tags. The genuine log has all returned bits zero. A putative log returning one each time has a different multiset and violates memory consistency. To use native timestamps one can pad iterations to a fixed power-of-two stride and place the loop start on a boundary of $2^s$ strides. The low bits identify the load phase, the next $s$ bits give the ordinal and the high bits are fixed. This example concerns projected event records containing the tag, address, operation and reply. Position-sensitive tests on a prescribed layout, address-order checks, routing switches and circuit size use different resources. Even the separating checks above can be evaluated directly by a RAM. The degree theorem gives no unrestricted SAT time bound.

Kemper, Lopatin and Reimers analyze separating invariants for general binary row arrays in Theorem 4.8 and Corollary 4.12. Their minimality proof uses complementary parity-class multiplicities. In the binary constant-data example, the rowwise linear change $y\mapsto y+\sum_jx_j$ gives exactly the two parity classes, so the hard pair also has this classical description. Cao studies multisymmetric polynomial nullities of finite tuple multisets. The translated-layout argument above imposes invariance only on the specified legal inputs. No priority claim is made. [Kemper, Lopatin and Reimers, *Separating invariants over finite fields*](https://doi.org/10.1016/j.jpaa.2021.106904) · [Wei Cao, *Nullities of multisets and value sets of multivariate polynomials*](https://doi.org/10.1016/j.ffa.2025.102709)

The companion script exhausts the binary translated-layout linear systems through four lanes, and tests the upper family against all small candidate multisets, including repeated tags. It also checks the finite-field collision directly on small prime grids. [Exhaustive checks](../audits/tagged_routing_degree_experiment.py)
