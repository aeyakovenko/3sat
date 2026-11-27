# Verifying a RAM history from separate tables of linear and quadratic observations

Consider the actual Boolean columns of the [row-indexed chronological and sorting verifier](ordered-diagrams-for-native-checksums.md) for the deterministic priority computation. It has a row cube of dimension $d=j+O(1)$, $M=2^j$ native steps, and $\operatorname{poly}(j)$ column and gate types. A proposed integer column is a sum of blocks of the form
$$
    1_{x\in H}\,A(Lx,q(x)).
$$
Here $H$ is any affine subspace of $\mathbb F_2^d$, $L$ is an affine map to $r\le d$ binary coordinates, $q$ is any Boolean quadratic polynomial, and $A$ is an explicit table of $2^{r+1}$ signed integers of $O(d+1)$ bits. Each block may choose different parameters. Overlapping supports and cancellation are allowed. Give each column at most $R$ blocks with at most $S$ table entries in aggregate, counting an empty column with unit cost.

**An exact nondeterministic RAM verifier checks the whole computation and its asserted output in $(1+R)(1+S)\operatorname{poly}(j)$ steps** for polynomial-in-$M$ caps. When $R$ is polynomial in $j$, the cost is linear in $S$ up to scale-polynomial factors, even when different operands and their proposed result use completely different observation maps. Below, the only cross-table operations needed for a gate are sums of products of two columns. A general three-table contraction already includes $\sum_{u,v,w}A(u,v)B(v,w)C(w,u)$.

## Contracting two blocks

Write $2A(u,b)=A(u,0)+A(u,1)+(-1)^b(A(u,0)-A(u,1))$. After this expansion, intersect the affine supports by Gaussian elimination. Each term in four times a pair sum is an integer of the form
$$
    \sum_{x\in H'} C(Lx)D(Kx)(-1)^{Q(x)}
$$
with one quadratic $Q$. The expression can be computed deterministically in $(2^r+2^s)\operatorname{poly}(d+1)$ steps for $r,s$ output bits of the two maps. Intermediate integers have $O(d+1)$ bits under the stated coefficient bound. The final combination divides exactly by four. The real affine-supported quadratic phases also occur in the stabilizer formalism. The argument here uses binary elimination and integer sums throughout. [Dehaene and De Moor](https://arxiv.org/abs/quant-ph/0304125) · [Fattal et al. on bipartite stabilizer structure](https://arxiv.org/abs/quant-ph/0406168)

Use coordinates $(z,y)$ on the nonempty $H'$, where $z$ parameterizes the affine image of $(L,K)$ injectively and $y$ runs over the kernel of the joint map on the direction space of $H'$. Eliminate any two internal bits occurring together. For binary affine functions $e,f$ of the remaining coordinates,
$$
  \sum_{a,b=0}^1 (-1)^{ab+ae+bf}=2(-1)^{ef}.
$$
The residual phase remains quadratic. When no internal pair occurs, summing each residual internal bit with coefficient $g(z)$ gives $2[g(z)=0]$. This produces a power-of-two factor, a quadratic phase on the visible coordinates and affine restrictions on their allowed values. Solve the restrictions. The nonzero visible support is now an affine relation $J$ on the two table indices.

Choose a basis of the direction space of $J$ from its first-side-only directions, its second-side-only directions, and a complement parameterized by $t$. At fixed $t$, the first index is determined injectively by private coordinates $a$ and the second injectively by private coordinates $b$. Write $\alpha=|a|$, $\beta=|b|$ for their bit lengths and $\gamma=|t|$. The first index determines $(t,a)$ and the second determines $(t,b)$, since a vector with zero first or second projection belongs to the corresponding private subspace. Hence $\gamma+\alpha\le r$ and $\gamma+\beta\le s$. The phase at this $t$ is the sum of two local quadratics and $a^{\mathsf T}Db$ for one binary matrix $D$. Absorb the local signs into the two arrays. Interchange sides if needed so $\alpha\le\beta$. For each $b$, add its signed entry to bucket $Db\in\mathbb F_2^\alpha$. Take the Walsh transform of the buckets, and dot the transform with the signed first-side array. Each fixed $t$ costs $(2^\alpha+2^\beta)\operatorname{poly}(d+1)$ work. Summing over the $2^\gamma$ choices proves the claimed cost. Basis changes, phases and table addresses can be computed from their polynomial-size binary descriptions at each accessed entry.

## Checking a Boolean gate with pair sums

Every candidate column $h$ in this representation takes integer values. The test
$$
                     \sum_x h(x)(h(x)-1)=0
$$
makes every entry zero or one, since each summand is a nonnegative integer. For Boolean operands $f,g$ and proposed output $h$, the quantity
$$
 fg-2fh-2gh+3h
$$
is nonnegative on the eight Boolean triples and vanishes exactly at $h=f\wedge g$. Its sum checks a whole AND gate. NOT, equality and constants use a squared linear difference. An AND/NOT basis suffices for all native instruction templates. Summing pairs of blocks from two columns costs at most $2RS\operatorname{poly}(d+1)$. A constant function or one affine guard also fits a block.

For an affine row substitution in a local gate, pull back the affine supports and maps and compose its quadratic phases before computing the sums. A chronological increment or decrement by one has $O(d+1)$ cases according to its carry or borrow length, each an affine guard with an XOR translation. Fixed slot offsets, bitonic partner switches and resetting low slot bits likewise admit polynomially many such affine cases. This checks the ordinary initial state, deterministic controller, sorted memory checks, intermediate gates and output at a specified row of the referenced native layout. Guess, bound and validate all tables and matrices once. Each actual trace in the stated representation passes the checks for its own sign. Soundness follows from the Boolean gate tests and the uniqueness of the sorted computation. The assertion concerns these actual columns, including the internal wire columns of the chosen AND/NOT layout.

Integrality matters. On the four rows $00,01,10,11$ take $f,g$ to be the input coordinates. The alleged AND values $(-1/2,1/2,1/2,1/2)$ pass both summed tests. They have the same sum, squared norm and inner products with $f$ and $g$ as the true AND. Allowing arbitrary fractional table values would lose pointwise soundness.

Under a deterministic $O(N^k)$ SAT solver for $k=1,2,3$, at every sufficiently large scale the unique genuine signed trace in this layout has
$$
             (1+R)(1+S) > M^{1/k}/(j+1)^B
$$
for some fixed $B$, in the sense that it admits no chart at or below this cap. To make the cap uniform, use dyadic upper bounds for $R,S$, each between one and a polynomial in $M$. A single nondeterministic verifier guesses the two dyadic exponents together with the chart, rejecting excess sizes and checking the product cap. Simulating the capped verifier by the ordinary packed RAM-to-3-CNF construction gives $M^{1/k}/(j+1)^{B-O(1)}$ encoded bits; constant-factor rounding or fixed padding does not affect the cost. A generous fixed $B$ makes the alleged solver and its packed input simulation cost $o(M)$. A correct acceptance at infinitely many stages for one sign contradicts the native deterministic detector theorem. For an unconditional exclusion, sufficiently small charts for an actual computation of one of the two signs at infinitely many true stages would be needed. [Native signed detector](priority-pinned-sat.md) · [Packed verifier compiler](packed-band-transfer.md)

## A word-computable obstruction at the cubic threshold

There is an exact lower bound for the number of affine directions one must fix before a certain easy row function becomes quadratic. Put $K=\mathbb F_{2^m}$ and take
$$
                    F(u,v,w)=\operatorname{Tr}_{K/\mathbb F_2}(uvw).
$$
The least codimension of an affine flat on which $F$ has Boolean degree at most two equals $m$. Setting $u$ equal to a constant suffices. For the reverse inequality take any flat with direction space $W$ of codimension $r<m$. It contains a direction $(a,0,0)$ with $a\ne0$, by dimension. The projection of $W$ to the last two coordinates has dimension at least $2m-r>m$. The third additive derivative of $F$ along $(a,0,0)$ and any two other directions equals
$$
 \operatorname{Tr}(a(vw'+v'w)),
$$
where $(v,w),(v',w')$ are their last two projections. This is a nondegenerate alternating form on the $2m$-dimensional space $K^2$, by nondegeneracy of the field trace pairing. A totally isotropic subspace has dimension at most $m$, since it lies in its orthogonal complement. Some third derivative is therefore one, at every basepoint of the flat. Every Boolean quadratic has zero third derivative. This proves the claim for all affine translates.

A single block representing $F$ needs at least $m$ affine observations when $m\ge2$. Its support must be the full row space, since otherwise $F$ would vanish on a complementary affine hyperplane, contradicting the flat bound. On any fiber of its observation map, its Boolean output is constant, the quadratic bit, or its complement. More generally for any sum of $R$ blocks representing $F$, one has
$$
                         R+\sum_{b=1}^R r_b\ \ge\ m .
$$
Start with the row cube. If an affine support splits the current flat, impose the opposite of one nonconstant defining equation to avoid the support. This decreases dimension by one and makes that support identically false. A support containing or disjoint from the current flat costs nothing. Then fix all affine observations, spending at most $\sum_b r_b$ further dimensions. On the resulting nonempty flat each block modulo two is a constant, a Boolean quadratic, or its complement. Their sum modulo two has degree at most two, so the total codimension is at least $m$.

On $2^{3m}$ rows the single-block cost is already at least $2^m$ explicit table entries. Even the more permissive representation supplying an arbitrary quadratic separately on every observation fiber requires $2^m$ fibers and attains this count by fixing $u$. Field multiplication and trace are computable in $\operatorname{poly}(m)$ bit operations given a defining polynomial, so a row function can reach this obstruction with cheap indexed evaluation. In fact, with fewer than $m$ nonadaptive quadratic bits a single table representing this function needs an injective observation map on all $2^{3m}$ rows. The [collision-flat proof and physical SAT realization](quadratic-observations-of-a-sat-verdict.md) give the stronger bound and its sharp threshold. This example disallows a blanket single-block compression argument based solely on fast access to each row. It provides no lower bound of the required strength on sums with many blocks or on the requested unrestricted SAT clock.

[Lean checks of integer and gate tests and binary Gaussian elimination identities](../lean/QuadraticTraceTables.lean) · [Exact contraction and trace experiments](../audits/quadratic_trace_tables_audit.py)
