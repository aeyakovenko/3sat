# Four-list orthogonality with few distinct overlap sizes

Let $L_1,\ldots,L_4$ be lists of $m\ge1$ subsets of $[d]$. A tuple $x\in L_1\times\cdots\times L_4$ has overlap $b(x)=|x_1\cap\cdots\cap x_4|$. The decision problem asks whether any tuple has $b(x)=0$. In the equivalent box cover, coordinate $j$ covers precisely the tuples containing $j$ in all four entries. The overlap is the number of boxes covering a tuple.

**Proposition.** Let $s$ be the number of distinct *positive* overlap sizes attained by all tuples. A deterministic algorithm that does not know $s$ decides the instance using containment counts on subsets of at most $2s+1$ coordinates. If the promise of at most $s$ positive sizes is supplied, order $2s$ suffices. These two orders are optimal in their respective containment-count models. For $d=(\log m)^{O(1)}$ and fixed $s$, the algorithm runs on the explicit lists in $m\operatorname{polylog}m$ native word operations, including witness recovery. Neither the vector sizes nor the positive overlap sizes need be small.

## Aggregation without enumerating tuples

For each subset $T\subseteq[d]$, let $n_i(T)$ be the number of entries of $L_i$ containing $T$, counted with multiplicity. Compute the binomial moments a degree at a time,

$$
B_j=\sum_{|T|=j}\prod_{i=1}^4 n_i(T)=\sum_x\binom{b(x)}j.
$$

The identity counts pairs of a tuple and a chosen subset of its intersection. It yields ordinary moments $M_p=\sum_x b(x)^p$ from $B_0,\ldots,B_p$ by expanding the integer polynomial $z^p$ in the binomial basis, with $M_0=m^4$. The same containment counts underlie the full inclusion-exclusion algorithm for $k$-OV. [*Faster Algorithms for $k$-Orthogonal Vectors in Low Dimension*, ICALP 2026, Lemma 4.1 and Theorem 1.2](https://doi.org/10.4230/LIPIcs.ICALP.2026.85)

For $k=1,2,\ldots$, form the rational $k\times k$ matrices

$$
H_k=(M_{a+b})_{0\le a,b<k},\qquad J_k=(M_{a+b+1})_{0\le a,b<k}.
$$

If $t$ ranges over the attained overlaps and $c_t>0$ is the number of tuples at $t$, let $V_{a,t}=t^a$. Then $H_k=V\operatorname{diag}(c_t)V^\mathsf T$ and $J_k=V\operatorname{diag}(t c_t)V^\mathsf T$. The positive weights and the ranks of Vandermonde matrices give

$$
\operatorname{rank} H_k=\min(k,\#\{t:c_t>0\}),\qquad
\operatorname{rank} J_k=\min(k,\#\{t>0:c_t>0\}).
$$

Indeed the nullspace of each weighted Gram matrix consists exactly of polynomials of degree below $k$ vanishing at its positive-weight nodes. The rational ranks agree with the real ranks used in this argument.

A strict rank difference certifies a zero overlap. Equal ranks below $k$ certify absence. Otherwise advance to the next $k$. At $k=s+1$ one of the two stopping conditions holds. If $s$ is given as an upper bound, compute $H_{s+1}$ using moments through degree $2s$. Rank $s+1$ forces a zero overlap. For rank $h\le s$, all $h$ attained overlaps are already represented and $J_h$ gives the number of positive ones, with highest moment degree $2h-1$. For $s=0$ the known promise forces a witness in any nonempty Cartesian product.

The same moments give the **exact number** of uncovered tuples. When the ranks reveal a zero, choose a polynomial $Q$ in the nullspace of the shifted Gram matrix with $Q(0)\ne0$. Such a polynomial exists because the product of $(z-t)$ over the distinct positive overlaps has the required degree and nonzero constant term. Normalize $Q(0)=1$ by linear algebra. Then $\sum_x Q(b(x))$ is precisely the number with zero overlap and is computed directly from the moments. In the advance-promise case with $s+1$ attained values, find the degree-$\le s$ polynomial normalized by $Q(0)=1$ via the $s$ equations $\sum_x b(x)^{i+1}Q(b(x))=0$ for $0\le i<s$. These use moments through degree $2s$; the Vandermonde matrix on the $s$ positive values shows that all $Q(t)=0$ there. When the number of attained values is known to be $h\le s$, use the analogous system on the positive values after their count is determined.

One direct native implementation enumerates $T$ by increasing cardinality and scans the four explicit lists to form the four counts. For degree limit $p$, this takes at most $m\operatorname{poly}(p,\log(md))\sum_{j\le\min(p,d)}\binom dj$ word operations, plus exact Hankel arithmetic polynomial in $p,\log m,\log(d+1)$. Indeed $M_p\le m^4\max(1,d)^p$, and determinants of order $p+1$ have bit lengths polynomial in these parameters by the determinant expansion. Fraction-free Gaussian elimination thus needs only polynomially many ordinary word operations. Subsets can be visited incrementally and discarded. In the stated polylogarithmic-dimension regime all work arrays fit a standard logarithmic-word RAM. To return a witness, bisect the four lists, test the resulting nonempty subproblems, and descend into one with a zero. Restriction can only decrease the number of positive sizes. There are at most sixteen tests per level and $O(\log(2m))$ levels.

## Matching information loss under adaptive aggregate queries

Use $p$ active coordinates. In the first list take every even-cardinality subset, or in a second instance take every odd-cardinality subset. The lists have the same size $m=2^{p-1}$ for $p\ge1$. In the other three lists every entry contains all active coordinates. For any restriction specifying bits on at most $p-1$ active coordinates, flipping one unspecified coordinate pairs the two parity classes. Thus the counts in every individual list agree at all these restricted patterns, and in particular all the $n_i(T)$ of degree below $p$ agree. Adaptive selection of such queries produces identical transcripts. Only the even input admits an orthogonal tuple. If distinct entries are required in all four lists, give each of the three fixed lists a disjoint block of $\lceil\log_2 m\rceil$ private label bits and encode its entry number there. The varying first list contains no private coordinate, so the overlaps and the transcript equality persist.

Set $p=2s$ with $s\ge1$. On each input there are precisely $s$ distinct positive overlaps, proving the order-$2s$ lower bound with the promise supplied. With $p=2s+1$, the even input has $s$ distinct positive overlaps and the odd input has $s+1$. An algorithm required to be correct on all lists cannot declare the even instance positive based only on queries of order at most $2s$. This proves the extra degree needed when there is no advance promise, including $s=0$. These lower bounds concern aggregate access to coordinate patterns. An ordinary RAM can inspect individual entries directly.

This control excludes candidate hard instances whose tuple overlaps take few distinct positive values in logarithmic or polylogarithmic dimension. It does not exclude an unrestricted subcubic algorithm when the overlap histogram has many distinct sizes. Priority for the particular parameterized algorithm and the matching parity-family formulation has not been established.
