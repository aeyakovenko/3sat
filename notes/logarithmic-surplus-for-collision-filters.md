# A logarithmic surplus for odd detection of an equal pair

Let $s(t)$ be the least number of fixed subsets of the unordered pairs of $t$ row indices such that every list with a repeated value has an odd number of equal pairs in at least one subset. The alphabet has at least $t$ values. There are absolute constants $c>0$ and $C$ such that, for $m=\lfloor t/2\rfloor\ge1$,
$$
s(t)\ge m+c\log_2 m-C.
$$
The same lower bound holds if the guarantee is required only for lists in which each value occurs at most three times. The coefficient obtained below is small. The bound measures the number of parity queries for the fixed equal-pair verifier. [Model and previous bounds](odd-filters-on-collision-pairs.md)

Alon's Theorem 1.6 gives exactly $\lfloor t/2\rfloor$ linear checks for the family consisting of all individual cliques, allowing isolated vertices. Our forbidden family also includes disjoint unions of several nontrivial cliques. The logarithmic excess holds even with only pairs and at most four triangles. In graph-code terminology it is an upper bound $2^{-\lfloor t/2\rfloor}t^{-c}$, up to a constant, on the relative size of a binary linear code avoiding those unions. Priority for this extension has not been established. [Alon, *Graph-Codes*, Theorem 1.6](https://web.math.princeton.edu/~nalon/PDFS/graphcodes5.pdf)

## Matching coordinates

It suffices to use $2m$ rows. The remaining row, if present, gets its own fresh value. An edge label $v_{xy}\in\mathbb F_2^{s(t)}$ lists the filters containing the pair $xy$. For a partition of the rows into equality classes, sum the labels of the edges internal to its classes. This sum is its syndrome. A valid family of filters gives a nonzero syndrome on every nondiscrete partition under consideration.

Fix $m$ disjoint pairs of rows $(i,0),(i,1)$. Their labels are linearly independent, since each nonempty submatching occurs as the complete set of equal pairs of some list. Write the putative label dimension as $m+k$ and extend these matching labels to a basis. In this basis write each label as $(u,z)\in\mathbb F_2^m\oplus\mathbb F_2^k$, with matching label $(e_i,0)$ at pair $i$. For $p\in\{0,1\}$ write $(u^p_{ij},z^p_{ij})$ for the edge from $(i,p)$ to $(j,p)$.

If a collection of disjoint triangles on rows of a set $I$ of pair indices has zero $z$-sum and zero $u$-sum on $I$, we can extend it to a zero-syndrome partition. For each nonzero coordinate outside $I$, add its matching pair as a class. Give each remaining row a singleton class. The outside pairs use fresh rows, and all nontrivial classes have size two or three. It will suffice to find such a collection containing at least one triangle.

## Finding three groups with compatible edge data

Fix $r=3$. For any two ordered groups of $r$ indices, index their elements by $a=1,\ldots,r$ in increasing order. Consider the $r$ edges joining equal positions $a$ in the two groups on row type $p$. The $u$-coordinates of these labels at the positions in the left group form an $r\times r$ matrix $L^p$ whose column $a$ is the restriction of the $a$-th label. Define $R^p$ by restriction to the right group. The ordered quadruple $(L^0,R^0,L^1,R^1)$ takes at most $Q=2^{4r^2}$ values. Fix $g=R_Q(3)$, a finite graph Ramsey number independent of $m,k$.

Divide the $m$ matching indices into $g$ consecutive buckets of size $n=\lfloor m/g\rfloor$, dropping any remainder. Color a transversal $(i_1,\ldots,i_g)$, one index from each bucket, by the following bits.

* For both row types and each unordered pair of buckets, record $z^p_{i_a i_b}$.
* For each triple of buckets and each choice of two of the three buckets, record the coordinate $u^p_{i_a i_b}(i_c)$ for both row types. Here $i_c$ belongs to the remaining bucket.

This uses at most $2^{D}$ colors, where $D=2k\binom g2+6\binom g3$. One color has density $\delta\ge2^{-D}$. For
$$
n>g\binom r2\,2^{D r^g},\tag{1}
$$
that color contains a product of $r$ distinct indices from each bucket.

Here is a counting proof of the product assertion. In each bucket draw $r$ positions independently with replacement. The probability that all $r^g$ transversals have the chosen color is at least $\delta^{r^g}$. To see this, successively replace the single random position in each bucket by $r$ independent copies. Conditional on the choices in the other buckets, success for all $r$ copies has probability equal to the $r$-th power of the previous conditional success probability. Jensen's inequality bounds its average below by the $r$-th power of the previous average. A union bound gives probability at most $g\binom r2/n$ that a position repeats in some bucket. Inequality (1) therefore gives a monochromatic product with no repeats. This is the dense complete multipartite hypergraph argument in a form with sufficient constants. [Erdős, *On extremal problems of graphs and generalized graphs*](https://renyi.hu/~p_erdos/1964-13.pdf)

Keep the $r$ indices in each bucket given by the product and call them a group. Two consequences will matter. On each fixed pair of groups, the residual vector $z^p_{ij}$ is constant over choices of its two endpoints. For any three distinct groups, the coefficient $u^p_{ij}(h)$ is constant over all three choices when $i,j,h$ range in their respective groups. The constants may depend on the groups, the role of each group, and $p$.

Color each ordered group pair by its quadruple of matrices defined above. The choice of $g$ supplies three groups $A<B<C$ such that the pairs $AB,AC,BC$ have the same color. In particular the restrictions at $A$ agree for $AB,AC$, and the restrictions at $C$ agree for $AC,BC$. Use these nine indices as $I$.

## Constructing the equality partition

Let $E=\{x\in\mathbb F_2^r:\sum_a x_a=0\}$. For row type $p$ and $x\in E$, make one triangle on the rows at position $a$ in $A,B,C$ for each $x_a=1$. These are disjoint triples. The syndrome is linear in $x$ because each selected position contributes the three labels of its own triangle.

Each group pair contributes its constant residual vector an even number of times, so the $z$-sum vanishes. At any index of $A$, the parallel edges from $AB$ and $AC$ sum to zero by equality of their left matrices. The edges of $BC$ each contribute the same bit at this index by the three-group property, and there are evenly many. Thus the restriction of the syndrome to $A$ is zero. The right matrices give the same cancellation at $C$ for $AC$ and $BC$, while the $AB$ edges cancel there by evenness. Only the $r$ coordinates at $B$ remain to check in $I$. Denote their linear dependence on $x$ by $K_p:E\to\mathbb F_2^r$.

Use both row types and consider the linear map
$$
(x_0,x_1)\longmapsto K_0x_0+K_1x_1,\qquad E\oplus E\longrightarrow\mathbb F_2^r.
$$
Its domain has dimension $2(r-1)=4$ and its codomain dimension $r=3$. Pick a nonzero kernel element. Its two triangle collections use disjoint rows even if they use the same positions, since the row types differ. At least one triangle is present. The combined syndrome vanishes on $I$ and on the residual coordinates, giving the promised partition after adjoining outside matching pairs. Hence a valid label family must fail (1).

In particular $m<g(1+g\binom r2\,2^{D r^g})$. All quantities other than $m,k$ on the right are absolute constants or occur in $D=2k\binom g2+6\binom g3$. Taking a base-two logarithm gives $\log_2 m\le 2\binom g2 r^g k+O(1)$. This proves the theorem. The rectangle extraction and asymptotic estimates are manuscript proofs. The four-to-three dimension obstruction is independently proved on actual three-bit masks in Lean. [Lean dimension check](../lean/CollisionFilterRectangle.lean) Priority for the filter bound remains unestablished.

## Witness size and recovery

Each nonzero even vector of length three has weight two. The construction therefore uses at most four triangle classes, accounting for at most twelve equal pairs, and at most $m-9$ outside matching pairs. The total is at most $m+3$. If the canonical matching was dependent, a nonempty zero-sum submatching already gives a counterexample with at most $m$ equal pairs. Thus the lower bound holds even with at most $m+3$ equal pairs and at most four classes of size three. Under the tighter promise of at most $m$ equal pairs, run the same proof on $2(m-3)$ rows and fill the remaining rows with distinct fresh values. This decreases the lower bound by at most an additive constant.

Given an explicit table of labels satisfying (1) in the canonical matching coordinates, the proof also yields a polynomial-time search. Gaussian elimination first finds a zero-sum submatching or supplies the basis used above. In the second case enumerate nine distinct matching indices grouped as $A,B,C$ with three ordered positions in each group. For each choice, test the four even subsets of positions independently on both row types, omitting the all-empty choice. A zero residual sum and zero coordinates on the nine indices suffice. The other coordinates specify exactly which outside matching pairs to add. These nine indices and two subset masks take $O(\log t)$ bits as a certificate when the table and deterministic basis-extension procedure are given. A dependent canonical matching can be handled directly by deterministic elimination without index advice. The extractor recomputes the full syndrome on the resulting partition. [Executable search](../audits/collision_filter_counterexample.py)

## A promise of fewer equal pairs

Fix $1/2<\alpha<1$. Even restricting to lists with at most $\lfloor\alpha m\rfloor$ equal pairs, the number of filters is at least
$$
m+c_\alpha\log_2 m-C_\alpha
$$
for constants $c_\alpha>0,C_\alpha$. The counterexamples have classes of size at most three and at most $O_\alpha(1)$ triples. In terms of the original $t$ rows, the number of equal pairs allowed can be any fixed fraction of $t$ strictly greater than one quarter.

For $d\ge1$ put $q_d=2^{d-1}/(2^d-1)$. Given a $d$-dimensional binary vector space and any list of $N$ linear forms on it, the average number of nonzero evaluations over its nonzero vectors is at most $q_d N$. A nonzero form takes value one exactly $2^{d-1}$ times, and a zero form never does. Choose a fixed $d$ such that $q_d<\alpha$. This is the binary Plotkin averaging argument.

Apply it first to dependencies among the $m$ canonical matching labels. If their kernel has dimension at least $d$, select a $d$-dimensional subspace of the kernel. The $m$ coordinate forms give a nonempty zero-sum submatching of weight at most $q_dm<\alpha m$. This already violates the guarantee. Otherwise retain $M\ge m-d+1$ independent pairs, assigning fresh singleton values to the discarded rows. Extend those $M$ labels to a basis of the ambient label space, with $k'=s-M$ residual coordinates, where $s$ is the proposed number of filters.

Repeat the product and graph Ramsey arguments with $r=d+2$ positions per group, $M$ matching indices, and $k'$ residual bits. The map from $E\oplus E$ to the $r$ middle coordinates has a kernel of dimension at least $2(r-1)-r=d$. Choose a $d$-dimensional subspace of that kernel. Every outside correction bit is a linear form on this subspace, since it is the sum of the corresponding edge coefficients of the selected triangles. The averaging inequality applied to the $M-3r$ outside forms gives a nonzero element requiring at most $q_d(M-3r)$ outside pairs. There are at most $2r$ triangles, contributing at most $6r$ equal pairs. Their combined total is bounded by $q_d(M-3r)+6r\le\alpha m$ for all sufficiently large $m$, since $q_d<\alpha$ and $r$ is fixed. All quantities being counted are integers, so the floor in the promise is respected.

It follows that (1), with these new parameters, must again fail. The logarithmic estimate yields $s\ge M+c_\alpha\log_2 M-O_\alpha(1)$, and $m-M\le d-1$. Enlarging $C_\alpha$ covers the finitely many smaller $m$. For fixed $\alpha$ the search remains polynomial in the table size. The first case tests $2^d-1$ combinations of a computed subspace basis. The second enumerates $3r$ indices and two even masks, testing the completed pair count as well as the syndrome. Priority for this sharpened promise has not been established.

## Why four choices per row do not yield a stronger divisibility bound

A candidate improvement assigns each row a palette $P_i$ of four distinct record values, indexed by two bits. Suppose $|P_i\cap P_j|$ is even for every $i\ne j$. The indicator that the two chosen values agree then has Boolean polynomial degree at most three over $\mathbb F_2$. Indeed its only possible degree-four coefficient is the parity of its truth table, which is $|P_i\cap P_j|\bmod 2$. Each filter gives a cubic equation on the $2t$ selector bits. A valid family has exactly as many common zeros as there are injective choices of representatives, say $J$. The usual Ax–Katz degree estimate gives divisibility by $2^{\max(0,\lceil(2t-3s)/3\rceil)}$ for $s$ cubic equations. At $s=\lfloor t/2\rfloor$ its exponent is $t/6+O(1)$. [Katz, *On a theorem of Ax*](https://web.math.princeton.edu/~nmk/old/ax.pdf)

In fact $2^{\lceil t/4\rceil}$ always divides $J$. By inclusion–exclusion on the partition lattice,
$$
J=\sum_{\pi}\prod_{B\in\pi}(-1)^{|B|-1}(|B|-1)!\,\left|\bigcap_{i\in B}P_i\right|.
$$
One can obtain the formula by summing the signs of permutations whose cycles must receive a common value. For a fixed assignment, its compatible permutations form a product of symmetric groups on its equality classes. Their signs sum to one for an injective assignment and zero otherwise. Grouping by cycle partition gives the displayed factors. Singleton factors contribute two powers of two and pair factors contribute at least one. For every $b\ge3$, $v_2((b-1)!)\ge\lfloor(b-1)/2\rfloor\ge b/4$. Thus each summand is divisible by $2^{\lceil t/4\rceil}$, including summands with an empty palette intersection. This exceeds the divisibility guaranteed by the cubic degree estimate at matching rank for all sufficiently large $t$. The proposed comparison cannot produce a positive surplus there.

## Why one direct counting argument stops at a matching

Suppose a binary subspace of edge sets consists entirely of graphs of equality partitions. On any three vertices a partition restricts to zero edges, one edge, or all three. The XOR of two distinct nonzero possibilities has two edges and is forbidden. Therefore all nonzero restrictions to this triple coincide. If two incident edges occur anywhere in the subspace, they always occur together and force the third edge of their triangle, including when they were first seen in two different vectors. Every connected component of the union of the supports is consequently a clique whose edges occur together in every vector. There are at most $\lfloor t/2\rfloor$ nontrivial components. The subspace has at most that dimension, with equality realized by a fixed matching. Even a translated packing whose distinct pairwise differences are nondiscrete partition graphs has at most $2^{\lfloor t/2\rfloor}$ members: translate one element to zero and use the same triple argument on pairwise differences. This explains why injectivity on one such packing alone misses the logarithmic term.

This palette divisibility exponent is exact for every $t\ge2$. For $b=2,3,4$ rows, give all rows a common symbol, give each pair its own additional shared symbol, and fill each row with private symbols up to size four. Pair intersections have size two and intersections of three or more rows have size one. The injective-choice counts are respectively $14,42,102$, each divisible by two exactly once. Use disjoint alphabets across blocks, so the counts multiply. Write $t$ as a sum of $\lceil t/4\rceil$ parts of size $2,3,4$: for $t\equiv1\pmod 4$ use $2+3$ and then fours, and for the other residues take the remainder if nonzero and then fours. This attains valuation $\lceil t/4\rceil$.
