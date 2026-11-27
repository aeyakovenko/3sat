# Exact offline verification from a small octant

Let a complete weighted dominance transcript have $n$ operations, $u=O(n/\log^2 n)$ updates, and $q=O(n)$ numerical claims. Write $L=\Theta(n\log n)$ for its proper ASCII DIMACS bit length. At query $j$ with coordinates $(a,b)$, partition **all** updates by their answers to three tests: did the update occur before $j$, is $x\le a$, and is $y\le b$? Let $k_j$ be the smallest of the eight resulting populations, including zero. A deterministic word RAM computes every true answer and the exact number of erroneous claims in
\[
                 O\!\left(L+\sum_{j=1}^q k_j\right)
\]
time. Thus one globally correct SAT program decides both verdicts in $O(L)$ on all these files with $\sum_j k_j=O(L)$. It can validate the public layout, schedule, packet inventory and masks in $O(L)$, restore chronological order by ID, use the algorithm below on recognized files, and run complete SAT search on other files. The model-count bijection gives the verdict directly. The same procedure applies to a recognized blank-padded prefix ending with a complete annotation, with only the delivered updates in the geometry. [Original DIMACS grammar and model count](weighted-range-transcript-encoding.md) · [Template recognition and a randomized offline check](offline-verification-of-weighted-range-transcripts.md)

## One missing integer

Identify an octant with the set $C\subseteq D=\{t,x,y\}$ of tests that pass. For any subset $S$, let $m_S$ be the total update weight passing every test in $S$. The desired answer is $F=m_D$. The seven $m_S$ for $S\subsetneq D$ can be computed for all queries in $O(n\log n)$ time: use the total weight, three one-dimensional prefix sums, and three two-dimensional sweeps. For each pair sort all points and queries by the first coordinate, inserting points into a Fenwick tree and taking prefix sums in the second. Encode time by update ranks $1,\ldots,u$ and put the number of earlier updates on each query. This makes all cuts inclusive, including spatial coordinate ties. Use the same sweeps with unit weights for the count margins. All sums need $O(\log n)$ bits or a constant number of words.

Let $W_C$ be the weight of the exact octant. Expanding the tests required to fail gives
\[
 W_C=A_C+\sigma_CF,\qquad
 A_C=\sum_{C\subseteq S\subsetneq D}(-1)^{|S\setminus C|}m_S,
 \qquad \sigma_C=(-1)^{3-|C|}.
\]
Consequently, summing the weights of **any one** octant recovers $F=\sigma_C(W_C-A_C)$. Without further update geometry these are the full linear constraints on the eight cells. The interval from nonnegativity alone is $[\max_{\sigma_C=1}(-A_C),\min_{\sigma_C=-1}A_C]$. Each integer in this interval induces a nonnegative integer table with precisely the supplied margins. Realizing those tables on the particular delivered updates is a stronger requirement.

For counts write the same identity $N_C=B_C+\sigma_C Z$. Choose one octant minimizing $B_C$ for each sign. These two candidates are computable from the seven count margins. Their populations sum to the known sum of their offsets, and the smaller population equals $k_j$. Initialize just these two reporters. Request one more record from each in rounds, accumulating its weight separately. The first reporter to exhaust supplies a complete weighted total after at most $k_j+1$ requests to either reporter. No decision about the smaller sign is needed in advance.

## Enumerating the two candidates

Build a balanced binary tree over chronological update ranks. At each node list its updates sorted by $(x,\text{rank})$. Store, for each catalogue prefix length, the number belonging to the left child. The right-child count follows by subtraction. In the same list build two static tables returning the position of a minimum or maximum $y$ in a subarray. Storing both extrema for all begins and power-of-two lengths costs $O(m\log(m+1))$ for a list of $m$ entries. Two overlapping intervals then answer any range extremum in constant time, using the integer logarithm of its length from a precomputed table. Summed over the time tree, construction time and space are $O(u\log^2(u+2))$. Empty input has zero answers. This is a static range-tree construction with linked catalogues. [Chazelle and Guibas, applications of fractional cascading](https://www.cs.princeton.edu/~chazelle/pubs/FractionalCascading2.pdf)

Each time prefix or suffix decomposes into $O(\log(u+2))$ canonical nodes by following one boundary path. Binary search the root for $x\le a$, and propagate this prefix length in constant time per visited node. In each canonical catalogue the desired side of $x$ is now a single interval. To report $y\le b$, take the minimum $y$ in that interval. Discard the interval if this minimum fails. Otherwise emit its update and put the two remaining subintervals on a stack. For $y>b$ use a maximum and the strict comparison. The full stack starts with $O(\log(u+2))$ intervals. Each output adds at most two tasks, so obtaining the first $s$ outputs, including the next exhaustion check if those were all the outputs, costs $O(\log(u+2)+s)$. This prefix bound justifies interleaving the two reporters even when their next-output delays differ. The total time across all queries is the displayed bound because $q\log(u+2)+u\log^2(u+2)=O(n\log n)$.

## Restricting all three coordinates before enumerating

Partition each coordinate into at most $B$ fixed bands, with intervals open on the left and closed on the right. Let $k_j^{\rm cell}$ be the smallest octant population when only updates in the same three-dimensional band cell as query $j$ are counted. There is a deterministic exact time bound
\[
   O\!\left(L+Bu\log(n+2)+\sum_j k_j^{\rm cell}\right).
\]
In particular $B=\max(1,\lfloor n/u\rfloor)$ costs $O(L)$ preprocessing for $u>0$. No array of $B^3$ cells is necessary. Sort the updates and queries by their three band indices and process only the occupied groups. Band boundaries can be coordinate ranks or fixed coordinate values and may be found by binary search.

For a query upper corner $r$ with band lower boundaries $l$, the local indicator on an update $p$ is
\[
  \prod_{i=1}^3\big([p_i\le r_i]-[p_i\le l_i]\big).
\]
The expansion contains the original dominance indicator and seven terms in which at least one threshold is a band boundary. For each of those seven terms, fix one coordinate with such a threshold and group queries by its value. For each group filter updates by this single threshold, then run an ordinary offline sweep with the other two thresholds. Across the groups the update copies number at most $Bu$, and each query appears once per term. The local product is computed by the two-candidate procedure within its cell. All cells together have at most $u$ updates and $q$ queries, so their sweep and construction overhead fits $O(L)$. Rearranging the expansion recovers the global answer. Because each local octant is a subset of its global counterpart, $k_j^{\rm cell}\le k_j$. In the four-corner example below, place the repeated interior query in an empty spatial band to give every $k_j^{\rm cell}=0$ while many $k_j$ grow proportionally to $u$.

## What the seven margins can distinguish

A four-update example keeps all seven weighted margins equal at **every issued query** of two different streams. Use weight one throughout. In the first stream the first two spatial locations are $(1,1),(2,2)$, and the next two are $(1,2),(2,1)$. In the second stream exchange the early and late pairs, preserving order within each. Ask $(1,1)$ once between the second and third updates. Ask $(n,n)$ everywhere else. Place the four updates in consecutive legal update slots and make any additional updates identical. The global spatial histograms agree. At the special time, each early pair has the same separate $x$ and $y$ histograms. At the other queries the two spatial tests are constant. Thus all seven queried summaries agree, while the special answer differs by one. Annotating each file with the answers from the first gives opposite DIMACS verdicts.

There is an important quantifier on this example. Providing the full weighted $(t,x)$ and $(t,y)$ distributions at **all** thresholds would determine this original stream: difference two consecutive time prefixes to isolate the unique positive-weight update at that time, including its $x$, $y$, and weight. If multiple updates were permitted to share each of the two time stamps, the four-point parity trade would preserve both full projected distributions as well. That convention changes the original source.

## Occupancy on the product distribution

On the Weinstein–Yu product distribution with public update period $\log^2 n$, the statistic $K=\sum_j k_j$ has mean $(1/64+o(1))qu$. For each fixed $\varepsilon>0$, $|K-qu/64|>\varepsilon qu$ has probability $\exp(-\Omega_\varepsilon(u))$ or less. These claims concern the original $q$ queries. An appended public final query has an empty future octant and adds zero. [Weinstein and Yu, §4, distribution $D$](https://arxiv.org/pdf/1604.03030)

To see the constant, let $s$ be the number of earlier updates, and put $v(z)=\min(z,1-z)$. Conditional on the query coordinates, each count is a sum of independent indicators. The smallest of the eight conditional means is
\[
                        u v(s/u)v(a/n)v(b/n).
\]
The expected minimum differs from this value by at most $\sqrt u$. Indeed the absolute difference of the two minima is bounded by the largest absolute deviation of a cell count from its mean. Its expectation is bounded by the square root of the sum of all eight variances, at most $\sqrt u$ because the eight expectations sum to $u$. Concavity also puts the expected minimum on the lower side.

Across the regular schedule on the integral subsequence, each $s=0,\ldots,u-1$ occurs equally often among original queries. The coordinates $a,b$ are independent uniforms on $[n]$. The discrete average of $v$ on either grid tends to $1/4$, and equals $1/4$ for even grid size. Averaging and multiplying gives the claimed constant. Changing one update can move one point between octants of each query, changing $K$ by at most $q$. Changing one query affects only its own minimum, by at most $u$. Independence and bounded differences give
\[
   \Pr(|K-\mathbb E K|\ge t)
        \le 2\exp\big(-2t^2/(u q^2+q u^2)\big).
\]
In particular a positive fraction of the queries have $k_j=\Omega(u)$ with the same high probability, since each $k_j\le u/8$. The bound on this enumerator therefore generally exceeds $L$ on the source distribution. Large $K$ is compatible with fast exact verification. For instance, repeat four corner locations cyclically with arbitrary weights, and issue the same interior query throughout. Middle-time queries have all eight populations $\Omega(u)$. Four running weight sums suffice to answer that particular family in constant time per decoded operation. [McDiarmid, method of bounded differences](https://doi.org/10.1017/CBO9781107359949.008)

## All choices of $B$ bands on these inputs

For $B=\Theta(\log^2 n)$, even the best grid chosen after seeing the stream still typically costs too much if the verifier must enumerate a smallest local octant at every query. The fixed-grid calculation gives the leading constant for equal bands. A uniform box argument then covers arbitrary rectangular partitions.

Fix one band partition of integer axis size $M$ with positive lengths $l_1,\ldots,l_b$, $b\le B$. Define
\[
   C_M=\sum_s(l_s/M)^2,\qquad D_M=\sum_s\lfloor l_s^2/4\rfloor/M^2.
\]
Thus $C_M\ge 1/B$, and $0\le C_M/4-D_M\le B/(4M^2)$. The first quantity is the expected relative band width for a random uniform threshold. The second is the expected relative band width times $v$ of the threshold's local position. Indeed $\sum_{i=1}^{l}\min(i,l-i)=\lfloor l^2/4\rfloor$. For the time axis of $u$ update ranks, the actual query cuts are $s=0,\ldots,u-1$ with equal multiplicity. Assign an exact time boundary to the following group of updates for averaging, so query offsets within a length-$l$ band run from zero to $l-1$. This gives the same sum. At an exact boundary either choice makes one local time side empty and hence gives the same $k_j^{\rm cell}=0$.

Write $C=C_tC_xC_y$ and $D=D_tD_xD_y$ for the products on axes of sizes $u,n,n$. On averaging the conditional means of the eight local counts, the mean of their minimum is $uD$. Indeed the conditional mean local occupancy is the time-band length multiplied by the two relative spatial widths, and the smallest cell mean includes the three local $v$ factors. The average of the mean local occupancy itself is $uC$. Conditional variances of the eight counts sum to at most that query's mean local occupancy. Cauchy–Schwarz applied first to the count fluctuations and then across queries gives the two-sided finite estimate
\[
 uD-\sqrt{uC}\ \le\ q^{-1}\mathbb E\sum_j k_j^{\rm cell}\ \le\ uD.
\]
Thus $D=(1/64+o(1))C$ uniformly for $B=o(u)$, and $uC\ge u/B^3$. If $B^3=o(u)$, the expected sum is at least $(1/64-o(1))qu/B^3$ for all the partitions. Equal bands dividing all axis sizes attain this asymptotic value.

**Rectangular partitions chosen in hindsight.** Partition the entire rank domain into at most $M$ disjoint axis-aligned boxes of arbitrary side lengths. The partition need not come from three global lists of cuts. In each box, a query's local octants are its eight intersections with that box. If $M\log n=o(u)$, then except with probability $\exp(-\Omega(u/M))$, **every** such partition has
\[
                    \sum_j k_j^{\rm cell}=\Omega(qu/M).
\]
For a grid with $B$ bands per axis one can take $M=B^3$. The preceding equal-band estimate attains this order in expectation on the divisible schedule. This lower bound concerns the total number of records in the smallest local octants, irrespective of how the partition was chosen. The coarse-sweep upper bound above was proved for global axis bands.

To prove this, measure box volume as the product of its coordinate lengths divided by $un^2$ on the integer rank domain. Each update time rank occurs once, and each query time rank occurs $q/u$ times when the number of earlier updates is indexed from zero. One can put both on $[u]$ by placing the queries with $s$ earlier updates at $s+1$, testing strict inequality in the time coordinate. This changes no comparisons. Using $s$ instead shifts the time domain by one, with no effect on the interior estimates below. For a fixed integer box of relative volume $v$, the mean update population is $uv$ and the mean query population is $qv$ with the common-domain convention. Each is a sum of independent Bernoulli variables from the time interval of the box. For a sufficiently small absolute $c_0>0$, Chernoff's inequality and a union bound over $O(n^6)$ boxes show, except with probability $\exp(-\Omega(u/M))$, that simultaneously every box with $v\ge c_0/M$ has at least $uv/2$ updates and $qv/2$ queries. This step uses $u/M\gg\log n$ and $q\ge u$. No union over partitions is necessary.

In any partition, cells of volume $v\ge 1/(2M)$ together have volume at least $1/2$. Each of their coordinate lengths is at least $1/(2M)$ times its axis size, which tends to infinity even on the shortest axis. The middle half of each axis defines an inner box with a fixed positive fraction of the cell volume. The first and last quarters on each axis give eight corner boxes, each also of volume at least a fixed positive fraction of $v$ after rounding. The intervals can be rounded inward with a one-unit gap to handle all strict and non-strict tests. Choosing $c_0$ small enough places all nine boxes in the simultaneous event above. Thus $\Omega(qv)$ queries in the inner box each see $\Omega(uv)$ updates in *every* local octant. The contributions across these cells are disjoint. Finally $\sum_{v\ge 1/(2M)} v^2\ge (1/2)^2/M$, which yields the assertion.

**Number of cells for linear enumeration work.** Fix any $A>0$. With high probability the fewest rectangular cells with $\sum_j k_j^{\rm cell}\le A q\log n$ is $\Theta_A(u/\log n)$. For the lower bound use the last argument at $M=\lfloor c_A u/\log n\rfloor$. The actual union-bound failure is $O(n^6)\exp(-c u/M)$ for an absolute $c>0$. A sufficiently small fixed $c_A$ both makes it vanish and makes the lower bound exceed the stated budget, uniformly over smaller partitions. Conversely group consecutive updates into time slabs of at most $\lfloor A\log n\rfloor$ updates each. Every cell population, hence every smallest local octant, is at most $A\log n$, on every input. This sharp threshold prices only local reporting. Computing the contributions of all earlier time slabs remains a separate part of exact verification.

The finite audit compares all seven Fenwick sweeps, each octant reporter, and the two-candidate reconstruction against direct answers. It includes repeated coordinates, zero populations, a dense stream, all $3^8$ tables with entries in $\{0,1,2\}$, and the trade on actual query cuts. It also checks the coarse expansion at 1,225 obtained cuts and the two expected-mass identities on all 512 products of four-position axis partitions. At the central cut with four independent points in each time half, the $4^8=65,536$ equally likely quadrant samples include $(4!)^2=576$ in which all eight cells are occupied. [Reproducible audit](../audits/small_octant_audit.py)
