# Discovering one equality-SAT verdict takes almost every successor row

Fix $w$ divisible by four. An ordinary Horn 2-CNF with $O(w)$ clauses and $L=\Theta(w\log w)$ encoded bits has $w$ data-bearing rows, each specifying one successor. The row values form a uniformly random single cycle. On every member of this family, at most $w/2$ successor entries determine the verdict among all completions satisfying the single-cycle promise. Nevertheless, even conditional on the formula being unsatisfiable, every correct deterministic SAT solver must touch an expected $w-O(\sqrt w)$ distinct rows. The same bound holds on satisfiable inputs. With a hard probe cap, any fixed positive advantage over guessing on the unconditioned distribution also requires $w-O(\sqrt w)$ rows. Below are exact descriptions of what a partial transcript certifies and how much posterior bias it leaves.

This tests the cost of discovering the connectivity retained by a spanning forest in DLMST. The graph here is just a union of cycles. Its representation by a finite group is the classical voltage-graph lift. The instance encoding, the partial-transcript calculation and the probability bounds are given here; historical priority for the combined result is unverified. [Khanna, Putterman and Song, Fact 2.5](https://eccc.weizmann.ac.il/report/2026/339/download/) · [Voltage lifts and cycles, Theorem 1](https://combinatorialpress.com/article/jcmcc/Volume%20050/vol-050-paper%2013.pdf) · [Three marked successors and their exact query costs](cyclic-order-certificates-for-a-sat-verdict.md)

## A graph of binary equalities

Use the eight triples of bits $(x,y,z)$ with product
$$
             (x,y,z)(u,v,t)=(x+u,y+v,z+t+xv)
$$
over $\mathbb F_2$. Put $A=(1,0,0)$, $B=(0,1,0)$, $Z=(0,0,1)$, and let $e=(0,0,0)$ be the identity. The first $w/2$ public vertex labels carry $h_i=A$ and the remaining labels carry $h_i=B$. The product of the $h_i$ in the order of any single successor cycle is either $e$ or $Z$, since the numbers of both colors are even. Both possible products are central, so rotation preserves the product.

Declare Boolean variables $U_{i,g}$ for every vertex and group element. Write the two binary Horn implications defining each equality
$$
                    U_{i,g}=U_{p(i),g h_i}.
$$
Pin $U_{0,e}$ true and $U_{0,Z}$ false. The lift of one full turn sends $(0,g)$ to $(0,gP)$, where $P$ is the cycle product. Since the lifted successors are a permutation, the equality component of $(0,e)$ contains $(0,Z)$ exactly when $P=Z$. Thus $P=e$ is exactly the SAT verdict. Each data row contains a constant number of clauses and depends only on $p(i)$. Use a constant amount of public satisfied padding between rows so a machine word can intersect varying fields from at most one row. Any access to a varying field is simulated with a query for its full successor, cached thereafter; the simulator may reveal strictly more information per queried row than the native solver uses.

A direct algorithm can recognize the public clause pattern, read all successors, and traverse from zero to compute $P$ while checking that the first return is after $w$ steps. The input convention uses dense variable ranges for $U_{i,g}$, with a fixed public order for the eight equalities and their two implications. Verify the names in a row all agree with the same decoded successor. Fall back to a general solver on a layout or cycle-promise failure. The recognized family takes $O(w)$ word steps with constant work words using indexed rows. As in the MST paper, a spanning forest of the equality graph suffices to decide the pin conflict.

When the product is $e$, the equality graph has eight cycles of length $w$. When it is $Z$, it has four cycles of length $2w$. Gap cycle counting in a stream and the one-cycle versus two-cycles connectivity problem are established uses of this topological distinction. Here the input reveals an indexed successor row of the base cycle of the solver's choice, with every other row available for subsequent queries. [Assadi et al. on gap cycle counting in streams](https://www.cs.princeton.edu/~hy2/files/stream_cycle.pdf) · [Nanongkai and Scquizzato on cycle connectivity and order](https://doi.org/10.1007/s00446-021-00418-2)

## Which partial reads suffice?

The known arcs of a partially observed cycle form paths. With $c$ such paths, each cyclic ordering of them is one possible single-cycle completion, and all are equally likely on a uniform input. Include isolated vertices as paths. For a path let $v\in\mathbb F_2^2$ be the sum of the first two coordinates of its vertex labels. Knowing the ordered vertices determines the whole group product along the path, including the factor at its tail. For two paths with projected vectors $v,u$, swapping them as adjacent blocks changes the central product by $Z^{\det(v,u)}$. This follows by multiplying the triples; central factors commute with all surrounding terms.

A transcript decides the sign exactly when all the path vectors lie in a single line through zero. In that case all the path products commute. If the vectors span the plane, arrange two independent vectors next to one another; swapping those paths produces two completions with opposite answers. Equivalently some one of the three nonzero linear functionals $\lambda$ vanishes on every path vector.

For each $\lambda$, mark vertices with $\lambda(h_i^{\rm proj})=1$. There are $w/2$, $w/2$ or $w$ marks. In cyclic order on this even number of marks, weight each intervening arc by its number of successors. To make all paths have even counts of these marks one must read at least the total weight of one of the two alternating pairings of consecutive marks. In fact pair neighboring marks inside each even path. These pairs give one of the two perfect matchings around the marked cycle and all their joining arcs were observed. Reading exactly the corresponding arcs conversely leaves even counts on each remaining path. For just two marks, the two pairings use the two opposite arcs. The full-observation case follows by choosing either alternating pairing. The minimum certificate for the verdict is therefore the least of these six sums. The two sums for each functional add to $w$. Every input has a certificate of size at most $w/2$, with equality on the alternating color order.

The worst-case deterministic discovery cost in this promise model is exactly $w-2$. With two paths their vectors sum to zero and hence agree. While $c>3$ and the vectors span the plane, removing the queried tail path leaves the other paths spanning the plane, because their sum equals its vector. Choose two independent ones. Answer the query by joining its path to a different remaining path, leaving those two independent. This adversary reaches three paths with both verdicts possible. The solver must query once more and both outcomes have completions.

## Querying a uniformly random cycle

For one fixed $\lambda$ let $o$ be the number of odd paths, meaning paths where $\lambda(v)=1$. It is even. A fresh successor query merges the chosen tail with one of the other $c-1$ paths, uniformly. When the tail is odd the count $o$ drops by two with probability $(o-1)/(c-1)$. Otherwise the count stays the same. An even tail always preserves $o$. Set
$$
 B_0=1,\qquad
 B_o=\prod_{j=2,4,\ldots,o}(j-1)/j=2^{-o}\binom{o}{o/2}.
$$
The quantity $cB_o$ cannot increase in conditional expectation. If $o>0$, choosing an odd tail preserves it in expectation because $(o-1)(B_{o-2}-B_o)=B_o$. An even-tail query gives $(c-1)B_o$. At $o=0$ all future paths remain even and $c$ decreases. Stopping when $o=0$ gives exactly $cB_o$ as the maximum expected number of paths that can remain at that time, by always choosing an odd tail until stopping. These are finite decision trees.

Extend an arbitrary exact query strategy past its decision using any fresh entries until one path remains. At the *first* decisive transcript, some functional has hit zero odds. The number of paths then remaining is at most the sum, over the three functionals, of the numbers of paths at their respective first hits. Therefore the optimal mean $Q$ of distinct queries until decision satisfies
$$
 w-w(2B_{w/2}+B_w)\ \le\ Q\ \le\ w-w B_{w/2}.
$$
The upper bound follows by targeting one color functional throughout. Since $B_m=\Theta(m^{-1/2})$, the optimal mean is $w-\Theta(\sqrt w)$. On these inputs every correct SAT solver must pay at least the lower bound in distinct data rows. This applies to an unlimited amount of offline computation between probes and arbitrary additional workspace.

Both verdicts have probability bounded below by a positive constant independent of $w$. For example rotate the cycle to start at zero, then exchange the second and third vertices whenever they have different colors. This is an involution on an event of probability bounded below, and changes the central bit. For every solver the expected number of rows still untouched when the answer becomes determined is $O(\sqrt w)$. Nonnegativity now bounds the conditional mean of this remaining count by $O(\sqrt w)$ separately on either verdict.

## Predicting the bit with a hard cap on probes

Let $n_A,n_B,n_C$ count the three kinds of nonzero path vectors and $M$ be their sum. The three counts have the same parity because the total vector is zero. Zero-vector paths contribute central factors independent of order. A uniform cyclic order can be sampled as a uniform linear ordering followed by forgetting the origin. Delete the zero-vector paths. Among the remaining paths, exchange the first unlike pair of types in positions $(1,2),(3,4),\ldots$, whenever such a pair exists. This involution changes the answer. If all three counts are odd there are no survivors, even when a last position is unpaired. If all are even the surviving orders consist entirely of like-type pairs, and all have the same sign. Indeed reordering pairs changes no sign, and equal-type factors commute. Labels within one type may have different central bits, but these contribute just one order-independent central factor.

Hence the absolute conditional bias, meaning the absolute difference between the two verdict probabilities, is zero in the odd case and otherwise equals
$$
 \frac{\binom{M/2}{n_A/2,n_B/2,n_C/2}}{\binom{M}{n_A,n_B,n_C}}.
$$
The empty ratio is one. This is the usual sign cancellation for inversions in a multiset word. On the initial cycle the magnitude is $\binom{w/2}{w/4}/\binom{w}{w/2}$. [Classical adjacent-pair involution for the Gaussian binomial at minus one](https://mathoverflow.net/a/454123)

In a nondecisive even state there is a type count $d$ with $2\le d\le M-2$. The chance that just this type occupies whole pairs is $\binom{M/2}{d/2}/\binom{M}{d}$. Its maximum over these even $d$ is $1/(M-1)$, by symmetry and the ratio $(d+1)/(M-d-1)$ when $d$ increases by two. This bounds the bias. For each functional $o_\lambda\le M$ and $B_{o_\lambda}\ge1/(o_\lambda+1)$ by the central binomial coefficient bound. Thus the posterior absolute bias is at most $\sum_\lambda B_{o_\lambda}$ in all states: the decisive case has a term one, the odd case has zero bias, and in the remaining case $3/(M+1)\ge1/(M-1)$.

For any strategy with at most $q<w$ distinct queries, expose fresh entries up to $q$ if necessary. The new information can only improve the optimal expected prediction. At this fixed time $c=w-q$. Applying the conditional-expectation bound for $cB_{o_\lambda}$ to all three functionals yields
$$
  \Pr[\text{correct}]\le
     \tfrac12+\frac{w(2B_{w/2}+B_w)}{2(w-q)}.
$$
Fixing and then averaging the algorithm's coins permits arbitrary randomized strategies. Any constant advantage therefore requires a cap of at least $w-O(\sqrt w)$, even on promised instances alone. This conclusion concerns a hard cap, whereas expected-cost algorithms can save probes by guessing on a fraction of runs.

The optimal cap for success $2/3$ on this distribution is in fact $w-\Theta(\sqrt w)$. To see attainability choose one color functional with $m=w/2$ initial odd paths and follow the greedy odd-tail strategy until it has no odd paths. Let $C$ be the terminal number of fragments. Its mean is $wB_m$. The quantity $c(c+1)/(o+1)$ also preserves conditional expectation at every greedy step. With $o>0$ the expectation after one merge is
$$
 (c-1)c\left(\frac{o-1}{(c-1)(o-1)}+\frac{c-o}{(c-1)(o+1)}\right)
 =\frac{c(c+1)}{o+1}.
$$
It follows that $\mathbb E[C(C+1)]=w(w+1)/(m+1)$ and $(\mathbb EC)^2/\mathbb E[C^2]\to2/\pi$. By the second-moment inequality, $\Pr[C\ge\mathbb EC/10]\ge(9/10)^2(\mathbb EC)^2/\mathbb E[C^2]>1/3$ for all sufficiently large $w$. Cap the queries at $w-\lceil\mathbb EC/10\rceil$ and guess a fair bit if the scalar test has not finished. The capped strategy achieves at least $2/3$ success. This upper bound concerns the specified uniform input distribution.

The formula has $\Theta(w\log w)$ encoded bits. One full scan obtains all $w$ successors, and linear word time suffices to use them here. The number of disclosed rows cannot count the further work needed for an unrestricted superlinear SAT proof. Lean verifies the group identities and the contextual block exchange. The probability and SAT arguments are written proofs. [Lean group law](../lean/CycleGroupVerdict.lean) · [Exhaustive partial transcripts and Horn connectivity](../audits/cycle_group_verdict_audit.py)
