# Hiding a source in a shuffled SAT product

Suppose a reduction takes a worst-case SAT file, renames its variables, and hides it among independent components of a larger file. How many components are needed before the query can have nearly the same distribution for every source? There is an exact finite answer for recoverable copies. Even for a balanced family of linear-time SAT instances of one encoded length $n$, polynomially many components leave worst-case statistical distance $1-2^{-\Omega(n)}$ from any one source-independent distribution.

## Exact capacity with advice

Fix $K\ge1$ source types. Each possible query $y$ has a list $S(y)$ of at most $t\ge1$ distinct recoverable types. On source $x$ the query has law $P_x$ and $x\in S(y)$ with probability one. A reducer may compare each $P_x$ with its preferred one of $A\ge1$ reference laws $D_1,\ldots,D_A$. Even if all preprocessing and decoding take unlimited time,

$$
\max_x\min_j d_{\rm TV}(P_x,D_j)\ \ge\
1-\min\left(1,\frac{t}{\lceil K/A\rceil}\right).
$$

Assign each $x$ a minimizing $j$. Some bucket contains $b\ge\lceil K/A\rceil$ types. Under its reference law, the probabilities of the respective list-membership events sum to at most $t$, so some assigned source has membership probability at most $t/b$. The same event has probability one under its own planted law. If the placement succeeds with probability $1-\delta$, subtract $\delta$ from the lower bound. The argument also works if each source uses a private mixture of the reference laws, by assigning it to the law maximizing its membership probability.

The bound is attained in the abstract list model. Partition the sources into buckets of size at most $\lceil K/A\rceil$. For a bucket of size $b$, sample a uniform subset of size $\min(t,b)$ as the reference list. On source $x$, condition this law on containing $x$. The distance to the reference equals one minus the probability of that event. Empty buckets can be discarded.

For $q$ queries with capacities $t_i$, suppose the source occurs somewhere with probability at least $1-\delta$. For each advice value fix $q$ reference marginals. If on every source its query marginals are within respective distances $\epsilon_i$ of the assigned advice marginals, then

$$
1-\delta\ \le\ \sum_i\epsilon_i+\frac{\sum_i t_i}{\lceil K/A\rceil}.
$$

Use the largest advice bucket and sum its marginal membership probabilities over queries and sources. At one source the reference sum is at most the second term. Apply the union bound under the actual query marginals there. The original queries can be dependent or adaptive, provided the claimed bounds on their unconditional marginals hold. Likewise if every marginal is pointwise dominated by $C$ times its corresponding reference law, $1-\delta\le C\sum_i t_i/\lceil K/A\rceil$. These inequalities allow arbitrary within-query padding.

## Exponentially many recoverable types in proper ternary DIMACS

Fix an even $r\ge4$ and a permutation $\pi$ of $\{0,\ldots,r-1\}$. Make two paths on $A_0,\ldots,A_{r-1}$ and $B_0,\ldots,B_{r-1}$ and add all matching edges $A_iB_{\pi(i)}$. Attach one pendant leaf to each $A_i$, three to each $B_j$, and one additional leaf at each of $A_0,B_0$. For every graph edge $uv$ put the positive proper clause $(h\lor u\lor v)$ in the file.

Pin $h,A_0$ and every even-indexed $B_j$ to zero. To pin $z$, append the four proper clauses $(\neg z\lor{\pm}p\lor{\pm}q)$ using all four sign pairs and the same two fresh variables $p,q$ for all pins. An incident edge between two pinned graph vertices now makes the formula unsatisfiable. Conversely, setting every unpinned graph vertex to one satisfies all edge clauses whenever the pinned vertices form an independent set. Alternating $B$ vertices have no internal path edge. Thus SAT holds exactly when $\pi(0)$ is odd. Exactly $r!/2$ of the files have either verdict.

With fixed variable names, clause and variable counts and every name's occurrence count are independent of $\pi$. With a conventional single-space, one-clause-per-line layout all files at this scale therefore have exactly the same encoded length $n=\Theta(r\log r)$ bits. Their variable-clause incidence graphs are connected. The source type survives any permutation of clauses, literal order, variable identifiers, or consistent variable sign changes. Group clauses by their sets of unsigned variables after discarding exact duplicate clauses. The fourfold supports identify and remove the pin gadgets. The unique common variable in the remaining triples is $h$. Removing it gives the original graph. Vertices of degrees 3 and 4 are precisely the $A$ path, and those of degrees 5 and 6 are precisely the $B$ path. In either induced path the marked endpoint has higher total degree than the other endpoint. Traverse the two oriented paths and read their matching to recover $\pi$. All operations take linear encoded time on the ordinary log-word RAM. Decimal names can be interned by a digit trie, and triples grouped by radix sorting their dense identifiers. On arbitrary components a decoder may discard malformed shapes after validation.

Here $K=r!=2^{\Theta(n)}$. Recovery from a batch of disjoint components gives at most one candidate per component. With $a$ bits selecting a reference distribution, achieving constant overlap for every source therefore requires $a+\log_2 t\ge\log_2(r!)-O(1)$. A promise that the input has a particular verdict still leaves $r!/2$ types. On the printed construction even the statistical distinguishing event has a linear-time recognizer given the source permutation. Clause shuffling, signed renaming and inserting other components preserve this test.

Arbitrary preprocessing may also preserve the type semantically. Take the same cone before its fixed pins and instead offer the future three-pin query $h=A_i=B_j=0$. Exactly the event $\pi(i)=j$ gives UNSAT. A preprocessed slot with a common decoder answering all these public pin queries therefore determines $\pi$, independently of its representation or preprocessing time. The list bound applies verbatim with one candidate per such slot. With a public decoder predicting $\pi$ up to $d$ incorrect image coordinates, each slot contributes at most $\sum_{j=0}^d {r\choose j} D_j$ possible sources if its prediction is a permutation, where $D_j$ counts derangements of $j$ elements. Fix the positions of disagreement and derange the images at those positions. Merely retaining the unpinned SAT bit requires none of this information.

## Exact leading storage cost when arbitrary preprocessing may make errors

For the same cones, choose a public continuation as follows. Draw a uniform row $i$, a fair bank $b\in\{0,1\}$, a uniform vector $u$ of $\lceil\log_2 r\rceil$ bits and a fair offset $v$. Pin $h,A_i$ to zero. Also pin $B_j$ to zero for those $j$ of parity $b$ satisfying $\langle u,j\rangle+v=1$ over $\mathbb F_2$, using the binary representation of $j$. Those $B$ vertices form an independent set. Consequently the answer is UNSAT exactly when $\pi(i)$ belongs to the chosen subset. The number of possible continuations is $O(r^2)$, each a proper CNF extension using $O(r\log r)$ encoded bits. Constantly predicting SAT gives accuracy $3/4$ on every permutation.

**Theorem.** Fix $0<\delta\le1/4$. The least worst-case number of bits in a summary that permits accuracy at least $3/4+\delta$ on these random future SAT queries for every $\pi$ equals

$$
              (4\delta+o(1))\log_2(r!).
$$

Both preprocessing and subsequent prediction may take arbitrary time. The decoder receives the summary and the public query, with no other access to the cone. Randomized preprocessing and prediction with private coins are allowed, with accuracy averaged over the coins and query for each fixed source.

To prove the lower bound, fix any summary and let $F_{i,b}(u,v)\in[-1,1]$ be its expected prediction sign, with SAT assigned $+1$. For a candidate image $j$ of parity $p$, write $\chi_j(u,v)=(-1)^{\langle u,j\rangle+v}$ and $\rho_{i,j}=\mathbb E_{u,v}[F_{i,p}\chi_j]$. The conditional accuracy for row $i$ under candidate $j$ equals

$$
 \frac12+\frac14\left(\mathbb E F_{i,1-p}+\rho_{i,j}\right)
 \ \le\ \frac34+\frac14\rho_{i,j}.
$$

Indeed the true sign is constantly $+1$ in the opposite bank and is $\chi_j$ in bank $p$. The characters for distinct $j$ in a fixed bank are orthonormal. Thus $\sum_{j\equiv p\bmod2}\rho_{i,j}^2\le\mathbb E F_{i,p}^2\le1$. At threshold $0<\tau<4\delta$, each row has at most $\ell=\lceil2/\tau^2\rceil$ indices satisfying $\rho_{i,j}\ge\tau$. For any permutation predicted with the required accuracy the mean of the selected $\rho_{i,\pi(i)}$ is at least $4\delta$. Since all correlations are at most one, the permutation must meet its row lists on at least

$$
s=\left\lceil r\,\frac{4\delta-\tau}{1-\tau}\right\rceil
$$

rows (take $\tau<1$). Choose $s$ agreeing rows and one listed image for each, then permute the remaining images. Consequently any fixed summary predicts at most $\binom{r}{s}\ell^s(r-s)!=r!\ell^s/s!$ permutations at the specified accuracy. Taking $\tau=1/\log_2 r$ for large $r$ gives $\log_2(s!/\ell^s)=(4\delta-o(1))r\log_2r$. Covering all $r!$ permutations takes at least this many bits up to an additive constant for variable-length summaries. Even with randomized preprocessing, each source has some summary achieving the promised mean accuracy. For the matching upper bound store the images on the first $\lceil4\delta r\rceil$ rows, answer those rows exactly, and answer SAT on other rows. Fixed-width images use $(4\delta+o(1))\log_2(r!)$ bits. More general work on permutation compression studies distortion measures on the recovered permutation itself. Here performance is measured on binary SAT answers, allowing completely inconsistent predictions. [Wang, Mazumdar and Wornell](https://arxiv.org/abs/1406.7435)

The storage conclusion also permits shared public coins independent of the source. Otherwise on some sequence of scales there would be a fixed $\eta>0$ with at most $(4\delta-\eta)\log_2(r!)$ bits. For each public seed, the union of all summary lists at advantage $\delta-\eta/8$ then covers a $2^{-\Omega_\eta(r\log r)}$ fraction of uniformly chosen permutations, taking $\eta<4\delta$. Even choosing the best summary private to each source leaves the mean success at most $3/4+\delta-\eta/8+o(1)$. Averaging over the public seed contradicts the guarantee on every source.

The list bound applies to $t$ such slots by summing the maximum number of permutations predicted at the specified accuracy per slot. Thus with polynomially many slots, one of which meets the threshold on every planted outcome, reference overlap bounded below by a positive constant on every source requires at least $(4\delta-o(1))\log_2(r!)$ bits selecting the reference law. This last statement assumes a good slot on each outcome. A bound averaged over the preprocessing coins alone need only force a positive probability of a good slot at a slightly lower threshold.

## A globally correct solver with a fast average and two slow planted answers

There is a deterministic SAT RAM that takes linear time on every product of these components. Per component, search for two variables meeting every ternary support. Branch on the three variables of an unhit support, at depth at most two. For a covering pair try its four valuations, then solve the residual 2-CNF by strongly connected components. This is a constant number of linear passes and is correct on every component where it succeeds. Here $h,p$ meet every support. Use general SAT on components without such a cover. This also handles arbitrary signed renamings of the control family. [Aspvall, Plass and Tarjan, linear-time 2-SAT](https://doi.org/10.1016/0020-0190(79)90002-4)

Modify this one fixed global program to spend $L^4$ steps before deciding whenever the component parser finds either of two distinguished permutations, the identity or the transposition of 0 and 1. Here $L$ denotes the complete encoded input length. The delay uses four nested counters of logarithmic width. Consider $t$ components, with $1\le t\le r^c$ for a fixed $c$, using consecutive disjoint namespaces and the stated layout. With probability $1/2$, draw all permutations independently and uniformly from the positive types. Otherwise use a uniformly chosen negative slot and draw its negative type uniformly, with all other types independently positive. The product SAT verdict is exactly balanced. Each component has probability $2/r!$ of being the marker of its own sign. The union bound puts the expected extra work at most $O(t L^4/r!)$ for the conventional layout with fixed namespace per slot. The total length is independent of all the selected permutations and is polynomial in $r$, so this single unrestricted program has expected time $O(L)$. The estimate also holds using polynomial maximum length when a packing introduces variable amounts of padding.

Now plant the identity in a designated slot with positive background components, or plant the transposition there with the same background. Both genuine runs cost at least $L^4$ and their verdicts are opposite. Only the two matching clauses in the planted component change. The delay is deliberate and verifies a limitation of this timing test. Even an exactly balanced average linear clock on a shuffled product does not control either planted run. The original globally correct program before adding the delay is fast on both.

Classical worst-case-to-average-case restrictions on nonadaptive self-correction for NP and conditional limits on OR/AND compression allow much broader reductions. The counting argument here uses the explicit requirement that a source type be recoverable among relatively few candidates. General joint semantic transformations may discard the type entirely, and a single SAT verdict has one bit. No unconditional SAT RAM time separation follows. [Feigenbaum and Fortnow](https://doi.org/10.1137/0222061) · [Bogdanov and Trevisan](https://doi.org/10.1137/S0097539705446974) · [Drucker on OR and AND compression](https://people.csail.mit.edu/andyd/newlimits.pdf) · [Dell and van Melkebeek on sparsification](https://pages.cs.wisc.edu/~dieter/Papers/sparsification-jacm.pdf)

The finite audit reconstructs all 24 and 720 sources at $r=4,6$ under seeded signed renamings and independently solves their CNFs. It tests every three-pin question for every $r=4$ source and checks the advice rounding and conditional subset construction on 80 small parameter triples. It also solves all 1,536 affine-mask continuations at $r=4$ and verifies the exact correlation identity on 3,840 predictor/permutation pairs. [Reproducible audit](../audits/recoverable_component_hiding_audit.py)
