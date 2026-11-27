# How long auxiliary cells must stay live in a multidimensional tape grate

Fix a dimension $d\ge2$. A trace has one head on $\mathbb Z^d$ and a fixed number of auxiliary heads on separate linear tapes. Each head moves to a neighboring cell or stays. The graph on the $T$ times $0,\ldots,T-1$ has forward chronological edges and forward edges between consecutive visits to each work cell. Deleting times removes the incident edges. The lower-bound constructions read a command stream strictly forward. These conventions specialize to the plane-plus-line construction at $d=2$. [Mixed-tape proof and PPST game](mixed-tape-pebble-frontier.md) · [PPST, §§3 and 5](https://trotter.math.gatech.edu/papers/34.pdf)

At the gap after time $i$, let $L_i$ count auxiliary cells having a visit at or before $i$ and another visit strictly after $i$. The cell contains a potentially useful past visit in this graph regardless of the stored symbol. There is exactly one consecutive-visit edge of that cell crossing the gap. Define

$$
A=\frac{1}{T}\sum_{i=0}^{T-2} L_i
  =\frac{1}{T}\sum_{a\text{ auxiliary cell visited}}(\operatorname{last}(a)-\operatorname{first}(a)).
$$

A cell visited once contributes zero. Use the empty sum when $T=1$. Let $W$ count distinct auxiliary cells visited, so $A\le W$.

**Theorem.** There is a constant $C_d$ such that deleting at most $C_d Q(T,A)$ vertices leaves weak components of size at most $C_d Q(T,A)$, where

$$Q(T,h)=T^{(d+1)/(d+2)}(h+1)^{d/(d+2)}.$$

For every integer $h\ge0$, put $H_h=|\{i:L_i>h\}|$. There is also a deletion set of size at most $2H_h+C_d Q(T,h)$ leaving weak components of size at most $C_d Q(T,h)$. These upper bounds permit auxiliaries with arbitrary motion.

Conversely, for every fixed $d\ge2$, a fixed machine with one $d$-dimensional head and one linear head has arbitrarily long traces with $W=\Theta_d(T^{1/d})$ for which deleting any $\gamma_d T$ vertices still leaves at least $\alpha_d T^2$ reachable ordered pairs, for constants $\alpha_d,\gamma_d>0$. Integer deletion caps are rounded down. A single such family also costs $\Omega_{d,R}(T)$ placements in every fixed number $R\ge1$ of rounds of the PPST two-person game.

## Two shifts for the upper bounds

First consider any subset of the original edges in which the sum of the durations of the auxiliary edges is at most $hT$, for real $h\ge0$. Let the duration of $(i,j)$ be $j-i$. Use all the original vertices to index time and tile visits even if some vertices have already been deleted. Fix integers $u,q\ge1$.

Partition $\mathbb Z^d$ into half-open cubes of side $u$ by independently shifting each axis uniformly modulo $u$. The probability that two positions belong to different cubes is at most their $\ell_1$ distance divided by $u$. The distinguished head moves at most once per step, so the bound for positions at $i,j$ is $(j-i)/u$. Its own cell edges have equal endpoint positions. Chronological durations sum to at most $T$. Choose a spatial shift with at most $(h+1)T/u$ remaining edges crossing cubes, and delete their sources.

Within each cube rank its original visits in time order starting at zero. Partition ranks into intervals of at most $q$ consecutive integers by shifting a periodic cut uniformly modulo $q$, allowing a shorter first and last interval. For an edge whose endpoints lie in that cube, of rank span $r$, the chance it crosses a cut is at most $r/q$. The same shift may be used in all cubes. Auxiliary rank spans sum to at most $hT$ since ranks differ by at most elapsed time. Within a cube visited $v$ times, the rank spans of consecutive-visit edges of one distinguished-head cell telescope to at most $v$. This still bounds the sum for any surviving subset of its edges. There are at most $u^d$ such cells per cube, so their total rank span is at most $u^d T$. A surviving chronological edge inside one cube has rank span one. Some rank shift therefore requires deleting at most $(u^d+h+1)T/q$ further edge sources. Each resulting weak component lies in a single rank interval and has at most $q$ vertices.

If $h+1\le T^{1/d}$, take

$$
 u=\left\lceil [T(h+1)^2]^{1/(d+2)}\right\rceil,
 \qquad q=\lceil Q(T,h)\rceil.
$$

The spatial edge term is at most $Q(T,h)$. Since $u^d=O_d(T^{d/(d+2)}(h+1)^{2d/(d+2)})$ and $d\ge2$, the rank edge term is $O_d(Q(T,h))$. If $h+1>T^{1/d}$ then $Q(T,h)\ge T$ already. Taking the original edge set and $h=A$ proves the first assertion.

For the second assertion delete the two incident times $i,i+1$ of every gap with $L_i>h$. This costs at most $2H_h$. Consider a maximal run $a,\ldots,b$ of such gaps. Every time in $[a,b+1]$ is now deleted. A surviving auxiliary edge crossing any gap in this run must begin before $a$ and finish strictly after $b+1$. When $a=0$ this is impossible. Otherwise it also crosses the low gap $a-1$, which at most $h$ original auxiliary edges cross. Every low gap still has at most $h$ surviving auxiliary edges. Summing over all gaps gives a surviving auxiliary duration sum at most $hT$. The two shifts applied to those surviving edges prove the assertion. They use original consecutive-visit edges throughout.

## Density of live auxiliary cells

Suppose every deletion of at most $\gamma T$ vertices leaves at least $\alpha T^2$ reachable ordered pairs, with $\alpha,\gamma>0$ fixed along a family. Components of size at most $q$ have at most $qT$ reachable ordered pairs in total, since $\sum_i |C_i|^2\le q\sum_i |C_i|$. The average bound implies $A=\Omega_{d,\alpha,\gamma}(T^{1/d})$, hence some gap has that many live cells. The trimmed bound gives more. Choose a sufficiently small constant $c>0$ and put $h=\lfloor cT^{1/d}\rfloor$. For all large $T$, $C_d Q(T,h)<\min(\alpha,\gamma)T/2$. If $H_h\le\gamma T/4$, the trimmed deletion would meet the budget while reducing the number of reachable pairs below $\alpha T^2$. Thus **at a positive fraction of all gaps there are at least $cT^{1/d}$ live auxiliary cells**, even if peak auxiliary occupancy has no prescribed upper bound. The conclusion is about simultaneously open consecutive-visit intervals. It does not require any particular stored values or useful data flow.

## Realizing the lower threshold with two heads

Use the robust outer DAG indexed by $s$ from the mixed-tape proof. After the bounded-degree replacement it has at most $C s$ vertices, $s$ designated inputs and $s$ designated outputs. Write

$$
 \ell=\lceil s^{1/(2(d-1))}\rceil,\qquad m=\ell^2,\qquad M=sm .
$$

Give each outer vertex a permanent $\ell\times\ell$ sheet of $m$ lane cells in the first two coordinates, all other coordinates constant on that sheet. In a box of integer side $K m$, use disjoint sheets with aligned origins. Their number is $(K m/\ell)^2(Km)^{d-2}=K^d m^{d-1}$. A fixed integer $K$ suffices since $m^{d-1}\ge s$. The $\ell_1$ diameter of the box is at most $dK m$. All between-sheet journeys therefore cost $O_d(m)$ physical moves.

On each sheet the old affine permutations of $(\mathbb Z/\ell\mathbb Z)^2$ still have $O(m)$ row-major traversal cost, including wraparounds. For each outer edge and each of the constant number of permutation labels, fill the line cells $0,\ldots,m-1$ from the source sheet. Drain them in reverse order while visiting the permuted lanes on the destination sheet. Each lane connection is the consecutive-visit path on its source cell, its line cell during that transfer, and its destination cell. Mark at most two lanes per deleted step, the permanent lane currently under the head if present and the buffered source lane in the current transfer if present. This covers every intermediate visit on the three-cell path. The robust-terminal proof requires the surviving outer paths to have at least $2\lceil\log_2 m\rceil+1$ edges, which follows at all large $s$ from their $\lfloor\sqrt s\rfloor$ lower bound. All pruning and mixing estimates use just the two-dimensional sheet expander and the bounded-degree outer graph. Thus deleting at most $aM$ times leaves more than $7M/8$ input hubs and $7M/8$ output hubs with all retained input-output pairs connected. The finite-alphabet command interpreter for this fixed dimension can ignore its work symbols. [Three-cell transfer and terminal proof](mixed-tape-pebble-frontier.md) · [Blocki and Cinkoske, Corollary 17](https://doi.org/10.4230/LIPIcs.ITCS.2021.64) · [Klawe's expander replacement](https://www.cs.ubc.ca/sites/default/files/tr/1992/TR-92-03.pdf)

Scanning hubs and the bounded number of passes per edge takes $T=\Theta_d(sm)$ steps, and the line visits $W=m$ cells. Because $s=\Theta_d(m^{d-1})$, this gives $W=\Theta_d(T^{1/d})$. Together with the density conclusion it attains the order of both the peak and the average necessary activity.

For the simultaneous game assertion, concatenate $k$ stages of the same $s$, putting each next input sheet at its predecessor's matched output sheet. The disjoint paths on shared permanent cells transport the retained terminal sets across each interface. Each additional stage costs $\Theta_d(M)$ steps. The stacked-stage argument requires $\Omega(M)$ total placements in $k$ rounds. It only uses the preceding robustness guarantee and the interface paths. [PPST game induction and antecedents](mixed-tape-pebble-frontier.md#several-rounds-in-the-ppst-game)

To choose one family for all fixed round bounds, take $0\le j\le\lfloor (\log_2 N)/2\rfloor$, $k_j=2^j$, and

$$s_j=\left\lfloor\left(\frac{N}{2^j(j+1)^2}\right)^{(d-1)/d}\right\rfloor.$$

Even the smallest $s_j$ tends to infinity. With $m_j$ and $M_j$ as above, concatenate the $k_j$-stage runs, reusing the line from its origin. Each run takes $\Theta_d(N/(j+1)^2)$ steps. Returning the heads to the origin between runs costs $O_d(m_j)$ per run and fits the same bound. The total length is $T=\Theta_d(N)$ and $W=\max_j m_j=\Theta_d(T^{1/d})$. The $j=0$ stage alone occupies a positive fraction of $T$ and supplies the quadratic-pair grate assertion after adjusting constants. For $j=\lceil\log_2 R\rceil$ in range the Challenger may begin at the last vertex of that particular run. The paths witnessing the $k_j$-stage strategy lie entirely inside it, so extra times elsewhere cannot defeat the strategy. Fewer rounds give the Pebbler no greater power. This yields $\Omega_d(T/[R(1+\log R)^2])$ placements and covers every fixed $R$ on the same family.

The finite audit checks the rank and spatial shift counts on 12,636 short traces in dimensions two and three, plus two longer out-and-back sweeps. It recalculates the surviving occupancies after trimming the high cuts. [Reproducible enumeration](../audits/mixed_tape_frontier_audit.py)

The geometry and uniformity here are for each fixed $d$. At $d=1$ the sheet layout is unavailable. PPST's positive segregator argument for ordinary linear tapes uses their precise computation-graph and block conventions. The stated bounds concern native step graphs. They do not give a separation of machine time classes. The earlier plane-plus-line note separately proves a block-respecting realization for PPST's epoch model. Priority of the dimension and activity refinements remains unverified. [PPST](https://trotter.math.gatech.edu/papers/34.pdf) · [Planar epoch realization](mixed-tape-pebble-frontier.md#geometric-block-graphs-at-ppsts-clock)
