# SAT with one geometric tape and polynomial random-access scratch

Fix $d\ge1$ and $0\le\omega<1/d$. Consider deterministic SAT algorithms with random read-only access to an ordinary explicit input, one initially blank $d$-dimensional work tape with one nearest-neighbor head, and writable random-access words. Let $N$ be the encoded input length in bits. On each unsatisfiable input let $T$ count the steps through the first sound UNSAT signal, and $W$ the largest number of simultaneously **nonzero** scratch words during that run. The controller has constantly many logarithmic-width registers. Each step touches constantly many scratch words and the cell under the geometric head, then takes a unit move or stays. Standard constant-arity word operations are as in the packed reduction. The tape may hold one tape symbol or one logarithmic-width word per cell.

**Theorem.** A fixed recognizer that eventually signals on every unsatisfiable formula and signals only on unsatisfiable formulas cannot satisfy both $T=O(N^c)$ and $W+1=O((T+1)^\omega)$ on all its negative inputs if

$$
 (d+1+d\omega)c^2<c+d+1. \tag{1}
$$

In particular, this excludes every $c<\sqrt{(d+2)/(d+1+d\omega)}$. The threshold from (1) itself is the positive root

$$
 \frac{1+\sqrt{1+4(d+1)(d+1+d\omega)}}{2(d+1+d\omega)}.
$$

For $d=2,\ \omega=1/4$, the two thresholds are $\sqrt{8/7}\approx1.06904$ and $(1+\sqrt{43})/7\approx1.07963$. Thus (1) excludes $c=43/40$ on a planar tape with at most $O(T^{1/4})$ nonzero scratch words. The same exclusion holds if only the **time average** of the nonzero count is $O((T+1)^\omega)$. It permits larger peaks and arbitrarily many different scratch addresses over the run. A further two-parameter bound below distinguishes steps where the geometric head moves. Addresses may be arbitrarily scattered in the logarithmic-word address space.

## Sharing scratch states at time cuts and tape contents at local cuts

Consider one genuine run with $T\ge1$. The certificate uses integers $u,b\ge1$. Translate a grid of side-$u$ cubes by a uniform offset modulo $u$ in each coordinate. Each nearest-neighbor move crosses a cube boundary with probability $1/u$, and a stay never crosses. Some offset has at most $T/u$ changes between the cubes occupied at successive steps. Use the head position **before** each instruction to assign that instruction's tape access to a cube. A machine that accesses the next cell after moving can split the instruction into constantly many such events.

Within each cube, list its visits in time order and cut this list into groups of at most $b$ visits. Use full groups of $b$ followed by the possibly shorter last group. Across all cubes there are at most $T/b$ boundaries between consecutive groups of a single cube. Split the actual chronological time line whenever the cube changes or consecutive steps change group. There are at most $1+T/u+T/b$ chronological intervals. Several nonadjacent intervals may belong to one group.

The guessed directory gives the time endpoints of those intervals, the cube and group labels, and the grid offset. At each interior chronological boundary give the full controller including the head position, and a canonical list of the nonzero scratch words as sorted address/value pairs. There is a **single shared record** at each such boundary. The initial scratch array is implicitly zero. At the final endpoint only the controller and signal are needed. Between successive groups of a single cube, give its complete tape contents in canonical within-cube coordinate order, also as one shared record. The first group of every cube starts blank. The last group of a cube has no outgoing tape-content obligation. Hence only *internal* group boundaries charge $u^d$ words. There is no full-cube setup charge per newly visited cube. With constants depending on the model and $d$, the directory and records use

$$
 Y=O_d\!\left((W+1)(1+T/u+T/b) + u^d T/b\right) \tag{2}
$$

words. Signed coordinates fit $O(\log(T+2))$ bits per coordinate. An address and its value each cost $O(\log(N+2))$ bits. The formula itself is immutable and does not enter the snapshots.

For arbitrary guesses validate field ranges, nonempty interval lengths, the partition of the declared time, the starting controller and zero scratch, and the declared final negative signal. Sort records by cube and time to check that its distinct groups occur in order, its intervals cover each group once, and no group exceeds $b$ steps. Match its consecutive groups to their unique shared cube records. Check the canonical sorted sparse lists and sizes. Enforce global time and directory caps during parsing. These checks cost $(Y+1)\operatorname{polylog}(N+T+2)$ with a cap on the *claimed* data. They impose no trust in the labels of an unchecked run.

An existential defect picks one group and replays all its intervals in time order. It keeps the group's private cube contents across those intervals. Initialize this cube from its incoming shared record, or as an implicit zero map for a first group. At each interval initialize scratch from that chronological boundary's shared list and use the shared starting controller. Replay every instruction, checking that every accessed tape position belongs to the claimed cube, that the arithmetic and head moves follow the machine, and that immutable input loads get their actual packed words. A last instruction may move to a different cube after its tape access. Compare the actual ending controller and, at an interior chronological boundary, the *whole* scratch to the shared record. At the final endpoint compare the controller and signal only. Compare the ending cube contents with the shared outgoing cube record when one exists. Require no continuation past a halting or first signal state. The empty-run convention can be checked directly.

A scratch comparison uses a dictionary of its nonzero addresses. Compare its count and look up every pair in the proposed ending list. Stores that reset to zero remove a key. Each interval uses a fresh dictionary or clears its touched entries. The total number of entries initialized or compared over any one group is at most twice the full chart length. Only $b$ local instructions are replayed. Full initialization or comparison of a cube array is charged to an explicit internal record. For a group with no such record an initially zero sparse dictionary suffices, even if $u^d>b$. Fixed-dimensional tuple keys, word-width conversions and bounded dictionary operations cost at most a polylogarithmic factor. Thus any individual defect test, including sorting and validation of the directory, costs $(b+Y+1)\operatorname{polylog}(N+T+2)$. There is no multiplicative $Wb$ cost.

On the true run all these checks pass. Conversely, if they all pass, the computations for the groups give one legal global execution. Induct in chronological time. The active cube's current contents are exactly those produced by its previous visits, carried across gaps within a group and across the shared record between its successive groups. No other cube can write this cell. Scratch and control pass across every chronological boundary through a record checked on both sides. The first incoming states are the true initial states, so every replayed step is genuine. This argument covers erasures, reuse of old scratch addresses, and runs touching many more than $W$ distinct scratch addresses. It requires no bound on the number of last-write edges spanning a time cut. [Earlier consecutive-visit separator for distinct auxiliary cells](mixed-tape-dimension-threshold.md) · [Related signed cut verification](slab-product-tradeoff.md)

## A weighted chart for average scratch occupancy

Write $S_t$ for the number of nonzero scratch words immediately before instruction $t$, with $0\le t<T$, and $h_t$ for that instruction's head position. Define

$$
 A=\sum_{t=0}^{T-1}(1+S_t),\qquad
 M=\sum_{1\le t<T:\,h_{t-1}\ne h_t}(1+S_t).
$$

There are no endpoint scratch charges. The expectation over the spatial offset of the sum of $1+S_t$ at the interior cube changes is at most $M/u$. Fix an offset attaining this estimate. Within each cube, number its visits starting at zero. Choose a uniform residue modulo $b$, and start a new group just before each nonfirst visit whose local rank has that residue. The same residue can be used in every cube. All groups have at most $b$ visits, including the first and last partial groups. Conditional on the spatial offset, each nonfirst visit has probability $1/b$ of starting a new group. Such a cut pays for one $u^d$ tape snapshot and costs at most $O_d(1+S_t)$ further words for its chronological boundary. If the predecessor in actual time belongs to another cube, that chronological boundary has already been counted. Thus some residue gives the combined chart bound

$$
  Y=O_d\!\left(1+\frac{M}{u}+\frac{A+u^d T}{b}\right). \tag{4}
$$

The replay and soundness checks are exactly those above. In particular, the last interval's outgoing scratch is never copied or compared. Nothing requires finding either favorable offset on the clock of the verifier. If $A\le (T+1)^{1+\omega+o(1)}$, then $M\le A$ and (4) gives the same exponents as (2). This proves the average-occupancy version of (1) by the same iteration.

## Charging the public proof and the challenged group separately

Write $B(e,c)$ for the following uniform bounded computation assertion. For each fixed nondeterministic RAM, nonexistence of an accepting branch by native clock $R$ on $m$ public words has a sound nondeterministic certificate taking $(R^e+m^c+1)H^{o(1)}$ steps, $H=\max(2,R,m)$. Equivalently, the construction may use arbitrarily small exponent slack in these bounds. The standard packed compiler supplies an ordinary 3-CNF of $N=H^{1+o(1)}$ bits for existence of that accepting branch, with a local packed-word generator accessing the public input. Its gate construction and polynomial-logarithmic indexing overhead are charged. A hypothesized sound negative recognizer satisfying the two resource bounds gives $B(c,c)$ for $c\ge1$, by materializing the formula and simulating the recognizer on a general RAM. A sparse dictionary of signed coordinate tuples suffices for its tape on this baseline simulation. Both the baseline and each defect computation can be forcibly clocked on all guesses and positive formulas. [Packed encoding and complementary hierarchy](packed-band-transfer.md) · [Uniform checkpoint transfer](computation-history-theorem.md)

Assume $B(e,c)$ for $1\le e\le c$. On negative instances of that source, an actual signaling run on the virtual formula has $T\le H^{c+o(1)}$ and $W+1\le H^{c\omega+o(1)}$. Define

$$
 \alpha=\frac1{d+1},\qquad p=c\left(1+\frac{d\omega}{d+1}\right),
 \qquad g=\frac{p}{1/c+\alpha/e},\qquad x=g/e,\qquad y=g/c. \tag{3}
$$

Choose $b=H^{x+o(1)}$ and $u=H^{(c\omega+x)/(d+1)+o(1)}$, rounded to positive integers. Short runs of at most $b$ can be replayed directly in the certification of a negative signal. For longer honest runs, $b^d\ge H^{c\omega}$ at the level of exponents, so $u\le b\le T$ up to subpolynomial factors. To verify the claimed inequality, $x=p/(e/c+\alpha)$ is minimized at $e=c$, where $x=c\beta$ with $\beta=(d+1+d\omega)/(d+2)$. Thus it suffices that $d\beta\ge\omega$. When $d=1$, $\beta-\omega=2(1-\omega)/3>0$. When $d\ge2$, the numerator of $d\beta-\omega$ is $d(d+1)+(d^2-d-2)\omega>0$. This also establishes slack for integer choices. In the nontrivial range $\omega<1/d$ we have $\beta<1$. The iteration below uses only $g<e$ and hence $x<1<c$.

In (2), the dominant spatial and local terms have the same exponent,

$$
 c+c\omega-\frac{c\omega+x}{d+1}
  =c+\frac{d(c\omega+x)}{d+1}-x
  =p-\alpha x=y .
$$

The $T(W+1)/b$ term is at most this order by $b^d\ge H^{c\omega}$, and the additive $W+1$ term is covered when $u\le T$. Thus the honest chart uses at most $H^{y+o(1)}$ words. The outer verifier guesses that chart, then applies $B(e,c)$ to the nondeterministic computation searching for a bad group or failed structural check. All presentations can use a common cap. Its time is $H^{x+o(1)}$ because $x\ge y$. Its physical public input has $O(m+H^{y+o(1)})$ words, including the chart and the inherited source. Original formula reads use the same local generator, so the whole virtual formula need not be added to the physical input. Consequently the cost is bounded by $(H^g+m^c+1)H^{o(1)}$, since $xe=yc=g$ and guessing the chart fits. If $H=m>R$ then $H^g$ is paid by $m^c$ whenever $g\le c$. This proves $B(g,c)$. The outer simulator is a general nondeterministic RAM. Only the solver whose run the chart describes has the tape and scratch restrictions.

For the contradiction, assume (1), enlarging $c$ slightly above one if necessary. The reciprocal iteration in (3) is affine. Its slope is $\alpha/p<1$ and its fixed point in exponent coordinates is $g_*=c(p-\alpha)<1$, precisely by (1). Starting from $e=c>1$ the exponents decrease and stay at most $c$ until a finite step yields $g<1$. In particular $x=g/e\le1<c$ on this sequence. Strict inequalities permit rational exponents, computable integer caps and a fixed finite amount of accumulated rounding or simulation slack. If the original $\omega$ is irrational, it can likewise be relaxed to a slightly larger rational preserving (1) and $\omega<1/d$.

Apply $B(g,c)$ to the complementary native interpreter on an extension of its opponent's code, with public input of length $O(n_0)$ and a polynomial horizon $R=n_0^D$ for a fixed integer $D>c$. It costs $o(R)$ as $g<1$ and $D>c$. Concretely the bounded source accepts if it sees a rejecting branch of the opponent on its own full input. Use the nondeterministic nonacceptance recognizer itself as the opponent, relabeling its accepting halts as rejecting and all other halts as accepting. Then a discovered rejecting opponent branch says the source accepts and certifies that it does not. If the source never accepts, a nonacceptance certificate supplies just such a timely branch. A sufficiently wide fixed original source word and fixed-depth sparse simulation for narrower hosts implement the bounded universal test with slack. This is a contradiction for the restricted SAT solver through the local 3-CNF reduction. [Full clock, word-width and diagonal conventions](packed-band-transfer.md) · [Earlier two-resource iteration](native-treewidth-trade.md)

At the first step $e=c$ equation (3) gives $g=c^2\beta$. One step therefore gives the proposed square-root threshold. At the root in (1), the two sides of $c^2(d+1+d\omega)=c+d+1$ have $c>1$. Its right-hand side then exceeds $d+2$, explaining the strict improvement at every $\omega<1/d$. For $\omega=1/d$ both conditions meet $c=1$. This argument gives no exclusion of a linear solver with unrestricted scratch.

## When large scratch states occur mainly while the head stays put

Suppose $T=O(N^c)$ and $A=O((T+1)^{1+\omega})$, but $M=O((T+1)^{1+\rho})$ for $0\le\rho\le\omega\le1$. The weighted chart excludes these three bounds together whenever

$$
 (d+1+d\rho)c^2<c+d+1,\qquad (1+\omega)c^2<c+1. \tag{5}
$$

For example $d=2,\ \rho=1/4,\ \omega=3/4,\ c=43/40$ satisfy both strict inequalities. Thus the example with $c=43/40$ persists even if the time-average scratch count grows as $T^{3/4}$, provided its sum at tape moves is $O(T^{5/4})$.

For the proof let $p_\rho=c(1+d\rho/(d+1))$, retain $\alpha=1/(d+1)$ and put $q=c(1+\omega)$. Take $x=g/e$, $u=H^{(c\rho+x)/(d+1)+o(1)}$ and $b=H^{x+o(1)}$. For (4) the chart exponent is at most $\max(p_\rho-\alpha x,q-x,0)$. Choose

$$
 g=\max\!\left\{\frac{p_\rho}{1/c+\alpha/e},
                    \frac{q}{1/c+1/e}\right\}.
$$

Both nonconstant chart terms are at most $g/c$. This calculation retains the $A/b$ term without any hypothesis that $b^d$ dominates the scratch count. The defect clock still has exponent $x$ since $e\le c$. Each of the two maps inside the maximum is increasing in $e$, with its positive fixed exponent respectively $c(p_\rho-\alpha)$ and $c(q-1)$. Both are below one by (5). At every $e\ge1$ each map is strictly below $e$. If the iterates starting at $c>1$ never crossed one, they would decrease to a limit at least one, a fixed point of their continuous maximum. Neither map can equal that limit there. Thus a finite iteration reaches the same complementary diagonal. The strict conditions allow subpolynomial factors on the resource bounds by increasing the exponents slightly.

## Previous work and scope

Van Melkebeek and Raz proved the square-root exponent for pure $d$-dimensional work tapes with random input access. Williams explicitly includes a subpolynomial random-access store and obtains stronger numerical exponents in that regime, approximately $1.3009$ for one dimension and $1.1887$ for two. The spatial division and the alternating simulation of small-space computations have these precedents. The argument here charges a polynomial *peak* of nonzero random-access words at chronological cuts, and separately charges the full contents of just the tape cubes that have an internal rank boundary. Its derived curve need not be the best possible one even for this hybrid machine. Historical priority for the polynomial scratch tradeoff and this accounting has not been established. [van Melkebeek and Raz](https://pages.cs.wisc.edu/~dieter/Research/sat-t.html) · [Williams, §7](https://people.csail.mit.edu/rrw/automated-lbs.pdf)

Lean checks the gluing of locally verified states, the implication between the two rational exponent tests, and a finite iterate beyond the one-pass threshold. The experiment replays genuine groups and injects errors into both kinds of shared state. The machine simulations and asymptotic lower bounds have manuscript proofs. [Gluing lemma](../lean/HybridTileCuts.lean) · [Exact exponent checks](../lean/HybridTapeExponent.lean) · [Replay audit](../audits/hybrid_tile_cut_audit.py) · [Independent crossing-sequence proof and logarithmic endpoint](hybrid-tape-crossing-chart.md)

The [per-address read and write proof](hybrid-scratch-read-write.md) also handles sparse changes to large scratch states. It gives the planar exclusion $c=11/10$ for $\sum_a\min(r_a,w_a)=O(T^{4/5})$ and compares small positive peak exponents with a direct simulation using Williams’s model.

Using different side lengths for the tape axes recovers (5) and improves it for direction-dependent motion. For the planar $c=11/10$ example the smaller side can be one tape cell. [Axis-weighted proof and numerical check](axis-weighted-tape-cuts.md)
