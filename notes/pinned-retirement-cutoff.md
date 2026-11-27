# Selecting a default scale and certifying a priority cutoff

Write $b_j$ for the priority bit at scale $M=2^j$. The default is one. At stage $i$ the first $a_i=O(\log\log(i+4))$ requirements become eligible. Previously retired indices stay retired. The first eligible index $e$ signaling within its own $\lfloor 2^i/2^{e+1}\rfloor$ interpreter instructions wins, chooses the stage color, and retires. The simulation of a candidate depends only on $i,e$. This note uses the proved fact that each fixed sound detector of either color spends $\Omega(2^j)$ steps at every sufficiently late scale on which it signals. [Priority algorithm and pinned SAT formulas](priority-pinned-sat.md)

## Selecting an index from a batch

In each block $B_h=[2^h,2^{h+1})$ there is a scale of color one for every sufficiently large $h$, since at most $a_{2^{h+1}}$ indices through the block can have won with color zero. The disjunction of the positive pinned formulas in such a block therefore has a known answer.

Consider a fixed uniform partial deterministic algorithm on the block label that returns a scale $i\in B_h$ with $b_i=1$ whenever it succeeds. Its execution takes $\Omega(2^i)$ native steps on every sufficiently late success, where the cost is measured on the chosen scale's machine. Indeed a sound color-one detector on scale $j$ finds $h=\lfloor\log_2 j\rfloor$, runs the selector, and signals precisely when the returned index equals $j$. A block implementation using words of $O(2^h)$ bits can be simulated in the chosen scale's $O(j)$-bit words with constant-factor width normalization and $o(2^j)$ setup on any putatively cheap execution. The same argument covers a list of certified outputs, charging the cost to generate and inspect that list. A guess that merely asserts a block contains some default yields no identified index.

The indexing bound is tight. Test the actual priority bit at successive scales starting at $2^h$, stopping at the first default. The total cost through the returned $i$ is $O(\sum_{k\le i}2^k)=O(2^i)$. A proposed reduction would refute its hypothesized ordinary SAT algorithm if explicit query generation, the actual SAT calls, and index extraction together cost $o(2^i)$ on infinitely many successful blocks. Deciding the block disjunction alone yields its already-known truth value.

## The price of omitting the highest-priority tests

Set $L(j)=\lceil\log_2(j+2)\rceil$, $m(j)=\max(0,j-L(j))$. Let $u(j)$ be the least rank winning in the finite window $m(j)<i\le j$, capped at $a_j$, with $u(j)=a_j$ for an empty window. Then $u(j)\to\infty$, since every bounded set of ranks wins only finitely often. A direct computation of $u(j)$ costs $O(2^j)$.

Given a sound lower bound $r\le u(j)$, compute the exact retired set through $m(j)$, then replay the remaining stages while omitting ranks $e<r$. This returns the true $b_j$. With the incoming retired set correct, the actual winner, when present, has rank at least $r$. Every eligible candidate preceding it failed to signal. Removing the low ranks preserves that winner and the next retired set. If there was no winner, removing tests preserves that outcome. Induction proves the replay claim. The ordinary setup and two geometric series give cost

$$
O\!\left(2^{m(j)}+2^{j-r}+2^{j/4}\operatorname{poly}(j)+\operatorname{poly}(j)\right).
$$

Here the second term sums the original per-index budgets over the retained suffix and all window stages. The third allows the native interpreter's fixed-limb tables. All constants can be chosen independently of the supplied $r\le a_j$. [Lean proof of finite-window replay](../lean/RetirementCutoff.lean)

There is a further cost if one feeds the retained trials through the ordinary 3-CNF compiler. Since $2^{a_j}=\Theta(\log j)$, even the advertised budget of the last active rank at stage $j$ is $\Theta(2^j/\log j)$. A worst-case certificate allowing that entire trial still pays the compiler's order-$j^3$ factor in encoded bits. An empty suffix has no such trial, and an instance-specific early halt may also be cheaper.

**Finite-window lower bound.** For every fixed deterministic partial procedure $P$ returning only sound lower bounds $r\le u(j)$, there are $C,\delta>0$ such that every sufficiently late output with $r\ge C$ costs $P$ at least $\delta 2^j$ steps. Build a detector for each color by running $P$, performing the pruned replay, and signaling on the corresponding answer. On scales where $P$ returns, the appropriate detector has a uniform positive lower-bound constant. Choose $C$ so that the $2^{j-r}$ term is smaller than a quarter of the lower bound. The remaining setup is $o(2^j)$. This proves the claim even for procedures undefined on other scales. In particular, a procedure with sublinear cost on all its successful scales can certify only bounded cutoffs.

For any uniformly cheap, divergent rank target $k(j)\le a_j$, the particular claim $k(j)\le u(j)$ is true except on $O(L(J)a_J)$ of the first $J$ scales. Each winning stage spoils at most $L(J)$ subsequent windows, including the window ending at that stage. Nevertheless, any fixed sound deterministic procedure signaling that claim takes $\Omega(2^j)$ at every sufficiently late success, by returning $k(j)$ as its cutoff. Density alone therefore supplies no cheap individual positive certificates in this construction.

## Permanent retirement and common prefix advice

For each color $c$, the set of indices of that color that ever retire is computably enumerable and many-one complete for the halting problem. Given a machine $p$, compile a fixed detector that at scale $i$ simulates $p$ on its designated input for at most $i$ steps and signals if it halts. The index paired with $c$ is computable from $p$. For a halting $p$ this detector signals within budget at all sufficiently large stages. Once it is active, only finitely many smaller indices can preempt it, so it retires. For a diverging $p$ it never signals. This is the standard settling-time phenomenon applied to the actual rank enumeration. [Settling-time functions of computably enumerable sets](https://www.math.uwaterloo.ca/~csima/papers/settlingtime.pdf)

In particular, any oracle computing an unbounded rank cutoff $s(j)$ such that no index below $s(j)$ wins **after** stage $j$, for all sufficiently large $j$, computes the halting set. With the finite starting threshold hardwired, find $j$ with $s(j)>e$ and replay through $j$ to decide whether $e$ ever retires. This conclusion concerns permanent retirement. The finite-window quantity $u(j)$ is computable.

Conversely, let $W$ be the single infinite characteristic sequence of all ranks that eventually retire, in index order. Give the simulator only its first $k(j)\le a_j$ bits, for any $k(j)\to\infty$, however slowly. After ordinary replay through $m(j)$, find the longest initial segment of those bits for which every marked index has already retired. Its length $r(j)$ tends to infinity. For any fixed prefix, all the marked retirements in that prefix have occurred by a fixed finite stage. All unmarked indices never win. The chosen prefix is safe to omit, and the displayed replay bound gives an exact $o(2^j)$ computation of $b_j$ on all scales with this common prefix advice. A fixed finite common prefix would simply be a constant in a uniform machine. The advice here differs from unconstrained scale-dependent advice, where one bit could directly supply $b_j$.

The finite-window lower bound and the common-prefix upper bound concern this explicit pinned family. Neither supplies a short uniform certificate for the unrestricted SAT target.
