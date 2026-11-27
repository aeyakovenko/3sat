# Disjoint sources of later reads in an actual SAT computation

**Research journal, 24 November 2026.** The half-read argument locates one cut in the solver's own input order. How many disjoint intervals of the *same run* must supply something the machine actually reads later? On the explicit quadratic 3-CNFs, a constant fraction of the first half of the intervals acquiring logarithmically many fresh signs do. The charged native read events for those intervals are all distinct. This statement applies to every deterministic solver with unrestricted work memory and unrestricted running time. [Half-read theorem](half-read-reuse.md) · [Explicit 3-CNFs](expander-cut-signs.md)

## Statement

Use the public layout with $2m$ independent signs, in $N=\Theta(m\log m)$ encoded bits. Use ordinary fixed-register word RAMs with polynomial address range and word alphabet, an input word exposing at most one data pin, and ordered native access slots. The signs are independent fair bits. For a fixed solver divide the first $m$ pin discoveries into complete consecutive epochs of $t$ fresh pins, starting at the initial state and cutting immediately after each $t$th discovery. Write $K=\lfloor m/t\rfloor$. The wall-clock lengths and input positions of those epochs may depend on all previous observations.

Call an epoch *retrieved* when a suffix access after its end satisfies either condition.

* The machine reads a data pin first observed during this epoch.
* It reads a work address whose contents at epoch end differ from its contents at epoch start, before any post-epoch store to that address.

The second event may retrieve a zero genuinely written over an earlier nonzero word. Distinct epochs witnessing the first condition own disjoint pins. For the second condition the latest actual store before the read was inside its owning epoch. Thus selecting a witness for every retrieved epoch gives pairwise distinct native read slots and source epochs. Several work reads may concern the same physical address in different versions.

There are absolute constants $a,p,c>0$ and a constant $C_M$ depending on the fixed solver's controller bound such that whenever
$$
      C_M\log_2 m \le t\le a m,
$$
the probability that at least $cK$ epochs are retrieved is at least $p$, for all sufficiently large $m$. At logarithmic epoch width this is $\Omega(N/\log^2 N)$ distinct epochs and later reads on one actual computation. For the dyadic widths in this range there is even a positive-probability set of inputs on which this conclusion holds at a positive fraction of all those widths. The within-width disjointness does not extend across widths.

## Some rows of every discovered partition carry rank

Let $F$ denote the sign of the complement-graph quadratic on the pins. Its binary cross adjacency has rank at least $\kappa m$ across every balanced split, for an absolute $\kappa>0$. Every constant-verdict coordinate subcube leaves at most nine coordinates free, so every run discovers at least $2m-9$ pins and all the specified cuts exist. These two properties and the character-matrix form of a quadratic are the only family-specific assumptions used below. [Expander and subcube proofs](expander-cut-signs.md)

On one full run let $S$ be the first $m$ distinct pins. Partition its rows into the complete discovery sets $X_j$ of size $t$ and a remainder of fewer than $t$ pins. Write $P_j$ for pins discovered before epoch $j$ and $Y_j$ for all pins outside $P_j\cup X_j$. Subadditivity under stacking row blocks, and inclusion $S^c\subseteq Y_j$, give
$$
   \kappa m\le t+\sum_{j=1}^{K}\operatorname{rank}_2 B[X_j,S^c]
        \le t+\sum_{j=1}^{K}\operatorname{rank}_2 B[X_j,Y_j].
$$
Here $B$ is the full complement adjacency. Set $a=\kappa/4$ and $\alpha=\kappa/4$. Since no term exceeds $t$, at least $\kappa K/2$ epochs have rank at least $\alpha t$. Call this event $R_j$. The balanced split used to prove this count may depend on the future, while $R_j$ itself depends only on the history through the epoch end.

## Simulating an epoch whose changes are never retrieved

Fix a possible full prefix $\pi$ through the start of one epoch. It fixes the values on the earlier set $P$, its entire memory $C_0$, and its controller. Conditional on this prefix, all remaining pins are independent fair bits. In this proof the analyzer gets $\pi$ for free. Use $R$ for the large-rank event at the end and $Q$ for retrieval on the suffix. Write $h=\Pr(R\mid\pi)$, $\beta=\Pr(R\cap Q\mid\pi)$.

Draw a fresh uniform public vector $Z$. On reaching the end of the epoch on a genuine original input, leave the pins in $P\cup X$ unchanged and fill the remainder from $Z$. Given the epoch-end trajectory, this companion reaches precisely the same end and has the same conditional distribution of completions as the original. Some fixed $Z$ therefore makes the mass of epoch-end trajectories with $R$ and a retrieval-free companion at least $h-\beta$. Fix this vector for this starting prefix.

There are few possible pairs $(X,c)$ on those trajectories, with $c$ the end controller. Run the companion suffix starting with the controller $c$, the *start* memory $C_0$, the known $P$-values, and the public $Z$ for every other pin. Keep all suffix stores. If the true companion is retrieval-free this simulation is exact, instruction by instruction. It never reads a pin of $X$. Any work read before local overwrite has the value it already had in $C_0$. Let $T$ be the set of read coordinates outside $P$ in the simulated suffix. Then $T\cap X=\varnothing$, and at most nine pins outside $P\cup X\cup T$ were missed by the entire companion run. Given $c$ one recovers $X$ as the complement of $P\cup T$ with those exceptions removed. The number of possible pairs is at most
$$
        J=|\mathrm{controllers}|\sum_{i=0}^{9}{2m\choose i}=m^{O_M(1)} .
$$
The catalog only uses simulations that halt. This bound is uniform over $\pi$, even if its work array is densely occupied.

For each catalog pair retain the epoch-end trajectories with the stated large rank and cheap companion. Their event is a cylinder $A_{X,c}\times\{0,1\}^{Y}$ in the cube conditional on $\pi$: once $X$'s values are fixed to a retained row, the trajectory uses no further unknown pin through epoch end, and the companion thereafter uses fixed $Z$. These cylinders are pairwise disjoint in the original conditional cube even when they have different row sets of coordinates. Their masses $u=|A_{X,c}|/2^t$ sum to at least $h-\beta$.

For each pair define a signed predictor depending only on $y\in\{0,1\}^Y$. Simulate the suffix with $c,C_0$, the true $P$-values and $y$, setting all $X$-values to zero. Use any fixed sign if the simulation fails to halt. Every actual original computation on this cylinder that is retrieval-free agrees with the prediction, by the same instruction induction. Consequently every predictor error on a retained cylinder implies $R\cap Q$ on the *original* input.

## The normalized correlation on a cylinder

After fixing $P$, the signed verdict on $X,Y$ is $(-1)^{x^\top B[X,Y]y}$ times a row sign and a column sign. If $b=\operatorname{rank}_2 B[X,Y]$, its real operator norm is $2^{(t+|Y|-b)/2}$. Indeed each distinct row character occurs $2^{t-b}$ times up to sign, and the distinct characters are orthogonal. For any signed predictor $g(y)$, Cauchy–Schwarz then gives
$$
    |\mathbb E[1_A(x)F(x,y)g(y)]|\le 2^{-b/2}\sqrt u .
$$
Here the expectation is on the whole conditional cube, rather than normalized on the cylinder. Its predictor-error mass is at least $(u-2^{-b/2}\sqrt u)/2$. Summing over disjoint cylinders and using $\sum\sqrt u\le\sqrt J$ proves
$$
     \beta\ \ge\ \tfrac12(h-\beta-\sqrt J\,2^{-\alpha t/2}).
$$
Choose $C_M$ so the final error term is at most $\kappa/4$. Averaging over each starting prefix and summing over epochs, the deterministic rank count proves that the expected number of retrieved epochs is at least $\kappa K/12$. A variable in $[0,K]$ with this mean exceeds $\kappa K/24$ with probability at least $\kappa/24$. Finally average the indicators of these successes over dyadic widths. Their expected fraction is at least $\kappa/24$, so a constant fraction of inputs succeeds on a constant fraction of widths.

## Forcing many disjoint reads on each verdict under a time budget

Suppose the solver takes at most $T$ access slots on every member at this scale. Fix either sign $\sigma$. For $t\ge C_M\log m$ as above, set $W=\max(1,\lceil 8T/(\kappa K)\rceil)$. On a fraction $\Omega(1/W)$ of the inputs *of that sign*, at least $\Omega(K/W)$ distinct epochs are retrieved. In particular, a solver running in $O(N)$ time on this family would have $\Omega(m/\log^3m)=\Omega(N/\log^4N)$ distinct retrieved epochs on an $\Omega(1/\log^2 N)$ fraction of each verdict, using logarithmic discovery width. This is a resource profile of a possible linear-time solver on these inputs.

Call an epoch short when it uses at most $W$ stores. On every full run at most $\kappa K/8$ epochs fail this condition. For one fixed starting history $\pi$ put $H=R\cap\{\mathrm{short}\}$, $s=\Pr(H,F=\sigma\mid\pi)$, and $\beta_\sigma=\Pr(H,Q,F=\sigma\mid\pi)$. At every epoch end at least $m$ coordinates remain free. The polar matrix of the quadratic restricted to them is $J+I+G_Y$ over the binary field, where $J$ is the all-ones matrix and $G_Y$ is the simple sparse adjacency. The diagonal of $I+G_Y$ is all ones and every row has at most nine ones. A row basis must cover all columns, so its rank is at least $|Y|/9$. Adding $J$ costs at most one rank. The bias of any binary quadratic with polar rank $r$ is at most $2^{-r/2}$, even with arbitrary linear terms. To see this, square the signed expectation and substitute the difference of two independent inputs. The inner average vanishes unless this difference lies in the polar kernel. Thus $s\ge(1/2-2^{-\Omega(m)})\Pr(H\mid\pi)$ regardless of the earlier pinned signs.

Use the same independent fill, now retaining only companions that satisfy $H$, avoid retrieval, and have sign $\sigma$. Some fixed fill covers mass at least $s-\beta_\sigma$ by at most $J$ disjoint high-rank cylinders. Here $J$ again denotes the catalog size. On one such cylinder $A\times\{0,1\}^{Y}$, the following rectangle cover describes retrieval *exactly*. For each $y$, start the baseline simulation with $C_0$ and stop it if it would read an $X$ pin. For a halting baseline without any such read, let $g(y)$ be its sign. For the remaining columns use any predictor sign. Include all columns with a baseline stop at an $X$ pin or a nonhalting baseline in one rectangle of full row extent $A$. Every genuine run there retrieves something, since a retrieval-free run would follow the baseline and halt without such a pin read.

For each native address $a$, add the rectangle consisting of the rows where $C_{\mathrm{end}}(x)[a]\ne C_0[a]$ and the ordinary halting columns where the baseline reads $a$ before a suffix overwrite. On these columns, if some such address is ever encountered the genuine run retrieves something at the first such encounter; otherwise the genuine run follows the entire baseline without retrieval. This proves the cover assertion. It uses at most $L=U+1$ rectangles where $U$ is the address-space size. Since every retained source epoch has at most $W$ stores, a point lies in at most $W+1$ cover rectangles. This multiplicity bound is where the time hypothesis enters.

Write $d_A=2^{-\alpha t/2}\sqrt{\Pr(A)}$. The sign imbalance on any subrectangle of this cylinder has magnitude at most $d_A$ by the same operator norm argument. Split columns according to $g$. Where $g\ne\sigma$, every genuine $\sigma$ input retrieves, so the mass of those columns within the cylinder is at most twice their retrieved $\sigma$ mass plus $d_A$. Where $g=\sigma$, every genuine $-\sigma$ input retrieves. Intersect each cover rectangle with these columns and sum. The $-\sigma$ mass there is at most the summed $\sigma$ mass over the intersections plus $L d_A$, which is at most $(W+1)$ times the retrieved $\sigma$ mass there plus $L d_A$. One more discrepancy estimate bounds the mass of these columns by twice their $-\sigma$ mass plus $d_A$. Adding and summing over the disjoint cylinders gives
$$
 s-\beta_\sigma\ \le\ 2(W+1)\beta_\sigma
     +(2L+2)\sqrt J\,2^{-\alpha t/2}.
$$
Both $L$ and $J$ are polynomial in $m$ for fixed $M$, so increasing $C_M$ makes the final error less than $\kappa/32$. Averaging $s$ over starting histories and summing over $j$ gives at least $(1/2-o(1))(3\kappa K/8)$. Therefore $\mathbb E[1_{\{F=\sigma\}}\#\mathrm{retrieved}]=\Omega(K/W)$. Since the count is at most $K$, conditioning on $\sigma$ and thresholding at a sufficiently small constant times $K/W$ proves the stated conditional probability. Disjointness of the selected read slots is the same last-writer or first-pin ownership as before.

## Where the time argument stops

The theorem forces many distinct sources and many distinct native reads. All destinations could be postponed to one final phase. Indeed on this same grid-expander family one solver has only $O(m/\log m)$ work loads, each paired with exactly one earlier store, with no pin rereads anywhere. All these pairs can cross one common time cut. [Tile construction and its limits](tile-matching-sat.md)

Fredman and Saks introduced chronograms in the online data-structure setting. Here the epochs come from a static decision algorithm's own order of seeing fresh data, the suffix is unconstrained, and its single output is a sign. The extra catalog step addresses this endogenous partition. The theorem's precise priority remains unverified. [Fredman and Saks](https://doi.org/10.1145/73007.73040) · [Finite virtual-memory and epoch bookkeeping](../lean/BirthEpochReuse.lean) · [Proof-component audit](../audits/birth_epoch_reuse_audit.py)
