# Retrieval or many changed work words in disjoint discovery intervals

Use the ordinary $N=\Theta(m\log m)$-bit SAT family with $2m$ uniform private pins and the discovery epochs of $t$ fresh pins each, through the first $m$ discoveries. Fix any correct deterministic solver. Write $H=\lfloor m/t\rfloor$, and let $W_j$ count work addresses whose contents at the end of epoch $j$ differ from their contents at its start. Say epoch $j$ is retrieved if the suffix reads one of its newly discovered pins or reads a changed work word before any subsequent overwrite at that address. Both events refer to genuine native instructions. The work word may include a zero written over an earlier nonzero. [Epoch definitions, disjoint witnesses and rank count](birth-epoch-reuse.md)

There are constants $a,c>0$ such that, for $1\le L$, $C_M(\log m+L)\le t\le a m$, on all but $O(2^{-cL}+2^{-ct})$ of the inputs **at least $cH$ different epochs** are each either retrieved or satisfy
$$
        W_j \ge c\,\frac{t^2}{L\log^2 m}.
$$
The constants may depend on the fixed controller and address-width bounds. This holds with no deadline, also conditional on either verdict. In a range where the displayed threshold is below one the alternatives give limited information. The memory term charges an actual change of value at an actual address. Distinct epochs with a charged change require distinct native stores. Likewise, witnesses to retrieval across different epochs are distinct native reads.

Consequently if there are at most $O(m\log m)$ stores through the first half of the pin discoveries, take $t=\lceil C L\log^3m\rceil$ in range, with $C$ sufficiently large depending on the store bound. On all but $2^{-\Omega(L)}$ of the inputs with that store budget, in the sense of an **unconditional exceptional mass**, $\Omega(m/t)$ of these disjoint source epochs are retrieved. The statement also holds on each verdict when the budget is uniform there. The suffix may take arbitrarily long and probe any number of initially zero words. For example $L$ of order $\log\log m$ gives inverse-polynomial-in-$\log m$ exceptional mass. This improves the probability statement for these wider intervals; the unlimited-time constant-density result also handles intervals as short as order $\log m$.

## The polynomial only needs to work on the actual sparse rows

Fix a full start prefix, so all earlier pins $P$ and memory $C_0$ are given to the analyst. An epoch's new pin set is $X$ of size $t$ and the unseen balance is $Y$. Call the end high-rank if the binary cross rank between $X$ and $Y$ is at least $\alpha t$. Every true run has at least $\alpha H$ high-rank epochs for a fixed $\alpha>0$ by the row-block rank argument. For one epoch choose an integer cap $W$ on $W_j$ and let $\lambda$ be the conditional probability of high rank, $W_j\le W$, and no retrieval.

Draw an independent fill and replace the still-unseen pins at epoch end by that fill. Conditional on the entire end prefix, high rank and $W_j\le W$ are already fixed, while the two completions are iid. Thus the expected original-and-companion joint mass is at least $\lambda^2$. For fixed fill, every companion satisfying all three tests comes from one of at most $J=m^{O_M(1)}$ pairs $(X,c_0)$, where $c_0$ is the end controller. Indeed, simulate from $C_0$ using the earlier pin values and the fill elsewhere. If no retrieval occurred this gives all later queried pin coordinates and at most nine missing coordinates remain to specify $X$. The qualifying prefix rows at each such pair form disjoint cylinders of masses $u$. Every row of these cylinders has $W_j\le W$. [Full companion reconstruction](birth-epoch-reuse.md)

Fix one cylinder $A$ and column $y$. Run its suffix on the start memory $C_0$, true earlier pins, and true $y$. If this simulation ever queries a pin of $X$ or runs forever, set its indicator and signed approximant to zero for this column. No retrieval-free true halt could then occur on that column. Otherwise it returns a sign $g(y)$, and $D(y)$ is the set of distinct addresses it read before local overwrite. Set $E(x)=\{a:C_{\rm end}(x)[a]\ne C_0[a]\}$. On this cylinder the true signed output restricted to retrieval-free runs is exactly
$$
           g(y)\,1[|D(y)\cap E(x)|=0].
$$
A first read of a discrepant word is itself a retrieval, regardless of what happens after the paths branch. All rows have $|E(x)|\le W$ even if the scan $D(y)$ covers all $U$ addresses.

Use the small-error NOR polynomial from the adaptive tree proof with $k=0$, grid $\{0,\ldots,W\}$ and error $\eta=2^{-4L}$. It is one at zero, pointwise bounded by one on this integer grid, and of degree $d\le\min(W,C\sqrt{WL})$, using the exact polynomial if needed. Its Newton expansion is
$$
 P(e)=\sum_{i=0}^d p_i\binom ei,\qquad |p_i|=|\Delta^i P(0)|\le2^i.
$$
The forward difference uses only the first $i+1$ grid points, so no bound off the grid is needed. In turn $\binom{|D(y)\cap E(x)|}{i}$ is a sum over $i$-subsets of the universe of the product of two subset-containment indicators. Consequently the approximant is a sum of row-column products, with sum of coefficient magnitudes at most $B=\sum_{i=0}^d2^i\binom Ui$. On excluded columns set every column factor to zero. No expansion in hypothetical dense arrays is needed. [Small-error construction](adaptive-default-polynomial.md)

Multiplying by the true verdict sign makes the exact restricted output the indicator of no retrieval. Each row-column product with its row restricted to $A$ has absolute correlation at most $2^{-\alpha t/2}\sqrt u$ by the rectangular spectral bound. The approximation error on $A$ contributes at most $\eta u$. Summation and Cauchy–Schwarz give
$$
       \lambda^2\le\eta+\sqrt J\, B\,2^{-\alpha t/2}.
$$
Take $W=\lfloor c_1 t^2/(L\log^2 m)\rfloor$ for sufficiently small $c_1>0$. Since $\log U=O(\log m)$, $\log_2 B=O(1+d\log(U+1))$ is a sufficiently small fraction of $t$. The controller catalog costs $O_M(\log m)$ in the exponent, absorbed by the lower bound on $t$. This proves $\lambda\le 2^{-2L}+2^{-\Omega(t)}$, uniformly over the starting prefix. Summing conditional expectations over the $H$ epochs and applying Markov's inequality shows that, except on the stated mass, fewer than $\alpha H/2$ high-rank epochs evade both charges. Both verdicts have constant mass asymptotically. To get the store-budget corollary, each epoch exceeding the cap uses at least $W+1$ native stores in its own disjoint interval. At the chosen $t$ fewer than $\alpha H/4$ epochs can consume those stores if the constant is large enough.

The theorem allows every destination read to occur in the same later phase. The tile solver on this precise family does exactly that and finishes in $O(N/\log N)$ time on the family. Thus even accurate localization of many genuine sources leaves an elapsed-time implication unproved. [Matching construction](tile-matching-sat.md) · [Finite checks of real sparse rows and the Newton expansion](../audits/sparse_epoch_change_audit.py)
