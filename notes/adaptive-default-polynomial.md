# Approximating trees with a predictable answer at each work query

Consider a deterministic decision tree reading individual bits of a string $x$ and whole words of an array $Z\in[v]^U$. It can also depend arbitrarily on public data $y$. Each work query has a distinguished forecast, fixed by the history at that node. Cache answers so repeated queries require no new branch. Truncate with signed output zero upon exceeding $r$ distinct bit queries, $q$ distinct work queries, or $k$ work replies different from forecast. Give halting leaves either sign, and give divergent paths zero. A cap on distinct queries makes the branching tree finite after contracting local computation. The rule allows arbitrary deterministic input probes by the forecaster as long as its probes of $x$ count toward $r$.

For $0<\eta\le 1/2$ the resulting signed output has a real approximant of uniform error $\eta$ with **bit degree at most $r$** and **work degree at most $k+O(\min\{q,\sqrt{q(k+\log(1/\eta))}\})$**. Work degree counts distinct whole-word coordinates in a product. The work degree can always be capped at $q$ using the exact leaf expansion. All estimates hold simultaneously on every $(x,Z)$, including arrays that never occur at a real machine checkpoint. The degree bound does not depend on the size of the word alphabet.

## How many wrong leaves survive exact checks?

Fix $y$. For a signed leaf take the exact product of all its bit tests and all its tests requesting a work answer different from the forecast at that node. Each such latter factor tests equality with the specified actual branch label. For its remaining work tests let $e(Z)$ count the forecast equalities that fail, a sum of at most $q$ one-word indicators. Replace the conjunction of those tests by a univariate filter $P(e(Z))$, multiply by the signed exact product, and sum over signed leaves. A tree that has no signed leaves contributes zero.

At fixed $(x,Z)$, consider only leaves surviving the exact products. Along each candidate path, a bit test has a forced answer. A work query whose forecast is correct also has a forced answer. Where the forecast differs from the true word, there are exactly two possible compatible choices before pruning. Following the true reply consumes a one token; substituting the forecast consumes a zero token. Any other answer fails an exact factor. The sequence of tokens replays the leaf uniquely, even when a substituted reply changes all subsequent queries. For a leaf with $j$ exact nonforecast replies and $e$ false forecast replies this gives at most $\binom{e+j}{j}$ possibilities, independently of path length. Summing over $j\le k$ gives $\binom{e+k+1}{k}$. At $e=0$ only the true path can survive. If it ends at an abstention, its absent term has signed value zero. Thus $P(0)=1$ and the following inequality suffice.
$$
 \sum_{e=1}^q \binom{e+k+1}{k}|P(e)|\le\eta .
$$
The bit degree is exact because each leaf fixes at most $r$ bits. Conditional forecasts, addresses, bit positions, and branch labels are constants *along that particular leaf*. The work degree is at most $k+\deg P$ after expanding each product. Reducing repeated factors on the same address preserves its whole-word support.

## A weighted small-error NOR filter

Take $h=\lceil k+\log_2(2/\eta)+1\rceil$. For $q=0$ use $P=1$. For $h\ge q/2$ use the exact polynomial $\prod_{i=1}^q(1-e/i)$. Otherwise start with $\prod_{i=1}^h(1-e/i)$. For every $b=2^t h<q$ with integer $t\ge0$ multiply it by
$$
 C_b(e)=\frac{T_{n_b}((q+b-2e)/(q-b))}{T_{n_b}((q+b)/(q-b))},
 \qquad n_b=\lceil8h\sqrt{q/b}\rceil ,
$$
where $T_n(\cos u)=\cos(nu)$ and $T_n(\cosh u)=\cosh(nu)$. These factors all equal one at zero. Each has magnitude at most one on $[0,b]$ and at most $2\exp(-16h)\le 2^{-20h}$ on $[b,q]$, by $\operatorname{arcosh}((q+b)/(q-b))=2\operatorname{atanh}\sqrt{b/q}\ge2\sqrt{b/q}$. The degrees sum to $O(\sqrt{qh})$ by the geometric series, including integer rounding.

The roots dispose of $e=1,\ldots,h$. For each $e>h$ take the block $2^t h<e\le 2^{t+1}h$ (the strict endpoint ensures $2^th<q$). At least $t+1$ filters damp this block. The absolute root product is $\binom{e-1}{h}\le 2^{h(t+3)}$, using $\binom ah\le(\mathrm e a/h)^h$. The compatibility factor is at most $\binom{e+h+1}h\le 2^{h(t+4)}$. The number of grid points is at most $2^{h(t+3)}$. The sum in the block is consequently at most $2^{-h(17t+10)}$. Summing the geometric series gives the claimed accuracy. This also bounds the magnitude of the entire signed approximant by $1+\eta$ pointwise.

## Comparison and a sharp obstruction

The square-root dependence on the query budget has a precedent in the guessing-tree quantum query theorem, including for multi-valued answers. Small-error symmetric-function approximation and constructive polynomial filters are also established. Here the argument keeps the input-bit degree exact while handling arbitrary predictions and a variable error budget on real paths. Priority of this combination has not been established. [Beigi and Taghavi](https://doi.org/10.22331/q-2020-03-02-241) · [de Wolf](https://homepages.cwi.nl/~rdewolf/publ/qc/degreesymmf.pdf) · [Sherstov](https://web.cs.ucla.edu/~sherstov/pdf/algopoly-sicomp.pdf)

A suffix can test $q$ distinct binary cells and stop at its first one. Guess zero throughout. Every path uses at most one exception, but approximating its signed verdict uniformly over its possible initial arrays to constant error requires degree $\Omega(\sqrt q)$ by the approximate degree of OR. Thus a general uniform real approximant cannot remove the inspection budget from the result. The SAT application also needs a norm bound, so an unbounded sign-representation polynomial has different consequences. [SAT application](sparse-reply-sat-cuts.md) · [Lean verification of the binary replay code](../lean/SparseReplyPaths.lean) · [Finite tree and filter tests](../audits/sparse_reply_cut_audit.py)
