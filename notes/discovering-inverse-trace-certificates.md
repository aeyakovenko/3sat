# How many inverse-trace pins can a decision algorithm actually skip?

On the inverse-trace SAT family with $d$ varying pins, typical minimum certificates leave about $\log_2\log_2 d$ pins unread. An exact deterministic solver, however, can leave only **$O(1)$ pins unread on average**, even considering its accepting and rejecting runs separately. The algorithm may know the function and use arbitrary preprocessing independent of the input and unlimited computation between reads. The distinction comes from having to discover the certificate by queries. [Typical certificates and formula encoding](typical-certificates-for-inverse-trace-sat.md)

There is also a characterization for an algorithm allowed errors. Fix $k\ge1$ and cap the algorithm at $d-k$ distinct, adaptively chosen pin reads. Its optimal uniform success on inverse trace converges to the same limit as for the optimal tree with that cap on an independent random truth table. The optimal tree is allowed to depend on the table. The result holds in every fixed binary basis with uniform estimates. The numerical bounds below place the two-thirds cap between $d-5$ and $d-3$, inclusively, for all sufficiently large $d$.

## A random table on the last few unread coordinates

Write $A_{r,k}(z)$ for the best fraction of agreement with a given $r$-variable truth table $z$ among coordinate decision trees of depth at most $r-k$. Let $a_{r,k}=\mathbb E_Z A_{r,k}(Z)$ for an independent fair table. Querying one specified coordinate first shows $a_{r+1,k}\ge a_{r,k}$, so these values converge to $a_k$. Changing one truth entry changes the optimum agreement by at most $2^{-r}$. The bounded-differences inequality gives

$$
   \Pr[|A_{r,k}(Z)-a_{r,k}|>\eta]\le2\exp(-2\eta^2 2^r).
$$

Take $r=\lceil4\log_2\log_2 d\rceil$. On a cube through a uniformly chosen field element $x$, with a fixed $r$-set of free coordinates and coordinates based at $x$, the $2^r$ signs differ from fair independent bits in total variation by at most $O(2^{2^r}2^r2^{-d/2})$. This follows by summing the translated-pattern errors from the character bound. Choosing the usual base point of the cube instead may permute its table by a coordinatewise translation depending on $x$. The optimum and its agreement fraction are invariant under every such translation. [Li and Zhong, Lemma 4.1](https://arxiv.org/html/2610.27127v1#S4)

Set $\eta=1/\log_2 d$. Multiply the two error bounds by $\binom dr\le d^r$. The result tends to zero faster than any inverse power of $d$, since $2^r\ge(\log_2 d)^4$ and $2^r=o(d)$. With that probability of exception, *all* incident $r$-cubes have optimum within $\eta$ of $a_{r,k}$. A depth-$(d-k)$ tree may be assumed to query distinct bits and to continue to the cap. At the first $d-r$ queries its leaves partition the inputs into $r$-cubes. On each it has at most $r-k$ further queries. The union estimate controls even this adaptively chosen cube. For the reverse inequality query any fixed $d-r$ coordinates and then use an optimal tree for each residual table. The residual table is publicly determined by the prefix and the known function. This proves convergence of the optimum to $a_k$. Randomizing the tree cannot improve its average success under the fixed input law.

The convergence has an effective rate. For a fair truth table on $\{0,1\}^{r+1}$, the optimum is the maximum over first-coordinate choices of the mean of their two optimal child scores. Each candidate has expectation $a_{r,k}$ and is $2^{-(r+1)}$-Lipschitz in each independent truth entry. The bounded-differences exponential moment bound and a sum over the $r+1$ choices give

$$
 0\le a_{r+1,k}-a_{r,k}\le
       \sqrt{\ln(r+1)/(2\cdot2^{r+1})}.
$$

Summing gives $a_k-a_{r,k}=O(\sqrt{\ln(r+1)}\,2^{-r/2})$ uniformly in $k\le r$. In the preceding cube comparison one may take $r=\lfloor\log_2(d/4)\rfloor$ and $\eta=C\log_2 d/\sqrt d$ for a sufficiently large absolute $C$. The TV bound is then $O(d2^{-d/4})$ and the concentration bound beats $d^r$ by an exponential in $(\log d)^2$. It follows that the optimal agreement on inverse trace is within $O(\log d/\sqrt d)$ of $a_k$ uniformly for $k\le r$. For $k>r$ both quantities are between $1/2$ and their respective values for $r$ omissions. The tree count below bounds $a_r-1/2=O(\sqrt{\log(r+2)}\,2^{-r/2})$. Thus the same absolute error holds simultaneously for the **entire** curve of probe caps.

## A count uniform in the number of omitted pins

The number $T_{r,k}$ of full labeled trees with $r-k$ distinct probes along each branch satisfies

$$
 \log_2 T_{r,k}\le2^{r-k}\!\left(1+\sum_{i\ge1}2^{-i}\log_2(k+i)\right)
                  \le 2^{r-k}\bigl(1+\log_2(k+2)\bigr).
$$

The first one in parentheses pays for the output labels. At level $r-k-i$ there are at most $k+i$ coordinate choices per node. The last inequality uses concavity of the logarithm. For each fixed tree, agreement with the independent fair truth table is a binomial proportion. A union bound gives

$$
 a_k\le \tfrac12+
 \sqrt{\tfrac{\ln 2}{2}\,(1+\log_2(k+2))\,2^{-k}} .
$$

Indeed for any strictly larger agreement the failure probability decays exponentially in $2^r$. At $k=6$ the displayed upper bound is below $2/3$. At $k=3$ exhaustively enumerating all $2^{16}$ four-variable tables gives $a_{4,3}=45407/65536>2/3$. For each table take the best of the four first-coordinate splits with a majority prediction on each half. Monotonicity gives $a_3\ge a_{4,3}$. This proves the stated interval for the two-thirds cap. Its upper endpoint concerns a decision tree on the promised inputs with unrestricted local computation. [Reproducible decision-tree calculation](../audits/inverse_trace_decision_audit.py)

For exact solvers a uniform tail estimate yields a stronger conclusion than any fixed-$k$ cap. Write $S$ for the number of pins unread at the actual halt, and put $m=\lfloor\log_2\log_2 d+\log_2\log_2\log_2 d\rfloor$. For $1\le k\le m+1$ take

$$
 \epsilon_k=\sqrt{(\ln 2)(1+\log_2(k+2))\,2^{-k}} .
$$

By the same tree count and the binomial tail, the probability that one fair $r$-table admits agreement above $1/2+\epsilon_k$ is at most $\exp(-(\ln2)(1+\log_2(k+2))2^{r-k})$. The TV error and union over all incident directions and all these $k$ still cost $d^{-\omega(1)}$, since $2^{r-m-1}\gg r\log d$. Truncate the exact solver at $d-k$ distinct reads, keeping its verdict if it has halted and guessing a fair bit otherwise. The success is $1/2+\Pr[S\ge k]/2$ (allow the solver to finish its deterministic work using the known coordinates before truncating). Thus

$$
                 \Pr[S\ge k]\le 2\epsilon_k+d^{-\omega(1)} .
$$

For $k\ge m+2$ the event requires a monochromatic $(m+2)$-cube through the input. The first moment in the certificate proof bounds its probability by $d^{-\omega(1)}$. Summing the tail gives $\mathbb E S=O(1)$ because $\sum_{k\ge1}\sqrt{(1+\log_2(k+2))2^{-k}}$ converges. Conditioning on either sign costs at most a factor of two. The estimate applies directly to distinct private words read by an actual correct SAT solver, since each word depends on at most one pin. At least a constant mean saving is possible in the promise query model. Read a fixed $d-1$ coordinates and stop when both completions agree. Their signs agree with probability $1/2+O(2^{-d/2})$ by the two-shift bound.

## The constant for exact mean savings

The comparison with a fair table extends to the limiting optimum mean saving itself. For a fixed $K$ maximize $\mathbb E\min(S,K)$ over exact trees for an $r$-table. One can assume the tree reads at least $r-K$ coordinates on every input by extending early leaves. Changing one table entry affects one leaf of an optimal tree, containing at most $2^K$ points. Repair that leaf by full reading. By symmetry the optimum is Lipschitz in each truth entry with constant $K2^K/2^r$. For fixed $K$ its fair-table mean has a limit $b_K$ by the fixed-first-split monotonicity and the bound $K$. The same bounded-differences and incident-cube argument as above transfers $b_K$ to inverse trace. To apply the upper bound, extend the exact tree to at least $d-K$ reads before taking the prefix cut. An optimal local continuation gives the lower bound.

The omitted tail beyond $K$ tends to zero uniformly as $K\to\infty$ in the limit over $d$, by the preceding summable estimates. For independent fair tables on $d$ variables the direct tree count gives the same tail control. For example up through $k=\lfloor d/2\rfloor$ the exceptional term for each $k$ is at most $\exp(-(\ln2)2^{d/2})$. For larger $k$ use the tail at $\lfloor d/2\rfloor$ and sum over at most $d$ terms. This proves that both optimum mean savings converge to the same finite constant $\lim_{K\to\infty} b_K$. The fair-table optimum here is averaged over the random table as well as its input.

These results formalize a limit on discovering short certificates, a question prompted by DLMST's use of comparison certificates. They concern one explicit predicate in a coordinate-query model, and lower-bound the number of genuine pin reads by a SAT solver on the given encoding. The predicate exposes at most $d$ distinct pins, while the formula also contains the public field arithmetic. An unrestricted lower bound exceeding the encoded length would have to charge additional operations. Historical priority for the inverse-trace transfer is unverified. [Khanna, Putterman and Song](https://eccc.weizmann.ac.il/report/2026/339/) · [Prior work on average deterministic query complexity](https://arxiv.org/abs/2403.03530)
