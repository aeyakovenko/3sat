# Multiplying every binary matrix pair from the mean cost of returning certified entries

Suppose a procedure on two independent uniform binary $d$-square matrices reports an expected fraction $\delta>0$ of their product entries. It may mark any other entry unknown. Every report is correct on every input and every random tape. Let $\tau$ bound its **mean** running time on uniform matrices, with finite expected time there. Then a randomized RAM computes the whole product over $\mathbb F_2$ on **every** pair, always correctly, in expected time
$$
                    O\!\left((\tau+d^2)\frac{\log(d+2)}{\delta}\right).
$$
The algorithm needs neither $\delta$ nor $\tau$. Densities and costs may both vary with $d$. The mean can be substantially smaller than the longest running time of the partial procedure. The proof below restarts with independent initial masks to accommodate the possible correlation between a long run and an unfilled table.

Couteau, Melissaris and Sajith give the random rank-one walk, its spectrum, the four product masks and an inverse-quadratic agreement bound for noisy predictions. Shinkar and Singh explicitly treat reported entries with erasures, building on Gola, Shinkar and Singh. Their one-sided routines can already certify a complete product. Here we use the observable erasures to bound the expected cost in terms of the mean cost per query and to apply it to actual clocks of a SAT solver. Priority for this particular accounting is unestablished. [Couteau, Melissaris and Sajith, Lemma 4.1 and Theorems 5.1 and 6.3](https://arxiv.org/html/2611.04680v1#S4.Thmtheorem1) · [Shinkar and Singh, Lemma 14](https://drops.dagstuhl.de/storage/00lipics/lipics-vol353-approx-random2025/html/LIPIcs.APPROX-RANDOM.2025.29/LIPIcs.APPROX-RANDOM.2025.29.html) · [Gola, Shinkar and Singh, Algorithms 2–3](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX-RANDOM.2024.34)

## A stationary walk with exact entry corrections

Randomly shift the rows of the left factor and the columns of the right factor cyclically, independently and uniformly. Undo the shifts on the reported entries. For any fixed output position its reporting probability averaged over uniform factors is now the same number $\mu\ge\delta$. Uniform factor pairs stay uniform under these shifts, so the expected cost is still $O(\tau+d^2)$.

For any fixed target $(A,B)$ draw uniform independent $R,S$. Start four computations with factor pairs from $\{R,A+R\}\times\{S,B+S\}$. The four products sum to $AB$. Each starting pair has the uniform product distribution. Walk from each pair $(U,V)$ by replacing it with $(U+E,V+F)$, where $E=uv^{\mathsf T}$ and $F=xy^{\mathsf T}$ use four fresh uniform binary vectors, including zero. Each walk is stationary in its own marginal. Keep the correction to its starting product by adding
$$
                 EV+(U+E)F.
$$
Both summands cost $O(d^2)$ bit operations using the outer-product factors. Any reported entry of the current product becomes a certified entry of the starting product at once. Cyclic shifts are used only for the oracle call; the walk moves on the unshifted factor pair.

For a Walsh character indexed by a matrix $H$, the eigenvalue for a step in one factor is $\mathbb E_{u,v}(-1)^{u^{\mathsf T}Hv}=2^{-\operatorname{rank}(H)}$. Indeed averaging over $v$ gives the indicator $u^{\mathsf T}H=0$. The eigenvalue for two factors is the product of their eigenvalues. Each nonconstant character therefore contracts by a factor at most $1/2$.

For a fixed coordinate of a given walk let $I_j$ indicate a certified report in step $j$. The mean hit function on the state space is $f(U,V)\in[0,1]$. The oracle and the cyclic shifts use fresh coins at each observation. At positive lag $h$, stationarity and the eigenvalues give
$$
   \operatorname{Cov}(I_j,I_{j+h})
     =\langle f-\mu,P^h(f-\mu)\rangle
     \le 2^{-h}\mu(1-\mu).
$$
Thus $\ell$ observations have expected count $\ell\mu$ and variance at most $3\ell\mu$. The probability of zero hits is at most $3/(\ell\mu)$. For $\ell\ge48/\delta$, each coordinate of each starting product is missing with probability at most $1/16$. A union bound gives probability at least $3/4$ of obtaining all four terms of that coordinate of $AB$. This calculation uses only marginal stationarity. No independence across coordinates or across the four initial masks is needed.

## An observable stopping rule under a mean running-time bound

At stage $j=0,1,\ldots$, take $\ell=2^j$. Perform $b=\lceil4\log_2(d+2)\rceil$ independent experiments of length $\ell$, drawing fresh starting masks for every experiment. Merge certified entries of $AB$ obtained by four-term reconstruction in any one experiment. Stop on a full table. Entries from previous stages can also be kept.

At each stage with $\ell\ge48/\delta$, the probability that some coordinate remains unfilled is at most $d^2(1/4)^b\le1/4$, even if the stage starts empty. Each complete stage has expected work $O(b\ell(\tau+d^2))$. Every observation is marginally uniform, regardless of how its cost and its success are correlated. Execute a whole stage or charge its full cost if stopping early. Its fresh randomness is independent of the event that the stage was reached. Costs up to the first adequate stage form a geometric sum. Beyond it the stage costs double while the probabilities of reaching them fall at least fourfold. Summing proves the stated expected bound. For coverage one, a single four-term experiment on the initial uniform pairs suffices in expected $O(\tau+d^2)$: at finite $d$ zero expected erasures means all entries are reported almost surely. A RAM implementation can interleave a step of deterministic schoolbook multiplication with each step of the randomized algorithm and return the first complete product. This gives an absolute $O(d^3)$ clock, including on exceptional coin tapes, changes expected time by at most a constant factor, and keeps all loop counters within logarithmic width.

## Substituting two actual SAT continuation clocks

Use the [adversarial last-packet experiment](native-product-time-from-last-packet-clocks.md). For a globally correct deterministic SAT program let $a$ be the common prefix clock for each factor pair and let $b_{ij}$ be the smaller of the two opposite-sign suffix clocks for its queried entry. Each completed race certifies the bit. Choose prefix and per-sign deadlines $U,h$. Return no entries if the prefix times out. Otherwise return all entries with a completed race. For uniform factors and an independent uniform index define
$$
\begin{aligned}
 \delta &= \Pr[ a\le U,\ b_{ij}\le h ],\\
 W &= d^2+\mathbb E\!\left[\min(a,U)+
          {\bf 1}_{a\le U}\sum_{ij}\min(b_{ij},h)\right].
\end{aligned}
$$
For finite caps take polynomial deadlines available within the cost bound. An uncapped race needs no step counter. Keep two overlays on the frozen state; log an address only on the first write by its continuation and clear its touched flag once after the race. This needs storage proportional to the number of distinct addresses even on a long execution. The resulting replay time is $O(W)$ in expectation. This includes setting up the physical signed master, each replay and each one-bit answer. For non-power dimensions zero-pad within the SAT encoding and retain only original indices.

Whenever $\delta>0$, the resulting worst-case expected clock for **exact** full binary matrix multiplication is $O(W\log(d+2)/\delta)$. With no caps and finite mean, it improves to $O(d^2+\mathbb E[a+\sum_{ij} b_{ij}])$. These form scalar benchmarks for the proposed matrix attack on SAT. No known unconditional lower bound on worst-case zero-error RAM multiplication at the required scale supplies a contradiction here. In particular, the distribution of clocks on randomly permuted SAT files can be very different from the clocks in the last-packet experiment.

[Exact finite audit of the walk, corrections, and a biased erasure procedure](../audits/low_rank_erasure_amplification_audit.py) · [Lean correction, Walsh, and counting identities](../lean/LowRankErasureAmplification.lean)
