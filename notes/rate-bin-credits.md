# Growing families of deadlines and oscillation of first-production times

**Research journal, 24 November 2026.** Under linear-time SAT, the phase identity extends to a growing number of deadlines without a separate program header for each one. It forces release mass across a continuum of logarithmic time scales. A second construction spends its credits at a rate chosen from completed prior computations. Together the implications include a test for linear SAT based on weak convergence, with no prescribed convergence rate. [Synchronized phase identity and native model](near-clock-credits.md)

Use the same globally prefix-free native stream RAM, its feedback phases and the first $h=2^{j-b_s}+1$ selected lengths of each offered block. Full coverage uses $B(m)=2^{20m}$. Let $P_r$ be the normalized mask cost of phase $r$ including its success. A halting exact name $p$ becomes eligible in window $u(p)=\max(t_p+1,|p|^2+1,2)$, where $t_p$ is its halting time. Let $I_r$ be the sum of $2^{-|p|}$ over names arriving in phase $r$. There is a constant $\eta>0$ and a single infinite set of phases $\mathcal R$ on which $I_r\ge\eta P_r$ and $I_r\ge c/[r(\log(r+2))^2]$. This set is independent of the generators below. The phase's sole success has target-word weight at most $2^{1-r}$.

On the failed windows of a phase, put mass $2^{-m}/P_r$ at $\log_2(t)/m$ for each selected target word whose first short producer finishes at step $t\le B(m)$. Each target word is counted once at its own length. The resulting finite measure $\nu_r$ on $[0,20]$ has total mass at most two. The definition uses no SAT assumption.

## A positive share at each of exponentially many rates

Assume linear deterministic time for ordinary explicit SAT. In phase $r$ put $b=\lfloor r/2\rfloor$, $K=2^b$, and choose the centers $\alpha_k=3+(k+1/2)/K$ for $0\le k<K$. At length $m$ use the integer deadline

$$
  D_{k,m}=2^{3m+\lfloor(2k+1)m/(2K)\rfloor}.
$$

One fixed generator reads $\operatorname{gamma}(d)$ and a complete halting program $p$. It computes the phase of $u(p)$ by replaying earlier windows, then reads $b$ raw bits choosing $k$. Each such subcredit has normalized weight $2^{-|p|-d-b}$. Within a phase and bin, all its subcredits are assigned to distinct requested words in arrival order. The requests at $m$ are exactly the target words absent by $\lfloor D_{k,m}/m^a\rfloor$, in lexicographic order. With fixed $k$ the deadlines are increasing in $m$ during the phase. A decoder for this bin evaluates only that bin's missing-word counts. It can reset its queue at the beginning of the phase. Exhaustive evaluation of all previous-window outcomes to recover the phase uses $2^{o(m)}$ steps. At every sufficiently late phase the fixed-block counting and unranking argument fits $D_{k,m}$ for one fixed sufficiently large $a$, uniformly in $r,k$. The extra calculations for the clock use $O(m+b)$-bit quantities, $b\le s$, and eligible programs are enumerable in $2^{O(s)}\operatorname{poly}(s)$ time. [Native cutoff compilation](near-clock-credits.md)

The cell for $(m,y)$ paid by the given subcredit has $m-|p|-d-b$ raw bits. Its entirety fits at the selected grid since $|p|\le s$, $b\le s$, and $m\gg s$. Its complete name length is $m+|\mathrm{header}|+|\operatorname{gamma}(d)|-d<m$ with a fixed large $d$. Each bin clears its own queue by the phase's success. If an arriving credit remains outstanding at the end of the success, its queue was continuously nonempty throughout that window. Every requested word there was then funded at this bin, making the good block bad. Consequently **each bin** pays $2^{-d}I_r/K$ distinct target-word weight in every sufficiently late phase. Each first-production time of a paid word belongs to $(\lfloor D_{k,m}/m^a\rfloor,D_{k,m}]$.

The possible normalized times lie in the central interval

$$
        J_{r,k}=[\alpha_k-1/(4K),\,\alpha_k+1/(4K)]
$$

for all sufficiently late phases, since $K(a\log_2 m+1)/m$ tends to zero uniformly over their selected lengths. These intervals are pairwise disjoint. Even attributing the entire successful window to a single bin removes at most $2^{1-r}$ weight, and $K2^{1-r}=o(I_r)$ on $\mathcal R$. Therefore for some fixed $\rho>0$ and every sufficiently late $r\in\mathcal R$,

$$
       \min_{0\le k<K} K\,\nu_r(J_{r,k})\ \ge\ \rho. \tag{1}
$$

The same bound holds if each $J_{r,k}$ is replaced by the actual length-dependent time test before summing the weights. A proof that this scaled minimum tends to zero over all phases for every sufficiently large fixed $a$ would exclude linear SAT. A pigeonhole upper bound of constant order does not yield the required decay.

Every weak accumulation point along $\mathcal R$ dominates $\rho$ times Lebesgue measure on $[3,4]$. Indeed for each continuous nonnegative $f$ on $[0,20]$, (1) implies $\int f\,d\nu_r\ge(\rho/K)\sum_k\min_{J_{r,k}} f$. Uniform continuity and midpoint Riemann sums give the domination on taking a weak limit. The same calculation holds on any phases with I_r≥ηP_r and K2^(1−r)=o(I_r), in particular the retrospectively decidable high phases used in the limit argument. The countable atoms from individually specified clocks are compatible with this continuous lower component. [Limit measures](phase-limit-measures.md)

## Concentrating credits using the previous phase

The normalized sequence $\nu_r$ itself cannot converge weakly under linear SAT. There must even be a **fixed continuous function** $0\le f\le1$ on $[0,20]$ whose integrals in consecutive phases differ by a fixed positive amount infinitely often.

Use one uniform decoder with an additional self-delimiting integer $e$. For the moment fix $e$, let $L=2^{2^e}$, and place $L$ centers at $3+(k+1/2)/L$. Around each center take a closed interval of radius $1/(4L)$ and a continuous bump supported there, equal to one on the interval of half that radius. At the beginning of phase $r$, choose the interval of **least previous-phase mass** under $\nu_{r-1}$, breaking ties by its first index. The supports are disjoint and $\|\nu_{r-1}\|\le2$, so the prior integral of that bump is at most $2/L$. The computation is timely. Fully simulate the previous windows' short names to find first production times. Comparing $t^{4L}$ with powers of two tests the rational interval endpoints exactly. For each fixed $e$, even $L$ times this previous-phase work fits $2^{o(m)}$ throughout the current phase. The common factor $1/P_{r-1}$ is unnecessary when choosing the minimum.

Spend all current-phase credits at the chosen center using the same integer-clock rule, with $K=L$. A raw bin field is no longer required. The full name length is $m+|\mathrm{header}|+|E(e)|+|\operatorname{gamma}(d)|-d$, where $|E(e)|=O(\log(e+2))$. One can take $d_e=O(\log(e+2))+O(1)$ with the fixed header and parser. For instance, choose twice the sum of the header and parameter-code lengths plus a sufficiently large fixed constant. The machine reads $d_e$ as data. The clock exponent $a$ can remain fixed because $e$ only changes fixed factors in the previous-phase work and the integer-clock arithmetic. Phase resets remove dependence on early clock exceptions for this eventual assertion.

For each fixed $e$ and sufficiently late $r\in\mathcal R$, the current bump integral is at least $2^{-d_e-1}\eta$, by queue clearing and deduction of the successful window. All funded times lie in the bump's plateau once $m$ is large. The constant $\eta$ is independent of $e$. Choose $e$ fixed and sufficiently large that $2/L<2^{-d_e-2}\eta$. The current integral of the chosen bump then exceeds its previous integral by at least $2^{-d_e-2}\eta$ in every such phase. One of this finite library of bumps is chosen infinitely many times, proving the assertion.

Thus weak convergence of these particular actual measures, with no need to exhibit their limit or modulus, would be sufficient to exclude linear SAT. The existence of convergent subsequences of bounded measures is consistent with the conclusion. The prefix construction supplies no unconditional convergence theorem for this source.

Lean checks the bit accounting for rate splitting and the finite least-bin averaging bound. The queue, clock and weak-limit arguments are manuscript proofs. [Lean file](../lean/RateBinCredits.lean)
