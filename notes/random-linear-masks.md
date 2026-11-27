# Selecting a hard word from a random linear mask

**Research journal, 24 November 2026.** A source seeking to exclude linear SAT need not decide which of its candidate words have short programs. It would suffice to generate a random nonzero binary row in a subspace whose active coordinates name hard words. The subspace may be unknown to the source. Even if the rows individually have exponentially small probabilities, their **first one positions** need not. The quantitative parameter is the Shannon entropy lost inside that subspace. I do not have a source attaining the required bound for the genuine set of short-program outputs.

## Concentration from a hidden subspace

Number the coordinates of a row in $\mathbb F_2^N$ from the left. Suppose a sampler returns an explicit row by its deadline, and an event of raw probability $\alpha>0$ selects nonzero rows of one fixed subspace $V$ of dimension $D\ge1$. Conditional on that event let $P$ be the row distribution. Define its entropy deficit in bits by

$$
h=\log_2(2^D-1)-H(P).
$$

No description of $V$, $h$ or the event is supplied. For any ordered list of $N$ different candidate words, assume every coordinate which is nonzero on some member of $V$ names a hard candidate. The sampler returns the candidate at the first one of its row. With raw probability at least $\alpha/[2\lceil 2(h+1)\rceil]$ it returns **one fixed hard candidate**. On other runs it may return easy words, or return nothing.

Read the coordinate functionals on $V$ in order. Keep a coordinate exactly when it increases the rank of the functionals already read. There are $D$ such pivots, and the vector of their values maps $V$ bijectively to $\mathbb F_2^D$. If the first $j-1$ pivot bits vanish, every intervening dependent coordinate also vanishes. Thus the first nonzero position is a pivot. Under the uniform law $Q$ on $V\setminus\{0\}$ the $j$th pivot cell has probability $q_j=2^{-j}/(1-2^{-D})$. The tail after $J$ cells has probability at most $2^{-J}$. Its probability $p$ under $P$ satisfies $h\ge pJ-1$: group rows into the tail event and its complement in the relative entropy $D_{\rm KL}(P\Vert Q)$ and use binary entropy at most one. Take $J=\min(D,\lceil2(h+1)\rceil)$. The tail is empty if $J=D$, and otherwise has $P$-mass at most one half. At least one of those $J$ pivots has the asserted mass. Only a linear scan of the actual row is needed to return its first nonzero coordinate. [Finite pivot counts and weighted pigeonhole argument in Lean](../lean/PivotRowMass.lean)

The cap calculation for this particular extraction rule is exact. For a proposed maximum cell probability $b\ge1/D$, minimize the entropy deficit over distributions meeting that cap. Within each cell the minimum is attained by the uniform conditional distribution. The optimal masses are $r_j=\min(b,cq_j)$ with $c$ chosen to make the sum one. For another admissible probability vector $p$, subtract $D_{\rm KL}(r\Vert q)$ from $D_{\rm KL}(p\Vert q)$. The result is $D_{\rm KL}(p\Vert r)+\sum_j(p_j-r_j)\log_2(r_j/q_j)$. After subtracting $\log_2 c$ in that sum only capped entries remain; their two factors are both nonpositive. This proves optimality, including the uniform cap $b=1/D$. For example a distribution splitting its mass equally across the first $K\le D$ cells and uniform within each has heaviest cell $1/K$ and deficit $(K+1)/2-\log_2 K+\log_2(1-2^{-D})$. Thus the order $1/(h+1)$ for the first-one rule is sharp.

## A sufficient condition on actual programs

Use the [sparse phases of the hardness test](dense-hard-table-sampling.md). Namely $q_1=2$, $q_{j+1}=2^{q_j}$, the phase header is a short self-delimiting code $a(j)$, and $\gamma_j=\lceil\log_2\log_2(j+4)\rceil$. Put $d_j=|a(j)|+\gamma_j$ and $T_j=2^{q_j}(q_j+2)^j$. List the first $N=2^{d_j}+1$ words of length $q_j$. A candidate is easy when an exact program of at most $d_j$ bits prints it by $T_j$ on the fixed efficient literal reference. Call the corresponding coordinate set $E_j$. There is at least one hard candidate by prefix counting.

Suppose a fixed ordinary randomized routine on $j$ returns an $N$-bit row within $2^{\lfloor q_j/2\rfloor}$ steps on its selected runs. At infinitely many $j$ suppose a good event of probability $\alpha_j$ yields nonzero rows of a subspace $V_j$ with $v_i=0$ for every $v\in V_j$ and every $i\in E_j$. With $h_j$ the conditional entropy deficit above, the sufficient condition is

$$
\limsup_j 2^{\gamma_j}\frac{\alpha_j}{h_j+1}=\infty .
$$

Use only the eligible phases in this limsup. One fixed inputless source reads $a(j)$ from fair bits, obtains the row and returns the corresponding $q_j$-bit word. At those phases one genuinely hard word receives probability at least $c\,2^{-|a(j)|}\alpha_j/(h_j+1)$ by time $2^{q_j}$. Along a subsequence this exceeds $2^{-d_j}$ by an unbounded factor. It is inverse-polynomial in $q_j$ there. Linear SAT would give a deterministic program of at most $-\log_2 p+O(1)$ bits and time $2^{q_j}(q_j+2)^{O(1)}$ for an output of mass $p$ in this regime. Eventually both resources fit the definition of easy, a contradiction. In particular a uniform row in any nonzero such subspace, conditioned to be nonzero, has deficit zero regardless of the dimension. The returned row itself need have no heavy atom. [Coding implication for linear SAT](sampling-at-a-numeric-length.md)

The hard part is ensuring that $V_j$ vanishes on **future** easy coordinates. Uniform fair rows without any constraints pass that condition with probability only $2^{-|E_j|}$ if all easy coordinates are required to vanish. Sampling rows from the orthogonal complement of the outputs already seen at a shorter clock can leave new easy directions unconstrained.

Two unconditional tests quantify this obstruction. First suppose a purported subspace $W_j$ can have an explicit basis computed from $j$ in time $2^{q_j}\mathrm{poly}(q_j)$. There is a constant $c$ such that, at every sufficiently large phase, restriction to the easy coordinates has rank at least

$$
\min\{\dim W_j,\,2^{\gamma_j-c}\}.
$$

Compute the pivot positions by ordinary elimination. The matrix has at most $N^2$ bits. Every one of the first $2^{\gamma_j-c}$ pivot positions independently yields an easy word: a program reads $a(j)$ and a raw ordinal of $\gamma_j-c$ bits, runs this computation, and prints the candidate named by the specified pivot. Choose $c$ to cover the fixed compiler and algorithm, and use an integer header for $c$ if needed. Each program then fits $d_j$ bits and the later clock. These pivots supply independent coordinate functionals on $W_j$. In particular a uniformly sampled vector of such an explicit $W_j$ belongs to the kernel of the easy restriction with probability $2^{-\operatorname{rank}(W_j|_{E_j})}$. If the restriction has full rank that kernel contains only zero. This applies even to a construction that has already removed all easy words detected at its chosen early clock.

Second, consider the selected runs of any fixed routine above which read at most $\lfloor q_j/2\rfloor$ random bits. For any good event confined to those runs and any subspace satisfying the conditions,

$$
2^{\gamma_j}\alpha_j/(h_j+1)=O(1)
$$

unconditionally. Enumerate every random prefix of that length through the routine's cutoff. Credit only timely nonzero rows with no excess reads. Count first-one candidates and rank them by unconditional credited mass, breaking ties by index. This takes $2^{q_j}\mathrm{poly}(q_j)$ native steps. The first $2^{\gamma_j-c}$ candidates in the computed order are easy by the same ordinal programs. Every hard candidate has credited mass at most $2^{c-\gamma_j}$. Compare this with the concentration lemma on the good event. Thus finding a small public linear system or hiding the subspace behind a few random bits cannot realize the proposed condition.

## Low-degree checks on actual program outputs

There is a concrete high-dimensional choice of the desired mask space at every sufficiently large phase. Enlarge the candidate list to the first $2^{d+2}$ words, where $d=d_j$, so their last $n=d+2$ bits range over the whole $n$-cube. Use degree $k=\lfloor d/2\rfloor+1$ multilinear binary polynomials on these suffixes. Their dimension is $B=\sum_{i=0}^k{n\choose i}\ge 2^{d+1}$ by complementing subsets. Evaluation on the full suffix cube is injective. Requiring the polynomial to vanish on the suffix of **every** length-$q_j$ output from a name of length at most $d$ by $T_j$ imposes at most $2^d$ linear constraints. Thus the resulting masks have dimension at least $B-2^d\ge2^d$. They are all zero on the easy candidates. This calculation is only an existence argument; the constraints depend on actual program completions. It complements the [degree-closure coding bound](adaptive-hash-tables.md).

One cannot get the required probability just by conditioning a uniform polynomial on the constraints already observed. Let $s=2^{\lfloor q_j/2\rfloor}$, and let $R_s,R_T$ be the ranks of the monomial evaluation vectors of the actual outputs observable by $s,T_j$, respectively, using all the above monomials. Unconditionally there is a fixed $c$ such that, at every sufficiently large phase,

$$
R_T-R_s\ \ge\ 2^{\gamma_j-c}.
$$

Enumerate the short names through $s$, extract their suffix evaluation vectors and compute their span. Then scan the full suffix cube in order, appending a vector exactly when it increases the current rank. There are at least $B-R_s\ge2^d$ append operations. The first $2^{\gamma_j-c}$ appended suffixes each have a program of length at most $d$ printing the associated full candidate: use the phase and ordinal code as before. All matrix sizes are polynomial in $2^d$, which is polynomial in $j$, and the native simulation, scan and printing fit $T_j$. The newly produced evaluation vectors are independent modulo the old span, proving the inequality. A uniformly sampled polynomial vanishing on all early outputs therefore vanishes on all later outputs with probability exactly $2^{-(R_T-R_s)}$. Even though the final admissible polynomial space is large, the good-event probability of this proposed early sampler decays exponentially in $2^{\gamma_j-c}$. Other sources need not sample via these early constraints.

## Can repeated sampling remove the entropy loss?

For an unrestricted unknown support, an algorithm that sees only independent sampled rows cannot promise better than order $1/K$ for all row laws with entropy deficit at most $K$. Consider $K$ candidate coordinates and a probability vector $p$ on them. Let the row be exactly the $i$th unit vector with probability $p_i$. Treat the support of $p$ as the hard set. Every draw is sound, and its entropy deficit in the coordinate subspace spanned by the supported unit vectors is at most $K$. Require the postprocessor to return a candidate on every run and to respect the support for every $p$.

Let $F_i(p)$ be its output probabilities. Any bounded number of adaptive samples gives a continuous map of the probability simplex to itself, by summing probabilities of finite sampling transcripts. Even an almost-surely halting algorithm has continuous output probabilities if it halts almost surely for **each** $p$: the continuous probabilities of halting with output $i$ by a finite cutoff increase to $F_i$, and their sum at the limit is one, which also gives upper semicontinuity. The same argument handles private random coins. If the error on every face is less than $1/K$, then at a point with $p_i=0$ we have $F_i(p)<1/K$. This allows some error in support selection.

Apply the Brouwer fixed-point theorem to the continuous self-map with coordinates proportional to $\max(0,p_i+1/K-F_i(p))$. Their sum before normalization is at least one. A boundary fixed point would have a missing coordinate $i$ with $F_i(p)\ge1/K$, which is impossible. At an interior fixed point all these coordinates are positive, their sum before normalization is exactly one, and $F_i(p)=1/K$ for every $i$. Thus some source defeats any claimed stronger concentration guarantee for this sampling model. For a bound of $R$ samples, one can approximate the adversarial $p$ by a dyadic vector within total variation $1/(KR)$, giving maximum output probability at most $2/K$ by coupling. These artificial easy sets need not be those of a native interpreter. The exercise rules out a universal repair that only resamples unknown hard labels. Related work uses topological arguments to bound replicability in multi-coin estimation. [List and Certificate Complexities in Replicable Learning](https://papers.nips.cc/paper_files/paper/2023/file/61d0a96d4a73b626367310b3ad32579d-Paper-Conference.pdf)
