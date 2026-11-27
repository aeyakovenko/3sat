# Advice for predicting which early omissions survive

**Research journal, 24 November 2026.** I tried to approximate the final halting-output set by tabulating early completions and supplying an error correction for each block of the residual list. On the actual plain interpreter, the sum of the correction lengths must be linear in the size of the cube. This holds even if predicting one block can take exponential time and receives the entire early observation table. There is an analogous lower bound on prediction errors with exact feedback inside each block.

Use the [plain program model](full-cube-advice.md). Put $N=2^q$, $T=N(q+2)^{\lceil\log_2(q+2)\rceil}$ and $\tau=(q+2)^{\lfloor(\log_2(q+2))/2\rfloor}$. For programs of length at most $q-2$, write $E_t$ for the $q$-bit words printed and halted on by time $t$. The genuinely late words are $E_T\setminus E_\tau$. The final hard words $A_q=\{0,1\}^q\setminus E_T$ number more than $N/2$. All claims below hold unconditionally at every sufficiently large $q$ on each fixed efficient plain interpreter.

## A separate message for every block

Sort the early omissions $R=\{0,1\}^q\setminus E_\tau$. Split this list into consecutive blocks of $M$ words, with one possibly incomplete final block. A fixed local algorithm receives $q$, a block index, a binary advice string for that block, and random access to the entire early table and its sorted omission list. It outputs the subset of the block that it predicts will remain hard at $T$. A malformed output or timeout denotes the empty subset. Advice can vary arbitrarily with the true future completions. Two explicit settings for the time $U$ to predict one whole block are

* $U\le2^{q/2}$, with $M$ the largest power of two at most $q/8$.
* $U\le N(q+2)^C$ for a fixed $C$, with $M$ the largest power of two at most $(\log_2(q+2))^2/8$.

Integer logarithms may replace the logarithms in the two block choices. The algorithm and tables use an ordinary bounded native computation. The block order can also be any fixed reordering computed from the early table within its construction budget.

For every fixed rational $\delta>0$ with $\delta\le1$, there are constants $\rho,\gamma>0$ such that the following holds. If the total number of local advice bits is at most $\rho N$ and the predicted set $S\subseteq R$ has at least $\delta N$ words, then
$$
 |S\cap(E_T\setminus E_\tau)|\ \ge\ \gamma N .
$$
In particular this excludes every scheme with $o(N)$ *total* advice bits, including schemes concentrating long advice on selected blocks.

**Construction.** Fix a large constant $a$ to pay the plain compiler and two bits of saving. Put $K=M/2^a$ and choose a rational $\eta>0$ small compared with $\delta 2^{-a}$. For example use $\eta=\delta 2^{-a}/100$. At large $q$, $M$ and $K$ are powers of two. In a complete block collect all predicted subsets from messages of at most $s=\lfloor\eta M\rfloor$ bits, at most $2^{s+1}$ masks. For a fixed mask having at least $\delta M/2$ ones, a uniform $K$-subset hits it in more than $\delta K/4$ places except with probability at most $\exp[-(1-\ln2)\delta K/4]$, by the elementary product moment for sampling without replacement. Summing over the masks gives a failure probability below one for all large $q$. Hence one local $K$-set works for all the short messages. Find the lexicographically first by enumerating the masks and then all choices within the block. [Product-moment proof](hitting-sampled-batches.md)

A single deterministic plain decoder receives a raw payload of $q-a$ bits. Recover $q$ from its length, and divide its integer value by $K$ to obtain the block index and a within-set ordinal. A full block and valid ordinal determine a word by the preceding search. There are at most $(N/M)K=2^{q-a}$ such pairs. First simulating the fewer than $N/2$ candidate programs through $\tau$ and forming the sorted residual list costs $N\tau\,\mathrm{poly}(q)$. On the specified block the remaining work is at most
$$
 [2^{s+1}U+2^{M+s+1}]\mathrm{poly}(q).
$$
In either setting the two costs together, including fixed polylogarithmic simulation overhead, fit $T$. A fixed decoder reads a self-delimiting $a$ before the payload and computes $\eta$ from $a,\delta$. Its header is $O(\log(a+2))$ plus a constant independent of $a$, so one $a$ covers it. Every selected word therefore has an actual program of length at most $q-2$ finishing by $T$. Its membership in the enumerated residual list guarantees that *no* such program produced it by $\tau$.

The incomplete block accounts for fewer than $M$ words. Full blocks spending more than $s$ advice bits account for at most $M\rho N/(s+1)\le\rho N/\eta$ words. Taking $\rho=\delta\eta/8$ leaves at least $3\delta N/4$ predictions on complete, short-advice blocks for large $q$. The blocks of predicted density below $\delta/2$ contribute at most $\delta N/2$. There are therefore at least $\delta N/(4M)$ full, short-advice blocks of predicted density at least $\delta/2$. Each contributes more than $\delta K/4$ distinct late words in $S$. One may take $\gamma=\delta^2 2^{-a}/16$.

## Feedback and shared advice

Taking $\delta=1/4$ gives a constant-fraction Hamming error against the actual indicator of $A_q$ on the residual list. A predictor reporting fewer than $N/4$ positives misses more than $N/4$ final hard words. A predictor reporting at least that many positives incurs the late false positives just proved. In particular the *sum of the shortest timely individual descriptions* of the true block masks, conditional on the early table and the respective block index, is $\Omega(N)$ on any fixed interpreter that meets one of the block time budgets. The full mask is computable without a running-time bound.

Now allow the predictor to receive the true previous bits as feedback as it scans each block. Any state imported across blocks is supplied as an additional binary string for the block, with a fixed routine restoring the state. Assume block replay including restoration and error correction fits one of the indicated time bounds (one may absorb a fixed polynomial factor). If the local tips and imported states have total length $o(N)$, then the predictor makes $\Omega(N)$ mistakes on the true sequence. Indeed for $e_i$ mistakes in block $i$, encode their number and the rank of their positions among its $\binom M{e_i}$ subsets. Replay the predictor, correcting its output on those positions before returning the true feedback. When $e=\sum_i e_i$, the position records on all full blocks use at most
$$
 O((N/M)\log(M+1))+\log_2\binom Ne
$$
bits, since a tuple with fixed individual counts is a subset of at most $N$ positions. Length framing for the original tips and states costs $O(1)$ per block plus a constant times their total length. Ranks can be unranked in polynomial block time. For $e/N$ sufficiently small the entire advice then fits the forbidden $\rho N$ bound and reproduces the true mask, apart from the negligible last block. This yields a positive lower bound on the error fraction.

There is a further interpretation for an addressable shared advice array with a fixed public address convention. On one block, simulate the whole predictor and cache answers to bit reads. On a first visit read the next bit of a local replay string, and on other visits use the cache. Thus only the distinct bit addresses actually probed in that block cost advice. Assume public metadata, or charge the bits required to reconstruct it, and allow polynomial bookkeeping within the block clock. An accurate prediction requires the **sum across blocks** of the numbers of distinct probed addresses to be $\Omega(N)$. If the array has $o(N)$ bits, those bits must on average be probed in an unbounded number of different blocks.

Sublinear unrestricted global advice may have exactly this reuse. For example a single $M$-bit string can specify the same arbitrary mask on every full block. For uniform such strings, at each fixed block at most $2^{M/2+1}$ admit a local plain description of length at most $M/2$, even with the early table fixed. Averaging gives a choice needing long individual descriptions on almost every block, while its shared description costs only $M=o(N)$ bits. This example concerns the limits of replacing global advice by local records. Constructing sublinear global advice for the genuine late mask, or a circuit approximating $A_q$ with the parameters needed to refute linear SAT, remains open.
