# Can isolation concentrate a dense set of hard truth tables on one output?

**Research journal, 24 November 2026.** At a fixed output length $m$, let $H$ contain the words omitted by every exact prefix program of at most $d$ bits on the deterministic reference at a later deadline $T$. Kraft's inequality gives $G=|H|\ge 2^m-2^d$. The [coding test](near-clock-coding.md) needs substantial probability on one member. I tested explicit pools and also gave the sampler a stronger operation that instantly returns the sole hard word in an implicit random bucket, whenever one exists.

## Isolation probability for one specified word

Fix $y\in H$ and $G\ge2$. Let the inclusion indicators of the $G$ words in one bucket be pairwise independent, each with marginal $\delta$. The probability that $y$ is the sole hard member is at most
$$
 \min\left\{\delta,\frac{1-\delta}{1+(G-2)\delta}\right\}
 \ \le\ \frac1{1+\sqrt{G-1}}.
$$
Indeed the number $Z$ of *other* hard members has mean $u=(G-1)\delta$ and variance $(G-1)\delta(1-\delta)$. From $(\mathbb E Z)^2\le\Pr[Z>0]\,\mathbb E Z^2$ we obtain the displayed bound on $\Pr[Z=0]$ for $\delta>0$. Isolation also requires inclusion of $y$. The two bounds cross at $\delta=1/(1+\sqrt{G-1})$. The zero marginal is immediate.

For three-wise independent membership, condition on $y$ being included. The other indicators still have the same means and are pairwise independent. Multiplying their zero-count bound by $\delta$ gives
$$
 \Pr[y\text{ is the sole hard member}]
 \le\frac{\delta(1-\delta)}{1+(G-2)\delta}
 \le\frac1{(1+\sqrt{G-1})^2}.
$$
The final inequality follows after clearing denominators from the nonnegativity of $(1-(1+\sqrt{G-1})\delta)^2$. With fully independent inclusions the exact probability is $\delta(1-\delta)^{G-1}$.

### A tighter bound and the exact integer extremum

Write $N=G-1$, $B=1[y\text{ is included}]$, $\mu=N\delta$ and $\sigma^2=N\delta(1-\delta)$. Take $0<\delta<1$. Pairwise independence forces the conditional mean of $Z$ to equal $\mu$ in both classes $B=0,1$. The variance decomposition gives $\operatorname{Var}(Z\mid B=1)\le\sigma^2/\delta$. Applying the same second-moment inequality *inside* this class gives the stronger bound

$$
\Pr[B=1,Z=0]\le\frac{\delta(1-\delta)}{1-\delta+N\delta^2}
\le\frac{1}{1+2\sqrt N}.
$$

For the last step the reciprocal of the middle expression is $1/\delta+N\delta/(1-\delta)=1+(1-\delta)/\delta+N\delta/(1-\delta)$. The last two terms have product $N$.

The optimum for *each* fixed $N,\delta$ can be obtained by accounting for the integer number of competing words. For $N=1$ it is $\delta(1-\delta)$. For $N\ge2$ put

$$
\nu=(\mu-\lfloor\mu\rfloor)(1-\mu+\lfloor\mu\rfloor),\qquad
V=\min\{\mu(N-\mu),\,(\sigma^2-(1-\delta)\nu)/\delta\},
\qquad S=\mu^2+V.
$$

Set $j=\min(N-1,\lfloor S/\mu\rfloor)$. The exact maximum designated singleton probability is

$$
\boxed{\quad \delta\left(1-\frac{(2j+1)\mu-S}{j(j+1)}\right).\quad}
$$

Indeed an integer-valued variable in $[0,N]$ with mean $\mu$ has minimum variance $\nu$ by the quadratic with roots $\lfloor\mu\rfloor,\lfloor\mu\rfloor+1$, and maximum variance $\mu(N-\mu)$ by $Z^2\le NZ$. Mixtures of the adjacent-integer law and the endpoint law realize the entire interval between them. Thus $V$ is the largest possible conditional variance at $B=1$; the required remaining variance at $B=0$ lies in this interval since $\nu\le\sigma^2\le V$. We have $1\le S/\mu\le N$.

On integer arguments $z\in[0,N]$ the quadratic $(z-j)(z-j-1)/(j(j+1))$ majorizes $1[z=0]$. Taking its expectation gives the boxed upper bound since the conditional second moment is at most $S$. To attain it use probabilities $((j+1)\mu-S)/j$ and $(S-j\mu)/(j+1)$ at $j$ and $j+1$ given $B=1$, putting the rest at zero. Both displayed probabilities are nonnegative by the choice of $j$. Their sum is at most one because the quadratic upper bound on the zero probability is nonnegative for any count law with mean $\mu$ and second moment $S$, which exists by the variance interval. For $B=0$ take the interpolated count law with the remaining variance. In each class, conditional on $Z$, select a uniform $Z$-subset of the $N$ competitors. The common conditional means give independence from $B$. The unconditional factorial moment $\mathbb E[Z(Z-1)]=N(N-1)\delta^2$ gives independence for each distinct competitor pair by symmetry. Thus the upper bound is attained by an actual bucket distribution. Related work gives tight moment bounds for sums of Bernoulli indicators under pairwise independence. Historical priority of the designated-singleton formula is unverified. [Ramachandra and Natarajan](https://arxiv.org/abs/2006.00516)

For $N=l^2$, $\delta=1/l$ and integer $l\ge2$, the construction simplifies. Without the distinguished item choose exactly $l$ competitors. With it, choose $2l-1$ competitors with probability $l/(2l-1)$ and none otherwise. This gives designated singleton probability $(l-1)/(l(2l-1))$, asymptotic to $1/(2\sqrt N)$. The leading constant in the uniform upper bound is therefore sharp.

### A finite-field construction favoring the same word in every singleton

Take a prime $r\ge5$, a subset $B\subseteq\mathbb F_r$ of size $\lfloor r/2\rfloor$, and $G=1+r|B|$ items. A bucket uses three independent uniform field values $X,Y,Z$. The distinguished item belongs when $X=0$. Item $(a,b)\in\mathbb F_r\times B$ belongs when $Z+aX+bY=0$. Any two of these nonproportional linear forms are jointly uniform, so distinct indicators are pairwise independent with marginal $1/r$.

When $X\ne0$ exactly one $a$ occurs for each $b$, hence at least two items occur. When $X=0$, the distinguished item is the sole member precisely if $Y\ne0$ and $-Z/Y\notin B$, or $Y=0$ and $Z\ne0$. Thus every singleton consists of the distinguished item, with total probability
$$
 \frac{(r-1)(r-|B|+1)}{r^3}=\Theta(G^{-1/2}).
$$
Independent repetitions concentrate on that one item in $O(\sqrt G)$ trials. Exhaustive enumeration checked all singleton identities and all one- and two-item marginal counts at $r=5,7,11$. It found respectively 16 of 125, 30 of 343, and 70 of 1,331 seeds giving singletons. This finite construction designates the favored item explicitly. It supplies no ordinary algorithm to make the favored item incompressible.

## What fits the sampler's clock?

With $A$ attempted buckets, sum the relevant single-bucket upper bounds. Dependence across a fixed list of buckets is allowed. For adaptive attempts the sufficient hypothesis is the same within-bucket independence and equal marginals conditional on the transcript before each attempt, with $\delta$ allowed to change. The output must come from a singleton. With $d<m$ and $G\ge 2^{m-1}$, a contribution $p$ to one word on these attempts requires $A=\Omega(p\,2^{m/2})$ for pairwise independence and $A=\Omega(p\,2^m)$ for three-wise independence. This grants unit cost even for testing uniqueness within the actual set $H$ and extracting its member. In $2^q$ steps and at $p\ge(q+2)^{-a}$ for a fixed $a$, such pairwise isolation requires $m\le 2q+2a\log_2(q+2)+O(1)$. Three-wise isolation requires $m\le q+a\log_2(q+2)+O(1)$.

For a pool of $A$ explicitly generated candidates each uniform on the $m$-bit universe, any rule publishing one of them gives $\Pr[\text{publish }y]\le A/2^m$, even with arbitrary dependence, arbitrary tie-breaking and a perfect hardness test. This includes fixed pairwise-independent candidate pools. A sampler that synthesizes a fresh word from the pool need not satisfy that inequality. The bounds apply to the contribution from the stated isolation or pool procedure.

### Ordinary affine hash buckets have a stronger obstruction

The complement of the hard set has only $L\le2^d$ easy words in the universe of size $U=2^m$. This yields an exact bound in a common hashing model. Suppose the bucket law is invariant under a group that maps any ordered pair of distinct words to any other such pair. In particular this holds for $B=\{x:Ax=b\}$ with a uniformly random binary matrix and an independent uniform right-hand side of any fixed row count. Conditioning on bucket size $s$ preserves the invariance. Each word then belongs with probability $s/U$. Given that the specified hard $y$ belongs, each other word belongs with probability $(s-1)/(U-1)$ by symmetry and the fixed size.

If $s\ge2$, isolating $y$ needs all $s-1$ other words to be easy. This is impossible for $s>L+1$. Otherwise the expected number of easy words conditional on $y$ belonging is $L(s-1)/(U-1)$, so the chance that all $s-1$ are easy is at most $L/(U-1)$. If $s=1$, the chance of isolating $y$ is exactly $1/U$. Averaging over sizes gives

$$
\Pr[B\cap H=\{y\}]
\le \max\left\{\frac1U,\frac{L(L+1)}{U(U-1)}\right\}.
$$

In particular, when $L(L+1)\le U-1$, even an oracle that instantly extracts the sole hard word from the usual affine hash bucket selects any particular hard word with probability **at most $2^{-m}$ per trial**. The uniform random singleton attains this bound in the symmetric class. Achieving total contribution $p$ needs at least $p\,2^m$ attempts if the conditional symmetry holds at each attempt. This applies at $d=O(\log q)$ and $m=q$ for all sufficiently large $q$. It explains why the asymmetric finite-field example above behaves differently despite its pairwise independence. Even invariance just under translations gives the weaker $(L+1)/U$ bound since possible successful sizes are at most $L+1$ and membership is uniform given size. Valiant and Vazirani use hashing to isolate a solution; the target here is repeated production of one specified word. [Valiant and Vazirani](https://ics.uci.edu/~vazirani/ValVaz.pdf)

Without symmetry, pairwise-independent membership still bounds the chance that $y$ and any easy competitor are included together by $L\delta^2$. If the probability that $y$ is the sole *hard* word is $p$, the probability that the raw bucket itself equals $\{y\}$ is at least $p-L\delta^2$. In regimes where $L\delta^2$ is much smaller than $p$, most such concentration is already present in the choice of buckets.

## A randomized test on a polynomial-size initial segment would suffice

Take $q$ a power of two, $m=q$ truth-table bits, and $h(q)$ the ordinary prefix gamma code of $q$. Set $d(q)=|h(q)|+\lceil\log_2(q+2)\rceil$ and $T(q)=2^q(q+2)^{\lceil\log_2(q+2)\rceil}$. Define $H_q$ using these $d(q),T(q)$. Among the first $2^{d(q)}+1$ words of length $q$ there is a member of $H_q$, for all large $q$. Consider a single uniform tester receiving $q$ and the candidate. Suppose that on each word of this initial segment at infinitely many such $q$, it decides membership in $H_q$ with error at most $1/3$ in time $D(q)$. A known cutoff can enforce this clock. Write $L=2^{d(q)}+1=O(q^3)$.

A fixed source reads $h(q)$ from fair bits and tests these $L$ words in order. Amplify each test independently to error at most $1/(10L)$ with $O(\log L)$ repetitions. With conditional probability at least $0.9$ the source publishes the first genuine member, the same word on those runs. Its scan costs $O(L\log L\,(D(q)+q))$ native steps up to fixed simulation overhead polynomial in $\log(D(q)+2)+q$. If this fits $2^q$ (for instance $D(q)\le2^{q/2}$), that word has ordinary mass at least $0.9\,2^{-|h(q)|}$ by $2^q$. Its shortest program through $T(q)$ exceeds $d(q)$. Both the bit excess and the allowed clock exponent increase without bound. Hence such an ordinary randomized tester, even just on the initial segment, would refute unrestricted linear-time SAT by the coding implication.

A deterministic tester with the same correctness and clock is already excluded at all sufficiently large such $q$. The deterministic scan fits $T(q)$ after compilation and its entire program is $h(q)$ plus a fixed header, contradicting the definition of the word it prints. The unconditional pseudodeterministic construction of Chen, Lu, Oliveira, Ren and Santhanam assumes a polynomial-time decidable dense property. Counting shows density here, while the required ordinary randomized membership algorithm remains missing. Direct simulation of all short programs through the defining clock uses order $2^{d(q)}T(q)$ simulation slots in the worst-case bounded scan. The finite isolation calculations establish a limitation of these sampling strategies. No general SAT lower bound or priority claim follows. [Chen et al.](https://arxiv.org/abs/2305.15140) · [Korten and Santhanam on constructing time-bounded incompressible strings](https://doi.org/10.4230/LIPIcs.CCC.2025.35)

The candidate list can be much smaller if only sparse lengths are tested. Put $q_1=2$, $q_{j+1}=2^{q_j}$, and give the source a self-delimiting integer code $h(j)$ of length at most $\log_2 j+2\log_2\log_2(j+2)+O(1)$. At phase $j$ set $m=q_j$, $d_j=|h(j)|+\lceil\log_2\log_2(j+4)\rceil$, and the hardness cutoff $T_j=2^{q_j}(q_j+2)^j$. Specifying this phase requires no $q_j$-bit header. The construction of the integer $q_j$ by repeated exponentiation, and even writing a full candidate of length $q_j$, fit well within the scanning clock. There are at most $2^{d_j}$ easy words. The first $2^{d_j}+1=O(j(\log(j+2))^3)$ words therefore suffice. A tester at time $2^{q_j/2}$ correct with bounded error across this small segment on infinitely many $j$ would give the same contradiction. The sampler's mass is at least $0.9\cdot2^{-|h(j)|}$, the program-length excess grows as $\log\log j$, and the excluded clock exponent grows as $j$. Since $j$ grows as the iterated logarithm of $q_j$, the task can be made narrow in the number of candidates. The membership test must still account for programs running all the way to $T_j$.

**An unconditional restriction on the correct random tapes of a tester.** Fix any proposed randomized tester with clock $D=2^{\lfloor q/2\rfloor}$. At every sufficiently large eligible $q$ there is a candidate on the initial segment for which the tapes giving the correct membership bit admit no fractional packing of successful subcubes of width $\lfloor q/4\rfloor$ having fair mass at least $3/5$. The assertion applies both to the power-of-two phases and to the smaller list on the tower phases above. It allows the packing to depend arbitrarily on the candidate and the correct bit.

Indeed apply one finite almost-independent tape generator to the tester's $D$ coin positions, with width $k=\lfloor q/4\rfloor$ and relative error at most $1/10$ on every cube of that width or less. In the field construction take the position-label field degree $h$ to be a power of two between $\log_2 D$ and $2\log_2 D$, and the evaluation field degree $\ell=k+\lceil\log_2(kh+1)\rceil+4$. Use this *exact* $\ell$ to avoid rounding the seed exponent up. One can enumerate the monic degree-$\ell$ polynomials until finding an irreducible, in $2^\ell\mathrm{poly}(\ell)$ time: use the standard finite-field irreducibility test by repeated squaring and polynomial gcds. For instance test $X^{2^\ell}=X$ modulo the proposed polynomial and coprimality with $X^{2^{\ell/r}}-X$ for each prime divisor $r$ of $\ell$. The label field can use the quadratic tower. Each bit then costs $\mathrm{poly}(q)$ steps and the seed space size is $2^{2\ell}=2^{2k}\mathrm{poly}(q)$. [Construction and fractional packing bound](cube-tape-coding.md)

If every candidate had the asserted packing, the correct bit would have seeded probability at least $(9/10)(3/5)>1/2$ on each query. Exhausting these seeds and taking the majority, then scanning the entire segment, would deterministically find a hard word in time $2^{2k}D\,\mathrm{poly}(q)\le2^q\mathrm{poly}(q)$. The header and fixed algorithm fit the forbidden name budget, and the time fits the later defining cutoff. This contradiction identifies at least one candidate with the stated obstruction. It does not exclude a tester using less structured correct tapes.

Lean verifies the finite second-moment inequalities from their moment or balance hypotheses and checks every singleton and pair marginal in the three prime-field examples. As an independent numerical check, a full joint-distribution linear program agreed with the boxed formula for all 216 pairs with $1\le N\le8$ and distinct interior rational marginals of denominator at most nine. Enumeration of all affine subspaces by dimension through four bits also checked the symmetric bound in 13,288 combinations of bucket size and easy-word set. The exact optimization and its attainment are manuscript proofs. [Finite isolation checks in Lean](../lean/SingletonIsolation.lean) · [Full-distribution optimization experiment](../audits/singleton_extremum_experiment.py)
