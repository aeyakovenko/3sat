# How often can a sampled set avoid short programs?

**Research journal, 24 November 2026.** The linear-time SAT target can be approached by generating large sets that contain few easy words. The successful sets can differ on every run, contain easy words, and occur with exponentially small probability. This note gives a sufficient rate and tests two ways to attain it. I have no ordinary sampler meeting the rate on the actual programs.

## A sufficient condition for the linear target

Fix the efficient exact-prefix universal RAM interpreter used for the [deterministic coding test](near-clock-coding.md). For a power of two $q=2^k$, let $a(q)$ be the ordinary Elias gamma code of $q$. Set

$$
d=|a(q)|+\lceil\log_2(q+2)\rceil,\quad N=2^{d+1},\quad
T=2^q(q+2)^{\lceil\log_2(q+2)\rceil},\quad D=2^{\lfloor q/2\rfloor}.
$$

Use the first $N$ words in lexicographic order on $q$ bits, at sufficiently large $q$ that these all exist. Let $E_q$ consist of their indices having a program of length at most $d$ that prints the word and halts by $T$. Prefix counting gives $|E_q|\le N/2$. Here $q$ measures the output of an auxiliary computation. The input length in the SAT lower bound still measures the entire explicitly encoded Boolean formula.

Let $R$ be a fixed ordinary randomized program on $q$. It returns an explicit $N$-bit mask $S$ within $D$ steps, with the empty mask used on a timeout or malformed output. Use at most one fair bit per step. Write

$$
B(q)=\frac{N}{(1+\log_2 q)(1+\log_2\log_2(q+2))^2}.
$$

Suppose there are a constant $\delta>0$, infinitely many such $q$, and nonnegative $u_q,v_q=o(B(q))$ along those phases, with

$$
\Pr[\,|S|\ge\delta N,\quad |S\cap E_q|\le u_q\,]\ \ge\ 2^{-v_q}.
$$

**Then explicit SAT has no deterministic worst-case $O(n)$ algorithm on the target unrestricted-workspace RAM.** This criterion does not ask the sampler to recognize the successful runs. A deterministic generator with $o(B(q))$ bits of nonuniform advice producing one such mask within the clock also suffices. A randomized wrapper can guess any one advice string of length $b$ with probability at least $2^{-b-O(\log(b+2))}$ using a prefix code for its length. Reserve a constant factor of runtime for the wrapper or use the same argument for sampler time $D\,\mathrm{poly}(q)$.

## Sampling a test set without replacement

Assume linear-time SAT. First fix any $1\le K\le N$ polynomial in $q$, and choose $H$ uniformly from the $K$-subsets of $[N]$. For a fixed row $S$ put

$$
w(H,S)=2^{-|H\cap S|}(1-|S|/(2N))^{-K}.
$$

Then $\mathbb E_H w(H,S)\le1$. Give the coordinates in $S$ weight $1/2$ and the others weight $1$. Their mean is $1-|S|/(2N)$. The expected product on $H$ is at most the $K$th power of their mean. To see this, maximize the elementary symmetric sum of order $K$ on the compact box $[1/2,1]^N$ at that fixed mean. Among its maximizers choose one minimizing the sum of squares. Averaging two unequal coordinates preserves their sum and increases their product. The coefficient of the product is nonnegative, so this would give another maximizer with smaller sum of squares. The maximizer thus has equal coordinates. Equivalently one can apply Hoeffding's comparison for sampling without replacement. [Hoeffding, Theorem 4](https://doi.org/10.1080/01621459.1963.10500830)

Average now over the actual row distribution. Some $K$-set has $\Phi(H)=\mathbb E_S w(H,S)\le1$. We need to produce one usable set deterministically and sufficiently early. Use a $D$-bit prefix $\rho$ for a complete run of $R$, consuming only the part actually read. Compute $z=\lceil 2^K w(H,S)\rceil$ as a ratio of powers of integers. Since $2^{-K}\le w\le 2^K$, this integer is between $2^K w$ and $2^{K+1}w$, inclusive, and is at most $2^{2K}$. The rational arithmetic needs polynomially many bits in $q$. Count pairs $(\rho,v)$ where $v$ is a $(2K+1)$-bit nonnegative integer less than $z$. The positive count $C$ satisfies

$$
2^{D+K}\Phi(H)\le C\le2^{D+K+1}\Phi(H).
$$

Use the [projected approximate counting algorithm](near-native-counting.md) to obtain a deterministic exponent $e$ with $2^e/4\le C\le8\cdot2^e$ in $D\,\mathrm{poly}(q)$ time under linear SAT. It counts prefixes and auxiliary integers exactly once in the relation, including when many prefixes give the same output. The algorithm uses Stockmeyer's hashing method and bounded-alternation simulation. The bit size of the exponent is $O(q)$ even though $D$ is exponential in $q$. Accept $H$ when $e\le D+K+3$. This accepts every $H$ with $\Phi(H)\le1$, and every accepted $H$ satisfies $\Phi(H)\le64$. To generate one canonical accepted set, encode its sorted list, and complete its bits in lexicographic order by existentially testing a qualifying suffix. Each extension test adds one quantifier to a uniform computation of $D\,\mathrm{poly}(q)$ time. Its elimination and the polynomially many calls still take $D\,\mathrm{poly}(q)$ under linear SAT. [Bounded alternation and explicit CNF formation](linear-quantifiers.md) · [Stockmeyer](https://doi.org/10.1137/0214060) · [Viola](https://eccc.weizmann.ac.il/eccc-reports/2005/TR05-137/)

For this $H$, on the event $|S|\ge\delta N$, $|S\cap H|\le b$, we have $w(H,S)\ge2^{-b}(1-\delta/2)^{-K}$. The event has raw probability at most $64\cdot2^b(1-\delta/2)^K$. The same bound holds for intersections with $E_q$ once $H\subseteq E_q$.

## Paying for every member of the same set

A single short phase description already suffices for $K=\Omega(B(q))$. Use an Elias delta code for $k=\log_2 q$, of length $\log_2 k+2\log_2\log_2(k+2)+O(1)$, and recover $q$. Reserve a constant $c$ for the fixed program, including $R$, the supposed SAT solver and its compiler. Use the remaining $d-c-|\mathrm{delta}(k)|$ bits as an ordinal into the canonical set of size $K=2^{d-c-|\mathrm{delta}(k)|}$. All programs know $K$ and reconstruct exactly the same set before outputting their selected words. A self-delimiting encoding of the fixed choice of $c$ can be absorbed by taking $c$ large enough. These exact programs fit the time bound $T$ including native simulation. Thus $H\subseteq E_q$ and $K\ge c_R B(q)$ eventually for a constant $c_R>0$. The exponent in the probability bound is $-\Omega(B(q))$ for fixed $\delta$ and $b=o(B(q))$. This proves the sufficient condition.

One can also pool short names. Fix a sufficiently large constant $c$ and use all exact names $p$ of length at most $d-c$ which print the canonical binary representation of $q$ by $2^q$. Let $P_q$ be that set, and use

$$
K_q=\sum_{p\in P_q} 2^{d-c-|p|}.
$$

Kraft's inequality gives $K_q\le 2^{d-c}$. Each decoder starts by running its input prefix $p$, learns $q$ and retains the number of bits consumed and the virtual completion time. It checks eligibility. It then enumerates $P_q$ by simulating each binary name of length at most $d-c$ through $2^q$ steps with exact consumption and timeout checks. The total cost is $2^q\mathrm{poly}(q)$, including simulation and sorting. Partition the canonical $K_q$-set into consecutive blocks of the displayed sizes in a fixed order on $P_q$. Read $d-c-|p|$ further bits and print the indicated member of the block for $p$. On the reference machine all these names fit $d$ bits and $T$ steps. For the finite initial phases a zero value of $K_q$ carries no claim. This proves the same probability bound with $K_q$.

On infinitely many dyadic phases $K_q$ even accounts for a positive fraction of **all distinct easy $q$-bit words**, including those outside the pool. If their number is $L_q$, then $L_q2^{-d}$ is at most the unbounded prefix-machine probability of an output of length $q$. The coding theorem bounds that probability by $O(2^{-K_{\rm pref}(q)})$. Here $K_{\rm pref}$ is unbounded prefix complexity. On infinitely many $k$ there is a program for $k$ of length $K_{\rm pref}(k)+O(1)$ that runs in $\mathrm{poly}(k)$ time, by encoding a shortest program and its runtime into a new integer. The fixed conversion between $k$ and $q=2^k$ changes prefix complexity by $O(1)$ and easily prints $\mathrm{bin}(q)$ within $2^q$ on these programs. Therefore $K_q=\Omega(2^d2^{-K_{\rm pref}(q)})=\Omega(L_q)$ on these phases. This subsequence need not coincide with any independently chosen subsequence for a proposed sampler. [Construction of fast near-shortest integer names](native-coding-delays.md)

## A sharper tail when very few words may be easy

There is a second choice of test set. Let $F_s(b)$ be the exact probability that a uniform $K$-subset intersects a fixed $s$-set in at most $b$ points. Use the score

$$
W(H,S)=\sum_{\substack{0\le b\le K\\F_{|S|}(b)>0}}
\frac{\mathbf 1\{|H\cap S|\le b\}}{(b+1)(b+2)F_{|S|}(b)}.
$$

For each fixed row the mean over $H$ is at most $\sum_{b=0}^K 1/((b+1)(b+2))<1$. Compute its rational value from binomial coefficients. Even multiplying all the denominators gives polynomial bit length in $N$, since every positive $F_s(b)$ is at least $1/\binom NK$. Count $\lceil W\rceil$ pairs per seed as above, now with $O(1+\log_2\binom NK)$ auxiliary bits and threshold $e\le D+3$. An $H$ of expectation at most one qualifies since $\mathbb E\lceil W\rceil\le2$, and the qualifying expectation is at most 64. Search as before. The function $F_s(b)$ decreases weakly with $s$ by coupling nested fixed rows. With $s_0=\lceil\delta N\rceil$, the resulting canonical set gives simultaneously for all $b\in\{0,\ldots,K\}$ and $\delta\in[0,1]$

$$
\Pr[\,|S|\ge\delta N,\ |S\cap E_q|\le b\,]
 \le64(b+1)(b+2)F_{s_0}(b).
$$

When $F_{s_0}(b)=0$ the event is impossible by the pigeonhole principle. In particular missing $E_q$ entirely has probability at most $128\binom{N-s_0}{K}/\binom NK$, at most $128(1-\delta)^K$. The choice of threshold does not enter the short names.

## Two attempts to generate a violating row

**Remove all early outputs, then thin the residual list.** Enumerate all $d$-bit-or-shorter names to an early clock $t$ such that this scan fits within $D/2$. Delete all observed pool members. Its deterministic residual list has at least $N/2$ entries. Unconditionally, its first $\Omega(B(q))$ entries are late easy words. The short ordinal programs above can run the scan, take their indexed entry, print it and halt by $T$. The same reasoning gives $K_q$ entries for a sufficiently large header reserve for this particular routine. Independently retaining each residual entry with fixed probability $p>0$ samples a dense set. The number of these certified easy entries retained is binomial, so the probability of taking $o(B(q))$ of them is at most $\exp(-\Omega(B(q)))$. This fails the sufficient rate for real program outputs. It also applies if a deterministic preliminary scan certifies additional exclusions while leaving at least $K_q$ eligible entries and fitting the same clock.

**Give the sampler advice about future completions.** For a set of $L=|E_q|\ge1$ easy indices, split $[N]$ into $M$ equal contiguous blocks, where $M$ is the least power of two at least $2L$. Then $M\le N$, $M<4L$ and at most half the blocks meet $E_q$. One advice bit per block marks the occupied ones. The complement is a mask of density at least one half containing zero easy indices, generable in $\mathrm{poly}(q)$ time. Guessing this table costs $O(L+\log N)$ bits. On the subsequence where $K_q$ is comparable to the total number of easy words, this attains the linear order in $K_q$ for the cost. It leaves the required sublinear advice cost unproved. On an arbitrary universe, for a fixed density-$\delta$ mask and a uniformly random $L$-set the probability of missing it is at most $(1-\delta)^L$. A union bound over all advice strings of length $b$ then requires $b\ge L\log_2(1/(1-\delta))$ to guarantee that *every* $L$-set can be avoided by some mask in that family. Beating this order for the actual $E_q$ requires exploiting its origin in computation. [Classical approximate membership representations](https://research.ibm.com/publications/exact-and-approximate-membership-testers)

The argument also clarifies what changes with the sampler's runtime. For a fixed ordinary sampler with a uniformly enforceable clock $2^{o(q)}$, a polynomial-time SAT algorithm of **any** degree would suffice to construct the test set by $T$. The counting and search tests use only a fixed number of quantifier blocks on instances of length $(2^{o(q)}+\mathrm{poly}(q))^{O(1)}$. Under polynomial-time SAT each block can be eliminated with fixed polynomial overhead, and the result is still $2^{o(q)}$. The phase-name enumeration separately fits $2^q\mathrm{poly}(q)$. For the explicit $D=2^{q/2}$ clock the linear hypothesis in the main argument controls the overhead. The journal has no violating sampler in either time regime.

[Lean verification of the product moment, count qualification and integer bounds](../lean/BatchHitPotential.lean) · [Finite experiment on correlated rows with different sizes](../audits/batch_hit_experiment.py)
