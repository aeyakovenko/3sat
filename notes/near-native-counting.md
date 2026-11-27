# Counting rare jointly plausible histories inside the native clock

**Research journal, 24 November 2026.** Let $M=2^n$, $B=M^{20}$ and let $v$ be the actual first missing native output at cutoff $B$. Under linear-time SAT one can estimate the logarithm of a projected witness count on almost $B$ bits in almost the same time as checking one witness. The two savings below are a short Toeplitz hash seed and a covering subspace specified by its generators. This allows a test of *relative* anomaly at $v$ even after conditioning on an arbitrarily rare nonlinear constraint. It also permits some mutually inconsistent outputs in jointly sampled program tables. The transfer uses **linear SAT**. The nested eliminations here give no corresponding cubic-time assertion. [Previous counting budget](multiplicity-dips.md) · [Native interpreter](native-missing-word.md) · [Shared answers under affine constraints](shared-answer-coverage.md)

## Projected approximate counts with quasilinear overhead

For fixed parameters and a label $x$, let $P(x,s)$ with $s\in\{0,1\}^H$ be given by a fixed number of Boolean quantifier blocks and a uniform deterministic RAM matrix of total bounded branch time $T$, including effective quantifier lengths. Count the primary strings $s$, regardless of the number of auxiliary witnesses for one string. Under linear SAT one can return zero for an empty set and otherwise an integer $j_x$ with

$$
2^{j_x}/4\le |\{s:P(x,s)\}|\le 8\cdot 2^{j_x}
$$

in $(H+T+2)\operatorname{polylog}(H+T+2)$ deterministic target-RAM time. Assume the bit widths and construction clocks of the fixed encodings fit this bound. A singleton empty-length string can be handled directly. This is a fine-grained use of Stockmeyer's approximate counting and the known three-quantifier quasilinear simulation of bounded-error randomness. [Stockmeyer](https://doi.org/10.1137/0214060) · [Viola, On probabilistic time versus alternating time](https://eccc.weizmann.ac.il/eccc-reports/2005/TR05-137/) · [Fixed-block elimination under linear SAT](linear-quantifiers.md)

For a threshold $0\le j\le H$, hash $s$ to $j$ bits by a random binary Toeplitz matrix plus a uniform offset. For $j\ge1$ there are $H+j-1$ diagonal bits and $j$ offset bits. On any nonzero difference vector, its first nonzero coordinate exposes one new random diagonal in each successive output row. The difference of the hashes is uniform, and the independent offset gives pairwise independent hash values on distinct inputs. To test nonemptiness of the zero bucket, guess $s$, check $P$, and universally choose one hash row to check its dot product. One row costs $O(H)$ bit operations up to encoding factors. This avoids writing a dense $j$-by-$H$ matrix. For $j=0$ the bucket is the whole set.

If the true count is $A$, the number in the bucket has mean $\mu=A/2^j$ and variance at most $\mu$. The chance of a nonempty bucket is at most $1/4$ for $\mu\le1/4$ and at least $4/5$ for $\mu\ge4$, by the second-moment inequality. Here is a direct bounded-alternation test of this constant gap. For an $r$-bit seed repeat independently $b=O(\log(r+2))$ times and take the majority. With a sufficiently large fixed constant the amplified error at each promised extreme is at most $1/[8(R+1)]$, where $R=br$. The nonemptiness predicate can first be decided by the fixed-block linear-SAT simulation; evaluating the $b$ copies preserves quasilinear overhead.

Set $d=\lceil\log_2(R+1)\rceil$. Ask whether there are $d$ shifts in $\mathbb F_2^R$ such that for every base seed, some linear combination of the shifts leads to an accepting amplified seed. At the high extreme at most half the seeds are uncovered initially. For an uncovered fraction $u$, averaging over a new shift gives an intersection of the uncovered set and its translate of expected fraction $u^2$. Adding a suitable generator to the span thus squares the uncovered fraction. After $d$ additions it is at most $2^{-2^d}<2^{-R}$. At the low extreme all $2^d\le2(R+1)$ translates together cover at most a quarter of the cube. The test has three blocks: the generators, the base seed and the coefficients. Their total length is $O(R\log(R+2))$, and the matrix evaluates only the selected combination. This is where an explicit list of $O(R)$ independent $R$-bit shifts would have exceeded the desired budget.

For $A>0$, define $j_x$ as the largest accepted $j$. The zero threshold accepts. All $j\le\lfloor\log_2 A\rfloor-2$ accept, and all $j\ge\lceil\log_2 A\rceil+2$ reject. The intermediate decisions need no monotonicity. To locate the largest, binary search on the **monotone** predicate that there exists an accepted $j$ above the queried cutoff, with the threshold choice outside the compiled test. This takes $O(\log(H+2))$ calls. An independent existential test detects $A=0$. The exponent occupies $O(\log(H+2))$ bits even when writing the count itself would cost order $H$ bits.

## A probability bound at the actual missing output

Let $E(x,s)$ select a nonempty set of jointly plausible strings and let $F(x,s)$ flag an anomaly. Both may use the bounded-quantifier verifier above. For an empty live set define the score to be zero. Otherwise put

$$
\delta_x=\Pr[F(x,s)\mid E(x,s)]
$$

under a uniform primary string. There is a constant $C$ such that, assuming linear SAT,

$$
\delta_v\le \frac{C}{M}\sum_x\delta_x
$$

for all sufficiently large $n$, provided $H,T\le B/n^a$ for a sufficiently large fixed $a$. The overhead exponents of the fixed verifiers and elimination routines must be independent of the eventual choice of $a$, or the resulting combined clock must be checked directly. No lower bound on the live probability is required.

Approximate the numerator and denominator counts separately and subtract the returned exponents. The resulting dyadic scores approximate every positive $\delta_x$ within a fixed multiplicative factor; zero is recognized exactly. To obtain the whole score table, existentially supply its $O(M\log(H+2))$ bits and universally select one entry to validate against its deterministic counting algorithm. Rank the labels by decreasing approximate score and compute a requested output bit. This batched computation costs $(H+T+M^2)\operatorname{poly}(n)$ under linear SAT, including $n$ decoded output bits and the native interpreter overhead. It can compare the exponents directly. The rank of a positive-score label is at most a fixed multiple of $\sum_x\delta_x/\delta_x$. A rank significantly smaller than $M$ by an arbitrarily growing factor would print $v$ with a name shorter than $n$ within $B$, proving the inequality. [Adaptive table verification](linear-sat-batches.md)

## Joint tables with occasional collisions

For a common live set, give every short name $p$ an output or timeout on seed $s$. Distinct names may share all of $s$. The row evaluators and the live criterion must fit the stated bounds, with a single well-defined row result for each live seed. Let $m_x(s)$ count occurrences of $x$. The event $m_x\ne1$ can be tested at fixed alternation by asking if $x$ is missing or has two distinct producers. Denote the expected number of labels with $m_x\ne1$ by $D$. Then

$$
\Pr[m_v\ne1\mid E]\le CD/M.
$$

In particular a joint model of the actual names which overrepresents an anomaly at $v$ by an unbounded factor relative to $D/M$ would refute linear SAT. If each table is injective with one omission, $D=1$. In general $D\le 2\mathbb E[\#\text{holes}]-1$, since each multiply occupied label consumes at least one surplus name and there are only $M-1$ names. An actual seed exhibiting the omission is sufficient to prove positive probability; it does not control that probability's size.

On a **free** hidden cube there are structural tests for a large anomaly probability. It suffices to supply $d$ bit-flip masks such that every translate of their span contains a seed with $m_v\ne1$. Each coset then has a fraction at least $2^{-d}$ of anomalous seeds. For example, consider the real multilinear polynomial representing $1-m_v$. If it has an inclusion-maximal nonzero monomial on $d$ coordinates, fix every variable outside that monomial arbitrarily. Its coefficient on those $d$ variables is unchanged, since all strict supersets have zero coefficient. At least one of the remaining Boolean settings is anomalous. In particular even if every other occupancy has high degree, the certificate at $v$ alone implies $d\ge n-\log_2 D-O(1)$ under linear SAT. The span condition also treats some high-degree functions: on a parity half-cube one coordinate flip suffices. The argument applies to a known free parametrization of a live domain when that parametrization samples its required law. Arbitrary conditioning may change all these fiber densities.

The threshold is attained by a selector. Give $M-1$ names the default labels $0,\ldots,M-2$. Select a uniform $n$-bit $y$. If a name has default label $y$, give it label $M-1$ instead. Every table misses exactly $y$, so $D=1$ and the anomaly probability at any particular label is $1/M$. For the actual $v$ there is a compatible assignment, all $n$ selector bits can force the anomaly from every base seed, and fewer generators cannot do so. The model illustrates the remaining gap: obtaining an advantage over this probability for the actual computation requires a correlation that the near-native verifier can establish.

An exhaustive finite check verified uniform hash differences in 577 input-pair and dimension cases, and the covering construction on all 177 at-least-half-dense subsets of the one-, two- and three-dimensional cubes. [Experiment](../audits/near_native_counting_experiment.py)
