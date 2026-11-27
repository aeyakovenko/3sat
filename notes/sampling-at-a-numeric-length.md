# Encoding a sampling deadline in the output length without receiving it as input

**Research journal, 24 November 2026.** Let $S$ be any fixed ordinary fair-stream sampler. Suppose it publishes a particular short word $y$ by time $t$ with probability $p>0$. There is one other ordinary sampler, independent of $y,t,p$, that publishes the binary representation of an integer $n$ encoding $y$ with probability $\Omega(p)$ by time $O(n)$. The integer satisfies
$$
 n\le (t/p)\,\mathrm{poly}(\log(2t)+\log(1/p)).
$$
The sampler receives neither the deadline nor the probability. If $p$ is inverse-polylogarithmic or larger, the numeric length $n$ is at most $t\,\mathrm{polylog}(t)$. This gives a transfer from arbitrary deadlines to an interpreter's own numeric test in the high-probability case.

Take $t=2^q$, $q\ge\max(1,|y|)$. Other integer deadlines can be rounded up to the next dyadic time. In that case use the probability at the rounded deadline, which is at least the original $p$. Write $F_i=\Pr[S\text{ publishes }y\text{ by }2^i]$ for $i\ge1$ and put $F_0=0$. The first bin includes all publications by time two. All the constants below are independent of the word, its probability and the deadline.

## Assigning mass to a common epoch

First run $S$ on fresh bits. Retain the word it publishes and the first epoch $j$ including its actual publication time. The new sampler has two equiprobable branches. The first branch encodes $y$ at epoch $j$ directly. Thus if $F_j-F_{j-1}\ge p/128$ for any $j\le q$, one epoch already carries enough probability.

In the other case at least $3p/128$ of unconditional source probability comes from epochs $j\le q$ with
$$
 p/32\le F_j\le p/16.
$$
Indeed, before the first epoch reaching $p/32$ the cumulative probability is smaller than $p/32$. Immediately before the first epoch exceeding $p/16$ it is at least $p/16-p/128$. All jumps between those endpoints land inside the band. The first crossing of the upper endpoint exists since $F_q=p$.

The second branch estimates $F_j$ from independent new runs of $S$ through time $2^j$, stopping after $K=2048$ successes for this same $y$. Let $L$ be the number of trials and set $\widehat F=K/L$. The sum of $K$ independent geometric waiting times has mean $K/F_j$ and variance at most $K/F_j^2$. With probability at least $0.95$, $L$ is within ten percent of its mean. On that event the procedure used $O(1/F_j)$ trials and $\widehat F/F_j$ lies between $1/1.1$ and $1/0.9$.

Round $3\widehat F$ up to the next power of two $\theta$. The machine may abandon values above one. On a successful estimate for a band epoch we have
$$
 2F_j<\theta<8F_j,\qquad p/16<\theta\le p/2.
$$
Only a constant number of dyadic values can occur in this range. Hence one $\theta=2^{-d}$ is selected on a set of raw streams of probability $\Omega(p)$, counting the branch probability and restricting to the successful estimates above. For each such stream the cost so far is at most $2^j 2^d\,\mathrm{poly}(j+d+|y|+2)$ native steps. Logarithms in the running-time bound pay for counters and bounded simulation.

Simply retaining the source timestamp can lose an unbounded fraction even on a fixed ordinary sampler. Read a gamma code for $k$, choose uniform $i$ in $[2^k,2^{k+1})$ from $k$ fresh bits, wait for order $2^i$ steps, then publish the binary word for $k$. A depth-$i$ binary-tree traversal realizes the wait with uniform upper and lower constant factors. At a deadline covering the entire phase its publication probability is the gamma-code mass $p_k=2^{-O(\log(k+2))}$, well above an inverse polylogarithm of that deadline. Each individual dyadic completion bin carries only $O(p_k/2^k)$ because its time interval admits only a bounded number of the exponents $i$. This is a failure of the direct timestamp rule on actual runs.

## A moving threshold fixes the next epoch

Here $\theta$ is known to the running machine. Both $p$ and $q$ are still unknown. At epoch $i\ge1$ set
$$
 g_i=\theta(1+1/(i+1)),\qquad e_i=\theta/(16(i+2)^2).
$$
Let $r$ be the first $i$ with $F_i\ge g_i$. It is a common integer depending only on $y,\theta$ and the source. For the selected runs $j<r\le q$, since $F_j<\theta$ and $g_q\le 3\theta/2<p$. The ordinary threshold $F_i\ge\theta$ can sit arbitrarily close to equality for many successive epochs. The decrement $g_i-g_{i+1}=\theta/((i+1)(i+2))$ exceeds $e_i$ and $e_{i+1}$.

Scan epochs from one. At each epoch test whether the sample proportion is at least $g_i$ using $\lceil C(i+2)^6/\theta\rceil$ independent bounded trials, with fixed large $C$. Return the first accepting epoch $\widehat r$. With probability at least $0.99$, all epoch tests reject when $F_i\le g_i-e_i$ and accept when $F_i\ge g_i+e_i$. To see this apply the Bernoulli tail bound at the two boundary probabilities $g_i\pm e_i$, using variance scale $O(\theta)$ there. Stochastic monotonicity gives the same one-sided guarantees at all the more distant probabilities. The failure probability per epoch is at most $2\exp(-cC(i+2)^2)$ for an absolute $c>0$, which is summable. The argument here only needs the selected $\theta\le1/2$, so the boundaries are valid probabilities. On the simultaneous success event the scan cannot return before $r-1$ because $F_{r-1}<g_{r-1}$, and must return by $r+1$ because $F_r\ge g_r$. One can couple the scan to independent trials for the unreached epochs. All the work performed by the stop fits $2^{\widehat r} 2^d\,\mathrm{poly}(\widehat r+d+|y|+2)$ time. In particular $\widehat r\ge j$. For the chosen $\theta$ at least one of these three possible return values therefore retains $\Omega(p)$ probability.

Put $m=\max(1,|y|,\widehat r)$ and choose the encoded integer
$$
 n=2^{m+d+C'\lceil\log_2(m+d+2)\rceil+C'}+r(y),
 \qquad r(y)=2^{|y|}-1+\mathrm{val}(y).
$$
The empty word has rank zero. In the first branch use $\widehat r=j$ and $d=0$. In either branch clearing the leading bit recovers the length-lexicographic rank and hence $y$. The selected runs finish by $O(n)$ for sufficiently large fixed $C'$. This includes writing the explicit binary representation. The wrapper can read $C'$ from a fixed header, so the physical simulation exponent on an efficient reference can be fixed before choosing $C'$. In the second branch $2^d=O(1/p)$ and $\widehat r\le q+1$. These inequalities prove the upper bound on $n$. Long or failing runs on other fair streams impose no condition on the claimed mass.

## Consequence for a proposed SAT attack

Assume just the [own numeric comparison](dilated-program-mass.md) holds on one efficient literal prefix interpreter $V$. Compile the sampler into $V$ with a fixed header and choose the padding exponent to cover its simulation overhead. For the integer above, the time-discounted mass $B^V_n(\mathrm{bin}(n))$ is at least a constant times $p$. The assumed comparison gives a deterministic $V$ program of single-program weight $\Omega(p)$ at time allowance $n\,\mathrm{polylog}(n)$. Project its integer to $y$ on any efficient literal reference. This projection costs a constant number of extra bits. Its source program runs in at most $n\,\mathrm{polylog}(n)/\Omega(p)$ steps, so the projection's multiplicative time overhead is polynomial in $q+b+2$, with $b=\lceil-\log_2 p\rceil$. Equivalently the best single-program weight for $y$ at allowance $t2^b(q+b+2)^{O(1)}$ is at least $\Omega(p)$. In particular one deterministic name has length at most $b+O(1)$ and physical running time at most $t2^{2b}(q+b+2)^{O(1)}$.

For each fixed $a$, if $p\ge(q+2)^{-a}$ this name finishes in $t\,\mathrm{polylog}(t)$ time. Thus a single sampler violating the usual *hard-deadline* coding guarantee on these probabilities would already violate the *soft*, numeric comparison on every efficient reference. This extends the [clock-recovery argument](dilated-program-mass.md) to external deadlines throughout this probability regime. The unconditional result here is the probability transfer between two ordinary samplers. Deriving a SAT lower bound still requires a violation of one of the coding guarantees. Related work gives resource-bounded codes with randomized representations; priority for the numeric-clock transfer is unestablished. [Lu, Oliveira and Zimand](https://arxiv.org/abs/2204.08312)

## Equivalence when only frequently sampled words are tested

The numeric comparison need only hold at **high mass relative to the numeric length being tested**. More precisely, the following are equivalent without any hypothesis on SAT.

1. On one fixed efficient reference $V$, for every positive integer $k$ there are constants $e,c>0$ such that $A^V_{n(2+\log_2 n)^e}(\mathrm{bin}(n))\ge c B^V_n(\mathrm{bin}(n))$ for all $n\ge2$ with $B^V_n(\mathrm{bin}(n))\ge(2+\log_2 n)^{-k}$.
2. For every fixed source $S$, efficient target reference $U$ and positive integer $a$, there are constants $f,b_0$ such that if $P^S_{2^q}(y)=p\ge(q+2)^{-a}$ and $|y|\le q$, then $y$ has a deterministic $U$ name of at most $\lceil-\log_2 p\rceil+b_0$ bits which finishes by $2^q(q+2)^f$.

For $1\Rightarrow2$, fix $a$ in the sampler above. The second branch already obtains $d$ within a fixed additive constant of $-\log_2 p$ on the selected runs. Modify the first branch to estimate $F_j$ by the same geometric trial procedure and use $d=\lceil-\log_2\widehat F\rceil$, retaining the exact timestamp $j$. On a jump of size at least $p/128$, $p/128\le F_j\le p$. Thus, after discarding the low-probability estimation failures and choosing one of a bounded number of dyadic estimates, this branch also has $d=-\log_2 p+O(1)$ on a set of raw probability $\Omega(p)$. The extra time fits the earlier bound with its $2^d$ factor.

In the integer encoding require in addition $m\ge2^{\lfloor d/(a+1)\rfloor}$, by increasing $m$ to the maximum with this value. On our successful runs this lower bound is $O_a((q+2)^{a/(a+1)})$, hence is at most $q$ at all sufficiently large $q$. For the resulting numeric length we have both $n\le 2^q\,\mathrm{poly}_a(q+2)$ and $2^{-d}\ge c_a(2+\log_2 n)^{-(a+1)}$. The latter follows by raising the lower bound on $m$ to the power $a+1$. The generated binary word takes $O(m+d+\log(m+d+2))$ bits to write, which also fits within its numeric clock. We have $B_n^V(\mathrm{bin}(n))\ge c'p\ge c''2^{-d}$ after compilation. Thus, for all sufficiently large $n$, assertion 1 applies with $k=a+2$. Finitely many smaller numeric lengths encode finitely many words, which have fixed literal programs and can be absorbed in the constants. Projection gives the length bound. Because $1/p\le(q+2)^a$, even the latest permissible projected computation finishes by $2^q\,\mathrm{poly}_a(q+2)$.

For $2\Rightarrow1$, use $S=U=V$. Given $B=B_n^V(\mathrm{bin}(n))\ge(2+\log_2 n)^{-k}$, truncate at the next dyadic time $s$ above $4n(2+\log_2 n)^{k+1}$. The omitted physical-time tail contributes at most $n/s\le B/4$. Hence $P_s^V(\mathrm{bin}(n))\ge3B/4$. This word meets the length condition and, for all sufficiently large $n$, the probability condition in assertion 2 at exponent $k+2$. Its resulting length is at most $-\log_2 B+O(1)$ and its time at most $n\,\mathrm{poly}_k(2+\log_2 n)$. This yields assertion 1.

In particular a high-mass hard-deadline counterexample would force numeric violations in precisely the inverse-polylogarithmic probability range where the [block search](dilated-program-mass.md) takes nearly linear time for each fixed cost and clock exponent. The equivalence supplies no such counterexample. If $|y|=O(\log(q+2))$, literal descriptions handle the complementary small probabilities, so assertion 2 for all $a$ also gives nearby-deadline coding at these output lengths for every positive $p$.

Lean verifies the band-mass and crossing-index inequalities on finite sequences, including a sentinel for a missing crossing. The finite experiment checked 108,240 crossing cases. The probability and machine-time analyses remain manuscript arguments. [Lean verification](../lean/MovingThreshold.lean) · [Finite checks and sharp examples](../audits/moving_threshold_experiment.py)
