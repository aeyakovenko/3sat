# How much extra time buys a constant-bit comparison with the full program mass?

**Research journal, 24 November 2026.** A test for the linear SAT target now compares a sum over *all* running times with a single deterministic program, to a constant number of bits. It gives that program a polylogarithmically longer starting time allowance. For outputs with appreciable mass, a randomized search for violations on an entire block of numeric lengths takes nearly linear time in the block's starting length. I have no sequence of violations on a fixed ordinary interpreter.

## One deadline selected from a distribution of completion times

Let a fixed stream sampler publish at most once. For one output word and baseline time $t\ge2$, give a fair stream the value $U=\min(1,t/\tau)$ if it publishes that word at time $\tau$, and zero otherwise. Times are at least one. Set $B=\mathbb E U$, $F(u)=\Pr[U\ge u]$ for $0<u\le1$. For $\lambda\ge1$ put
$$
 h=\sup_{0<u\le1} F(u)\min(1,\lambda u).
$$
Here $F(u)$ is the ordinary probability of the word by time $t/u$. If $B>0$, then
$$
 B\ \le\ h\left(1+\frac{\ln(1/h)}{\lambda}\right).
$$
Indeed, integrate $F$ from zero to one. On the three intervals cut at $h/\lambda$ and $1/\lambda$, its upper bounds are respectively $1$, $h/(\lambda u)$ and $h$. This proves the inequality, including $h=1$. The natural logarithm occurs only from the integral. The bound is attained for abstract clock distributions: put mass $h$ at $U=1$ and density $h/(\lambda u^2)$ on $(h/\lambda,1/\lambda)$.

Write $b=\lceil-\log_2 B\rceil$. With $\lambda=b+2$ we have $h\ge B/2$. Otherwise, monotonicity of $z(1+\ln(1/z)/\lambda)$ on $(0,1]$ gives $B<(B/2)(1+\ln(2/B)/\lambda)\le B$. Choose a threshold with product at least $B/3$. Its deadline $s=t/u$ obeys $t\le s\le3\lambda t/B$ since $F(u)\le1$. The selection is existential and does not require the program that ultimately prints the word to receive this threshold.

There is an ordinary sampler showing why the clock multiplier depends on $b$ in this threshold argument. On a self-delimiting gamma code for $d\ge1$, draw $d$ more bits, interpret them as a uniform $i\in\{1,\ldots,2^d\}$, wait for order $2^d i$ native steps, then publish the binary expansion of $d$. The wait can be a counted loop, with a warmup of $O(2^d)$ to reach word width sufficient for its counter. At baseline $t=2^d$, actual publication times lie between constant multiples of $ti$, uniformly in $d,i$. Let $\beta_d$ be the probability of the gamma code. The total discounted mass is $\Theta(\beta_d H_{2^d}/2^d)$, where $H_m=\sum_{j=1}^m1/j$. By any deadline $s\ge t$, the published fraction is at most $O(\beta_d\min(1,s/(t2^d)))$. Thus $h=O(\beta_d\lambda/2^d)$ and $b=\Theta(d)$. Every $\lambda=o(b)$ loses an unbounded factor on this single sampler. Its output has a short literal description. The example proves sharpness for selecting a single probability deadline from a time distribution.

## A constant-bit consequence of linear SAT

For an efficient literal prefix reference $V$, define the largest single-program weight at allowance $v$ by
$$
 A_v(y)=\sup_{p:V(p)=y}2^{-|p|}\min(1,v/\tau_V(p)).
$$
With $v$ a power of two, $-\log_2 A_v(y)$ differs by less than one from the [integer soft cost](unary-speed-gap.md). Let $B_t^S(y)$ denote the expectation $B$ above for a fixed ordinary sampler $S$. Suppose linear-time SAT holds on the model in the [research goal](../README.md). Then there are constants $c>0$ and $e$ depending only on $S,V$ such that for every $t\ge2$ and $|y|\le\lceil\log_2 t\rceil$,
$$
 A_{t(2+\lceil\log_2 t\rceil)^e}(y)\ \ge\ c B_t^S(y).
$$
In particular, this applies to $S=V$ and $y=\mathrm{bin}(n)$ with $t=2n$. A violation for every fixed $e,c$ on that case would exclude linear SAT. Using $t=n$ changes the two allowances and the masses only by fixed factors, and the length discrepancy of one bit is harmless.

To prove the bound, take $q=\lceil\log_2 t\rceil$ and first suppose $0<B$ and $b\le2q+4$. Use the selected threshold and round its deadline up, also increasing it to $2^q$ if needed for the output-length condition. This gives a deadline $s'$ of at most $2s+1$ with $\log_2(s'+2)=O(q+1)$. The [near-deadline coding implication](near-clock-coding.md) gives a prefix program of length at most $-\log_2 F(u)+O(1)$ which prints $y$ by $s'(2+\log_2 s')^{O(1)}$. With allowance $v=t\lambda(q+2)^{C}$ for a sufficiently large fixed $C$, its time factor $\min(1,v/\tau_V(p))$ is at least a constant times $\min(1,\lambda u)$. Multiplying gives the claimed constant fraction of $B$. Absorb $\lambda\le2q+6$ into the exponent. For $b>2q+4$, a literal program for $y$ takes at most $q+O(\log(q+2))$ bits and runs within the allowance. Its weight is at least a constant times $B$, enlarging constants at small $q$. The case $B=0$ is immediate.

In the earlier unary test the allowed difference grows like $\log\log n$ in the *bit budget*. Here the program has only constant additive bit error after the change to its time allowance. A fixed-$e$ counterexample can still be caused by the interpreter's own simulation delay. The criterion quantifies over every fixed $e$ on one interpreter. The proof supplies a necessary condition under linear SAT. Related literature gives probabilistic coding theorems and equivalences for weaker deterministic Levin-cost coding properties. Priority for this particular conditional comparison is unestablished. [Lu, Oliveira and Zimand](https://arxiv.org/abs/2204.08312) · [Hu, Lu and Oliveira](https://doi.org/10.4230/LIPIcs.ICALP.2026.110)

## Does the numeric test depend on the chosen interpreter?

The following equivalence is unconditional. Suppose one efficient literal prefix machine $V$ passes its own numeric test: for some fixed $e,c>0$ and every $n\ge2$,
$$
 A^V_{n(2+\log_2 n)^e}(\mathrm{bin}(n))\ge c B^V_n(\mathrm{bin}(n)).
$$
Then **every** efficient reference passes its own numeric test, with its own constants. In fact this one assumption implies the constant-bit comparison for arbitrary fixed sources and target references whenever the deadline can be recovered from the word itself within the available time.

Here is a quantitative version. Let $S$ be an ordinary fair-stream sampler, $U$ any efficient literal target interpreter, and $D$ another fixed fair-stream procedure with auxiliary input $y$. For any $q\ge\max(1,|y|)$ put $t=2^q$. Let $\rho$ be the probability that $D(y)$ prints the binary integer $q$ by $t(q+2)^d$ steps, for a fixed $d$. Under the numeric assumption on $V$, for some fixed $f,c'>0$,
$$
 A^U_{t(q+2)^f}(y)\ge c'\rho B_t^S(y).
$$
This includes constant-probability clock recovery, and timers with a short deterministic name supplied by fresh input bits. The clock is external to both the source and the selected output program in this assertion.

Write $r(y)=2^{|y|}-1+\mathrm{val}(y)$ for its zero-based length-lexicographic rank, including $r(\epsilon)=0$. A single wrapper runs $S$, saves the published $y$, then runs $D(y)$ on the unused fair input. When the latter returns a candidate exponent $j$, put
$$
 L=\max(j,|y|)+C\lceil\log_2(j+|y|+2)\rceil+2,
 \qquad n'=2^L+r(y).
$$
Publish $\mathrm{bin}(n')$. On the successful clock estimate $j=q$, the integer $n'$ is fixed by $q,y$, between $t(q+2)^C$ and $t(q+2)^{O(C+1)}$. Clearing its leading bit always recovers the rank. The wrapper interprets $C$ from a self-delimiting constant header; hence its native simulation exponent can be fixed before $C$ is chosen.

If $\rho B\le t^{-2}$, a literal program for $y$ already suffices, up to a fixed constant as above. Otherwise $B>t^{-2}$, and runs of $S$ taking more than $t^4$ contribute at most $t^{-3}$, leaving at least half the mass. For a retained source time $v$, the successful clock computation and the padded output take at most $\max(t,v)(q+2)^{O(1)}$ time after literal compilation on $V$. Printing $L$ bits and computing the padding use a polynomial in $q$ for fixed $C$; the arithmetic can use a fixed algorithm with $C$ as data. Choose $C$ large enough that $n'$ absorbs this polylogarithmic overhead up to a fixed constant. Thus the contribution of a retained source run to $B^V_{n'}(\mathrm{bin}(n'))$ is at least a constant times its old contribution multiplied by $\rho$. Fresh bits following each exact source publication are fair. Restricting to the common $j=q$ gives the lower bound $\Omega(\rho B)$.

By assumption there is one $V$ program for $\mathrm{bin}(n')$ with weight $\Omega(\rho B)$ at allowance $n'(2+\log_2 n')^e$. Its physical running time is at most that allowance times $O(1/(\rho B))$, hence polynomial in $t$. A fixed projection on $U$ simulates this program, clears the leading bit, and inverts the rank. Its name costs only a constant more. Its time is at most the old time times a polynomial in $q+2$, since the old time is polynomial in $t$ and reading the explicit padded word costs at most another logarithmic factor per simulated step. Increasing $f$ absorbs both the projection and the ratio $n'/t$. This proves the quantitative statement.

For another reference $U$'s numeric test, take $S=U$, $y=\mathrm{bin}(n)$ and the deterministic timer returning $|y|$. Then $t=2^{|y|}$ lies in $(n,2n]$ and $B_n^U\le B_t^U$. This proves reference independence as an all-length property. A failing sequence may move to padded lengths in transferring between machines.

The same proof allows an intrinsic clock known only approximately. Suppose a fixed timer estimates $q$ within $K\log_2(q+2)$ by $t(q+2)^d$ with probability $\rho$. For a reported nonnegative integer $j$, partition its dyadic band $2^i\le j+2<2^{i+1}$ into successive bins of width $i+1$ (truncate the final bin). Replace $j$ by the upper endpoint of its bin. For large $q$, accurate estimates intersect only a constant number of these bins: they span $O_K(\log q)$ integers, in at most two adjacent bands with bin widths $\Theta(\log q)$. At least one rounded value retains $\Omega_K(\rho)$ probability and differs from $q$ by $O_K(\log q)$. Increasing $C$ pays for this possible difference in the exponent of the clock. The padding and projection use no advice choosing the successful bin. A clock that is freely chosen after inspecting an entire output distribution still needs a recovery argument to obtain constant $\rho$.

## Searching a block in time proportional to the inverse mass threshold

There is an unconditional two-threshold experiment for this test. Fix $t=2^q$, clock multiplier $2^a$, integer budget $h\ge0$, mass threshold $2^{-d}$ with $d\ge0$, and failure probability $\eta\in(0,1/2)$. Consider all binary words of length at most $q+1$, or just the representations of integers in $[t,2t)$. In worst-case time
$$
 t\big(2^{a+h}+2^d\big)\,\mathrm{poly}(q+a+h+d+\log(1/\eta)+2)
$$
a randomized algorithm returns a list with the following simultaneous guarantees with probability at least $1-\eta$:

* Every listed word has integer soft cost $C_{2^a t}>h$ and mass $B_t^S>2^{-d}/8$.
* Every word with $C_{2^a t}>h$ and $B_t^S\ge2^{-d}$ is listed.

First compute the set of words of cost at most $h$ exactly. For each $l\le h$ test every $l$-bit name for exactly consumed publication with cutoff $t2^{a+h-l}$. This is equivalent to the cost test at that length. Recording only qualifying outputs in a trie and clearing the simulator between trials add at most a polynomial factor in the displayed parameters. The set can be computed even when only one word will ultimately be returned.

Use $J=d+4$. At time $t$ run $M$ independent fair streams. For $1\le j\le J$ run $M/2^j$ fresh streams until $t2^j$, crediting a publication only when its time lies in $(t2^{j-1},t2^j]$. Use $M$ a multiple of $2^J$ of order $2^J(q+1+\log(1/\eta))$ with a sufficiently large constant. Keep the hits $Z_y$ by word. The mean $\mathbb EZ_y/M$ lies between $B_t^S(y)/2-2^{-J}$ and $B_t^S(y)$ by rounding the retained discounts downward to powers of two and bounding the tail. Include words outside the exact cheap set if $Z_y\ge M2^{-d}/4$. When $B\ge2^{-d}$ the expected normalized count is at least $7\cdot2^{-d}/16$. When $B\le2^{-d}/8$ it is at most $2^{-d}/8$. Standard independent Bernoulli tail bounds at these two extremes and a union bound over fewer than $2^{q+2}$ words give both claims. Tries store only seen outputs, and each probability bin costs at most $Mt$ virtual steps. Within the block $B_t\le B_n\le2B_t$, and moving the soft baseline from $t$ to $n$ changes integer cost by at most one.

Consequently $a,d,h=O(\log(q+2))$ permits a search in $t\,\mathrm{polylog}(t)$ time at fixed confidence, even if only one length qualifies. This improves the clock for looking specifically at high-mass, low-budget violations. The earlier $t^2\mathrm{polylog}(t)$ procedure maximizes a different, unthresholded score over the entire block. Search speed by itself gives no lower bound on the score of a returned word or guarantee that a qualifying word exists on any particular block. [Earlier block search](unary-speed-gap.md)

Lean verifies a finite rank version of the mass estimate and the exact length-dependent cutoff. Sort equally likely stream outcomes by decreasing rate. Scale rates to a common integer denominator. When the envelope is at most $K$ rows' worth, every later rank $j>K$ satisfies $j\lambda u_j\le K$. A dyadic rank block $(m,2m]$ then contributes at most $K/\lambda$. The first $K$ rows contribute at most $K$. The Lean file checks these steps and their summation. The continuous integral, conditional coding implication, and randomized complexity bounds above are manuscript arguments. [Lean verification](../lean/DilatedMass.lean)

The exact finite check tried 1,286 positive eight-row profiles. On 256 equally likely completion times the unscaled envelope lost a factor of 6.124345, the 256th harmonic number. On a finite prefix machine with an intentionally redundant fast branch, the threshold search used 81,600 fair-stream trials. It returned the unique qualifying length, 21, whose exact mass was $4123/27648$. These are checks of the inequalities and search procedure on specified models. [Reproducible experiment](../audits/dilated_mass_experiment.py)
