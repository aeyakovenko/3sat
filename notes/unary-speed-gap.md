# A binary coding test equivalent to the speed-prior bound on unary words

**Research journal, 24 November 2026.** Under linear-time SAT, the difference between the best Levin cost and the negative logarithm of reciprocal-time program mass is at most $O_V(\log\log(n+4))$ on **every** $0^n$. The general output-length bound was $O(\log(n+2))$. Moreover the sharpened unary assertion is equivalent, without a SAT hypothesis, to a coding condition for arbitrary ordinary samplers on short binary strings. In this condition a program can spend extra time in exchange for fewer name bits. An unbounded ratio between the unary gap and $\log\log(n+4)$ on one fixed efficient literal interpreter would exclude linear SAT. Such an unbounded ratio would persist on the same lengths on every efficient literal reference. The family yielding an arbitrarily large fixed coefficient as the interpreter varies leaves this test open. [Reciprocal-time mass definition](discounted-program-mass.md) · [Unconditional fixed-coefficient examples](native-coding-delays.md)

Use base-two logarithms. Fix one efficient literal universal native prefix machine $V$. Write $u(p)=\lceil\log\max(2,\tau(p))\rceil$ for the log of its physical publication time and use $L,W$ from the [discounted-mass argument](discounted-program-mass.md), both on $V$. For integer $t\ge2$ let $q=\lceil\log t\rceil$ and define
$$
 C_t(y)=\min_{V(p)=y}\bigl(|p|+\max(0,u(p)-q)\bigr).
$$
The baseline is a full time allowance, including for very short programs. Every complete program running within the allowance pays only its length.

## The equivalence

The following two assertions about $V$ are equivalent:

1. For all $n\ge1$, $L(0^n)+\log W(0^n)\le O_V(\log\log(n+4))$.
2. For every fixed ordinary native sampler $S$ there is a constant such that, for $t\ge2$, $|y|\le q$ and $P_t^S(y)>0$,
   $$
   C_t(y)\le D+O_{V,S}(\log(q+2)),\qquad D=\lceil-\log P_t^S(y)\rceil.
   $$

For $1\Rightarrow 2$, let $a(y)=(2^{|y|}-1)+\mathrm{val}(y)$ be the zero-based length-lexicographic rank including the empty word, with $\mathrm{val}(\epsilon)=0$. Encode $(q,y)$ by the positive integer
$$
 n=2^{q+1}+a(y).
$$
For every $|y|\le q$, even at the maximum length, $2^{q+1}\le n<2^{q+2}$. The leading bit of $n$ determines $q$, and the remaining value recovers both the length and bits of $y$. Also $n=\Theta(t)$.

One fixed stream machine reads a self-delimiting $q$ of length $O(\log(q+2))$, runs $S$ for $2^q$ virtual steps, and upon a qualifying output prints $0^n$. It finishes those runs in $t\,\mathrm{poly}(q+2)$ time on $V$ after literal compilation, and their full raw probability on $V$ is at least $2^{-D-O(\log(q+2))}$. Thus $-\log W(0^n)\le q+D+O(\log(q+2))$. Assertion 1 provides a program $p$ for $0^n$ with $|p|+u(p)$ at most this same upper bound. Explicit output on the native machine implies $n\le c\tau(p)\log(2+\tau(p))$ and hence $u(p)\ge q-O(\log(q+2))$ here. For the last implication if $\tau(p)\ge n$ it holds immediately, and otherwise use $\log(2+\tau(p))\le\log(2+n)$.

When $D>q$, a literal description of $y$ already gives $C_t(y)\le q+O(\log(q+2))$. For $D\le q$, the selected unary program has $u(p)=O(q+1)$. One fixed projection simulates it, measures its output length and reconstructs the binary word from that integer. This adds $O(1)$ bits to the name and $O(\log(q+2))$ to the log time, including any literal compiler. Combining the upper bound on $|p|+u(p)$ with the lower bound on $u(p)$ gives the claimed bound for $C_t(y)$, including when the projected program runs before $t$.

For $2\Rightarrow1$, set $b=\lceil-\log W(0^n)\rceil$. A short integer literal followed by printing gives $b\le L(0^n)=O_V(\log(n+2))$. The [dyadic summation](discounted-program-mass.md) gives an endpoint $s=2^j$, $1\le j\le b+2$, with $P_s^V(0^n)>0$ and
$$
 j+\lceil-\log P_s^V(0^n)\rceil\le b+O(\log(b+2)).
$$
Another fixed sampler simulates $V$ and emits $\mathrm{bin}(n)$ instead whenever it sees a nonempty all-zero output of length $n$. Counting and checking the explicit word, including the simulation overhead, costs $s\,\mathrm{poly}(j+2)$ on these runs. Choose an integer $t'$ of this order large enough also to have $t'\ge 2n$; the native output bound $n\le O(s(j+2))$ permits this. Its rounded exponent $q'$ is $j+O(\log(j+2))$ and the binary expansion has length at most $q'$. Its mass by $t'$ is at least $P_s^V(0^n)$. Assertion 2 supplies a binary program $p$ with
$$
 |p|+\max(0,u(p)-q')\le D_s+O(\log(j+2)),\qquad D_s=\lceil-\log P_s^V(0^n)\rceil.
$$
Consequently $u(p)\le O(b+1)$. Expanding its binary integer to the unary word on $V$ takes time at most $\max(2^{u(p)},2^{q'})\,\mathrm{poly}(b+2)$, because $n\le2^{q'}$. The total cost is at most $q'+D_s+O(\log(b+2))\le b+O(\log(b+2))$. This proves assertion 1.

It suffices to test assertion 2 with $S=V$ itself. Literal compilation gives $P_{s}^V(y)\ge c_S P_t^S(y)$ at $s=t\,\mathrm{polylog}(t+2)$ for any one fixed $S$. Changing the baseline from $s$ back to $t$ increases $C$ by at most $\lceil\log s\rceil-\lceil\log t\rceil=O_S(\log(q+2))$. Thus even the binary criterion only requires one actual machine and its own fair-bit output distribution.

Under linear SAT the [short-output coding theorem](near-clock-coding.md) gives a program of length $D+O(1)$ and time $t\,\mathrm{poly}(q+2)$ when $|y|\le q$; the one-bit rounding of the length bound at a nondyadic $t$ is covered by taking deadline $2^q$. It therefore implies assertion 2. In assertion 2 alone an inexpensive outcome with $D=O(\log(q+2))$ always has a program running in $t\,\mathrm{poly}(q+2)$. The same follows if the ordinary unbounded program complexity of $y$ is at least $D-O(\log(q+2))$. Without such a lower estimate, the budget permits a program to spend its bit savings on extra time.

## Comparing the unary and binary sums at the integer itself

There is also a direct, unconditional comparison on the same machine. For $n\ge2$ put
$$
 B_n=\sum_{V(p)=\mathrm{bin}(n)}
 2^{-|p|}\min\!\left(1,\frac{n}{\max(2,\tau(p))}\right).
$$
Then
$$
 \begin{aligned}
 L(0^n)-\lceil\log n\rceil&=C_n(\mathrm{bin}(n))+O_V(\log\log(n+4)),\\
 \log\big(nW(0^n)\big)&=\log B_n+O_V(\log\log(n+4)).
 \end{aligned}
$$
In particular the unary test can be applied directly to a capped reciprocal-time mass on the ordinary binary representation, using its numeric value as the baseline clock.

For the first line, convert a program for the binary integer into a program for the unary output by an explicit write loop. In the opposite direction count the length of the explicit output and print its binary expansion. The name changes by a constant in each direction. From a binary running time $v$ the unary runtime is at most $\max(v,n)\,\mathrm{polylog}(2+v+n)$. From unary time $u$ the binary runtime is at most $u\,\mathrm{polylog}(2+u)$, including inspection of the output if needed. Both minimizing programs have logarithmic running time $O(\log(n+2))$ by the ordinary short literal descriptions. The output lower bound gives every unary program log time at least $\lceil\log n\rceil-O(\log\log(n+4))$. These inequalities give both directions, including a binary name finishing before $n$.

For the second line each compilation maps distinct exact prefixes to distinct prefixes and changes their total raw weight by a constant factor. Literal printing gives both $B_n\ge n^{-O_V(1)}$ and $nW(0^n)\ge n^{-O_V(1)}$. For either sum, programs of running time greater than $n^c$ contribute at most $n^{1-c}$, by Kraft's inequality. Choose one sufficiently large fixed $c$ so that at least half of each sum remains at all large $n$. This avoids charging an unbounded polylogarithmic simulation factor on an exceptionally long-running name.

On the retained binary terms with time $v$, converting to unary gives a contribution to $nW(0^n)$ of at least a fixed inverse polylogarithmic factor times $2^{-|p|}n/\max(v,n)$. Conversely for each retained unary term of time $u$ the converted binary program contributes to $B_n$ at least a fixed inverse polylogarithmic factor times $2^{-|p|}n/\max(2,u)$. Indeed $n/\max(2,u)=O(\log(n+2))$ by the output lower bound on these terms, so the cap at one and the simulator's polylogarithmic overhead together lose at most a polylogarithmic factor. Summing the two injective comparisons and taking logarithms proves the second line. The constants can depend on the fixed interpreter; no bound on raw program length beyond exact consumption is imposed.

Combining the lines, $L(0^n)+\log W(0^n)=C_n(\mathrm{bin}(n))+\log B_n+O_V(\log\log(n+4))$. A counterexample to the sharpened unary target must separate the best binary description from a sum of genuine binary descriptions after both have received this same numeric time allowance. The fixed-machine separation is unresolved.

## How rare can a counterexample be, and which clocks must it cross?

There is an unconditional bound at the target scale **on almost all numeric lengths**, for every efficient reference. Write $g(n)=L(0^n)+\log W(0^n)$. There is a fixed $c$ such that for every $s\ge2$ and $r\ge0$,
$$
 2^{-s}\#\{2^s\le n<2^{s+1}: g(n)>c\log_2(s+2)+r\}\le 2^{-r}.
$$
Indeed, hardwiring $s$ and the last $s$ bits of $n$ prints the word in $n\,\mathrm{poly}(s)$ time after compilation. Hence $2^{L(0^n)}\le n\,2^s\mathrm{poly}(s)$. The explicit-write lower bound on every contributing time gives $nW(0^n)\le O(s)P^V_\infty(0^n)$ throughout the block. By summing these bounds and using total eventual mass at most one, the mean of $2^{g(n)}$ is at most a polynomial in $s$. Markov's inequality gives the claim. Thus the issue is the worst numeric length, even in this unary reformulation.

One can also localize the necessary description improvement to a finite interval of time, unconditionally. Put $N=2^s$, $n\in[N,2N)$ and $H_s=2^{N^4}$. Then for all large $s$,
$$
 g(n)\le C_n(\mathrm{bin}(n))-K^V_{H_s}(\mathrm{bin}(n))+O_V(\log(s+2)).
$$
To prove this, truncate the binary sum $B_n$ at $T=N^3$. The omitted tail is at most $2N/T=2/N^2$. A literal binary program for $n$ takes $s+O(\log s)$ bits and finishes in much less than $n$ time, so $B_n\ge N^{-1}/\mathrm{poly}(s)$. The tail is smaller than half of $B_n$ at all large $s$.

Plain exhaustive search, with no SAT hypothesis, gives every binary word $\mathrm{bin}(k)$ for $k\in[N,2N)$ a table score. Enumerate all $2^T$ complete $T$-bit tapes, simulate $V$ to $T$ per tape, and add $2^{-T}\min(1,N/2^{u(p)})$ to the output's score on a success. Here $p$ is the prefix actually consumed on that tape. Exact halting names are thereby counted with their correct probability. The factor used differs from $\min(1,k/\max(2,\tau(p)))$ by at most four; all denominators divide a common power of two of exponent $T+O(s)$. Thus every score lies between $B_k/8$ and $B_k$, and the sum of scores is at most one. In descending score order $n$ therefore has a one-based rank at most $8/B_n$. With a self-delimited $s$ and a self-delimited rank length, its rank costs at most $-\log_2B_n+O(\log(s+2))$ bits including both headers. The literal lower bound on $B_n$ ensures that the rank length is $O(s+1)$. The entire table, sort, and native simulation cost at most $2^{O(T)}$, strictly below $H_s$ even after fixed polylogarithmic compiler overhead. This gives $K^V_{H_s}(\mathrm{bin}(n))\le-\log B_n+O(\log(s+2))$. Substitute in the preceding unconditional equality for $g(n)$.

For an explicit failed construction, at each large $s$ take $n_s$ to be the first integer in $[N,2N)$ whose binary expansion is absent from the programs shorter than $s$ at $H_s$. Such an integer exists, since fewer than $N$ programs are tested. Its unbounded complexity is $O(\log(s+2))$ by the finite search given $s$, yet $K^V_{H_s}(\mathrm{bin}(n_s))\ge s$. Its soft cost $C_{n_s}$ lies between $s$ and $s+O(\log s)$: programs shorter than $s$ only finish past $H_s$, and the upper bound uses literal printing. Thus this sequence realizes almost $s$ bits of eventual description improvement, while its actual unary gaps are all $O(\log s)$. Making the missing word deep through *every* clock up to $H_s$ defeats this attempted counterexample. A refuting sequence needs both a large finite-clock description improvement and sufficiently much discounted probability; depth alone gives no lower bound on that probability.

The integer threshold-count and truncation inequalities used here have been checked in Lean. [Finite inequalities](../lean/DiscountedMass.lean)

## Locating large gaps experimentally on a fixed interpreter

Given $s$ and native access to a fixed interpreter, one can locate an actual length in $[N,2N)$ whose gap is within a fixed additive constant of the block maximum with probability at least $1-N^{-2}$. The **worst-case** running time is $N^2\mathrm{polylog}(N+2)$ and the workspace is unrestricted. The estimate covers all lengths in the block at once. This gives an ordinary finite search procedure for examining an interpreter; its time exceeds the soft baseline of the lengths it inspects.

Use the literal descriptions above to fix an integer $H=2s+O_V(\log(s+2))$ with $L(0^n)\le H$ and $W(0^n)\ge2^{-H}$ throughout. First compute every $L(0^n)$ exactly. For each program length $l\le H$, enumerate all its names with a clock of $2^{H-l}$, retaining only exact consumption and a valid zero-word output in the block. Each length costs at most $2^H$ virtual steps. Counting output bits, checking zeros and resetting the simulator adds only polynomial overhead in $H$. Every minimizing name is tested.

For the masses set $J=H+3$ and take $M$ a multiple of $2^J$ between $C(s+1)2^J$ and $(C(s+1)+1)2^J$ with $C$ a sufficiently large integer. For each $1\le j\le J$ make exactly $M/2^j$ fresh, independent fair-input runs through $2^j$ steps. Credit a hit only when an output $0^n$ in the block is completed with $u(p)=j$. Writing $Z_n$ for its total hits over the bins, the mean of $Z_n/M$ equals the retained weight with each $1/\max(2,\tau)$ rounded down to $2^{-u}$. The truncated true tail is at most $2^{-J}\le W(0^n)/8$ and rounding loses at most a factor two. Thus $7W(0^n)/16\le\mathbb{E}Z_n/M\le W(0^n)$. For each fixed $n$ the hits are independent Bernoulli trials prior to summation, so a multiplicative Chernoff bound followed by a union bound over the $N$ lengths shows that all counts lie between one half and three halves of their respective means, except with probability $N^{-2}$. The estimates then yield all logarithms to an absolute constant. Maximizing the integer $2^{L(0^n)}Z_n$ selects the promised approximate maximizer. The virtual cost of each bin is at most $M$; independent sampling on demand, monitoring and bookkeeping preserve the stated total clock. This does not establish that the maximum on any unbounded sequence of blocks grows fast enough.

On a finite prefix machine with a literal branch, a fast branch with redundant names, and a late branch, the stratified experiment recovered the exact maximizing length 21 among lengths 16 through 31. Its cost-weight product was $1408/63$. This tests the estimator on a known finite table. [Reproducible search](../audits/discounted_mass_experiment.py)
