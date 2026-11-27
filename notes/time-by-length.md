# Whole sets of short descriptions that acquire their outputs late

**Research journal, 24 November 2026.** Assume deterministic linear time for ordinary SAT on a logarithmic-word RAM with unrestricted space. There are effectively selected blocks of output lengths in which, for many consecutive candidate lengths, *every* word with a prescribed zero prefix eventually has a short producer. For almost all lengths in that consecutive segment, almost all those words still have no short producer at a cutoff only a polynomial factor earlier. The prefix-free source is common to every length. [Length-mass inequality](prefix-lengths.md) · [Release times at a single length](clock-release.md)

## A prefix-free native clock

Use a single deterministic universal stream RAM with no public length or end-of-input signal. It first reads a prefix-free machine description. The simulated input is an unbounded one-way bit stream, and a halting program is exactly the finite prefix consumed when the computation halts. A run that halts publishes one finite binary word. Its domain is globally prefix-free, even across different output lengths.

At elapsed step $s$ take the physical width to be $w(s)=4\lceil\log_2(s+2)\rceil$ bits. Stored nonnegative values extend by zero when the width grows. The finite instruction set has indirect access, word logic, bounded shifts, modular arithmetic, control flow and bit-stream I/O. An instruction never writes more than a constant number of words. A designated interpreter can execute a fixed stream algorithm by a constant-length header. A fixed conventional logarithmic-word computation that generates and processes an explicit $L$-bit SAT input runs with a fixed polynomial overhead in $\log(L+s+2)$ per step. To see this, represent simulated words or addresses in limbs and store addressed words in a binary trie keyed by their bits. Allocate its nodes consecutively as needed. They fit in the physical address space after that many allocation steps. During construction one can handle even a large address by its bit representation. Fixed instruction-table dispatch, finite control, and arithmetic on these representations all take polynomial time in the bit lengths. For the decoders below these lengths are $O(N)$ or polynomial in $N$ throughout a block of scale $N$. Native machine words in *arbitrary* bounded transcripts have $O(\log(s+2))$ bits by definition. This new source supports quasilinear-time compilation of the fixed decoders up to polynomial factors in $N$. The multitape source in the earlier length note pays a larger simulation overhead.

For each $j\ge1$ put $N=2^j$ and use one cutoff $B_j=2^{20N}$ for every output length $N\le m<2N$. Only producers of length strictly less than $m$ count for an $m$-bit word. Write $P_{j,m}$ for the $2^{m-j}$ words of length $m$ whose first $j$ bits are zero. Let $q_m(t)$ be the fraction of that set produced by time $t$. Define

$$
 A_j(t)=\sum_{m=N}^{2N-1}2^{-m}\#\{y\in P_{j,m}: y\text{ is produced by }t\}
       =N^{-1}\sum_{m=N}^{2N-1}q_m(t).
$$

For *any* choices of times $t_j$, $\sum_j A_j(t_j)\le1/2$. Select one program for each counted word. Distinct words of all lengths use distinct halting names. A selected name $p$ pays $2^{-m}\le 2^{-|p|}/2$, and global Kraft mass is at most one. There is no computable convergence rate assumed here.

## Finding blocks under the linear SAT hypothesis

Choose a sufficiently large fixed integer $a$ and put $T_j=\lfloor B_j/N^a\rfloor$. For positive $b\le j$, the predicate $A_j(T_j)>2^{-b}$ has a uniformly constructed quantified circuit with a fixed number of blocks. Guess a bitmap on all candidate pairs $(m,y)$. Require its integer weight to exceed $2^{2N-b}$, giving each marked pair weight $2^{2N-m}$. There are fewer than $2^{2N}$ pairs, and the exact binary weight computation takes $2^{2N}\operatorname{poly}(N)$ size and time. Universally choose an index. If marked, existentially supply one name $p$, its length less than $m$, and one accepting native transcript by $T_j$ outputting $y$. Verify that the run consumed exactly $p$, halted, and emitted exactly the specified $m$ bits. Correctness of addressed reads follows from sorting the access records and checking adjacent values, with initialized memory and same-step ordering specified. Native widths and record lengths fit $\operatorname{poly}(N)$ throughout this check. All marked pairs have real producers precisely when the guessed table is a subset of the true output set. Taking the true set proves the converse. The comparison is exact at equality.

Only one selected transcript is checked. Thus the matrix and quantifier lists take $(T_j+2^{2N})\operatorname{poly}(N)$ encoded bits and construction time. Under linear SAT, fixed-block elimination decides the predicate, or its complement, within the same form of bound. The exponent of $N$ in this bound, including compilation on the stream machine, can be chosen independent of the numerical value of $a$: clocks have $O(N)$ bits, and a uniform algorithm computes $N^a$ with $a$ supplied as a fixed parameter. For sufficiently large fixed $a$, scanning any subsequence of stages through $j$, testing each stage at most once and then printing one selected output, finishes by $B_j$ for all large $j$. Earlier scales are doubly exponentially cheaper and there are at most $j$ of them. [Explicit fixed-block elimination](linear-quantifiers.md)

Starting with $j_0=0$, let $j_r$ be the least $j\ge\max(j_{r-1}+1,r)$ with $A_j(T_j)\le2^{-r}$. Each search terminates by the sum bound. A decoder supplied only $r$ performs these searches in order, recovering $j_r$ within its block's cutoff.

## Consecutive lengths that fill by the full cutoff

Encode $r$ in a prefix code of length $\ell(r)\le\log_2 r+2\log_2\log_2(r+2)+O(1)$, for example the gamma code for its bit length followed by its low bits. After a second self-delimiting integer $d$, put $j=j_r$. Read $k=j-\ell(r)-d$ raw offset bits and let their value select $m$ among the **first $2^k$ lengths** of the block (ignore small $r$ with $k<0$). Read $m-j$ more bits and prepend $j$ zeroes. Fix $d$ larger than the fixed header and its own code length combined, including the fixed value of $a$. Every resulting exact input name has length less than $m$. Varying the last field produces *every* word of $P_{j,m}$ by $B_j$ for every one of these lengths. The fraction of lengths in this guaranteed consecutive segment is $f_r=2^{-\ell(r)-d}\ge c/[r(\log_2(r+2))^2]$ for a fixed $c>0$.

At most $N2^{-r/2}$ lengths in the *whole* selected block have $q_m(T_j)\ge2^{-r/2}$, by the block average. Consequently at least

$$
 N\bigl(f_r-2^{-r/2}\bigr)
$$

lengths in the initial segment have the following property. All target words have a short producer by $B_j$, and strictly more than a $1-2^{-r/2}$ fraction have their **first** short producer in $(T_j,B_j]$. The fraction of exceptions within the guaranteed segment tends to zero. The exceptional lengths need not be consecutive.

The precision can grow independently of the code length for $r$. For example, replace $r$ in the small-average threshold by $2^r$, and require $j\ge2^r$. The same proof gives late fraction greater than $1-2^{-2^r/2}$ outside at most $N2^{-2^r/2}$ exceptional lengths, with the same order of guaranteed segment size. More generally, for a fixed total computable positive integer $b(r)$ tending to infinity, retain the increasing search and start it beyond $r$, $b(r)$, and the time to compute $b(r)$. Earlier selected stages and these fixed computations fit below the resulting $B_j$. The formula gives at most $N2^{-b(r)/2}$ exceptions, which is a vanishing fraction *of the segment* whenever $2^{-b(r)/2}=o(2^{-\ell(r)})$.

The guaranteed full-coverage fractions $f_r$ are summable by Kraft's inequality for the code for $r$. The late words charged to different blocks are distinct, but their required mass can therefore fit the global half-unit of description weight. Indeed the aggregate normalized late mass in the selected block is at least $A_j(B_j)-A_j(T_j)\ge f_r-2^{-r}$. An upper bound on late production that beats this quantity on unbounded selected blocks would exclude linear SAT. The counting and time arguments here supply no such upper bound.

Lean checks the finite bound on exceptional lengths inside the fully covered segment. The existing prefix-code file checks the Kraft charge and the raw decoder's strict length saving. The native model and simulation times remain manuscript arguments. [Segment estimate](../lean/TimeByLength.lean) · [Prefix-code verification](../lean/PrefixLengthMass.lean)
