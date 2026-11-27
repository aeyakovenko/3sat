# Positive snapshot budgets at SAT time exponents 3/2 and 8/5

Suppose a fixed deterministic logarithmic-word RAM decides SAT in time $N^{c+o(1)}$ on $N$-bit formulas. For every fixed uniform decoder there are arbitrarily long inputs on which some actual solver state lacks a single description of at most $N^e$ bits that answers every native memory-word query within $N^d$ steps. The following triples satisfy this conclusion.

| SAT time exponent $c$ | Description exponent $e$ | Lookup exponent $d$ |
|---|---|---|
| $3/2$ | $1/13$ | $1/13$ |
| $8/5$ | $1/3000$ | $1/3000$ |

The decoder has random access to the original formula, the absolute time, and the same packed description for all addresses. The SAT solver may use unrestricted physical workspace. The strict arithmetic below also rules out uniform $N^{e+o(1)}$ and $N^{d+o(1)}$ budgets. This is an explicit instance of the [true-start snapshot simulation](true-start-snapshot-trading.md). The sequence of speedups and slowdowns is Williams's published annotation $1100100$. Its original application concerns physical space. [Williams, Sections 3 and 4](https://people.csail.mit.edu/rrw/automated-lbs.pdf)

## Accounting for the seven steps

Start from a full-input deterministic computation of time $n^A$ whose actual states admit $n^{Ae/c}$-bit descriptions with word-query time $n^{Ad/c}$. Divide all exponents in this calculation by $A$. The normalized initial time is one, the original input exponent is $h=1/A$, and the first root machine's description and query exponents are $E=e/c$ and $D=d/c$. A normalized split of size $x$ creates $n^{Ax}$ intervals. A SAT slowdown at normalized source exponent $U$ gives a new deterministic tail of normalized time $cU$, description length $eU$, and query time $dU$. The underlying reduction and checkpoint verifier incur arbitrarily small fixed exponent losses, suppressed in the calculation.

1. Split the root run with an existential list of size exponent $x+E$. In the challenged interval, split the same root run with a universal list of size exponent $y+E$. The choice of an outer interval and the universal inner list merge into one universal block. Within it, keep the selected outer endpoints and the original input when forwarding the inner list. The subsequent existential challenge keeps the selected endpoints and one observation per level. It replays an interval of length exponent $1-x-y$, querying an original-root description at cost exponent $D$ per instruction. Thus eliminating this last challenge has source exponent

   $$
   U_1=\max\{h,y+E,1-x-y+D\}.
   $$

   The incoming inner list covers all its selected endpoint descriptions. The word-access latency is charged once per replayed instruction after both splits.
2. Eliminate the merged universal block. Its input contains the complete first list. Its guessed length and forwarded inner-list size have already been charged in $U_1$. The source exponent is

   $$
   U_2=\max\{h,x+E,cU_1\}.
   $$

   One existential block remains, followed by a deterministic tail of time exponent $cU_2$. That tail is a fresh SAT simulation on input containing the first list.
3. Split that fresh tail with an existential list of exponent $z+eU_2$, merging with the remaining existential block. The universal challenge must forward the earlier first list as part of the fresh tail's input. Its replay has exponent $cU_2-z+dU_2$. Eliminating this challenge has source exponent

   $$
   U_3=\max\{h,x+E,z+eU_2,(c+d)U_2-z\}.
   $$

   Eliminating the merged existential block then gives a deterministic line of normalized time $c^2U_3$. The preceding maximum already bounds both existential guesses and the forwarded list.

The terminal ratios of description and query exponents to the clock are again $e/c,d/c$. If $c^2U_3<1$, this computation can be repeated at successively smaller clock exponents, choosing the initial nondeterministic exponent large enough that $h\le1/10$ throughout. A finite number of contractions then simulates nondeterministic time $n^L$ in deterministic time strictly below exponent $L$, contradicting bounded complementary diagonalization. The true-start proof establishes the replay invariant on dishonest intermediate lists, recovery of the description bounds after each SAT slowdown, and closure of the class across the iterations. [True-start proof and hierarchy argument](true-start-snapshot-trading.md)

## Rational certificates

The displayed terminating decimals denote exact rational numbers. Taking $h=1/10$ suffices for all smaller input floors. Each split leaves a normalized interval-length exponent greater than $h$.

| $c$ | $x$ | $y$ | $z$ | $U_1$ | $U_2$ | Final ratio $c^2U_3$ |
|---|---:|---:|---:|---:|---:|---:|
| $3/2$ | .39 | .305 | .4 | $2779/7800$ | $2779/5200$ | $538731/540800$ |
| $8/5$ | .3904 | .3048 | .3904 | $36601/120000$ | $36601/75000$ | $46873/46875$ |

Setting $e=d=0$ provides a separate check. At sufficiently small $h$, choose $x=z=c^2/(4+c^2)$ and $y=(1-x)/2$. For $1\le c\le2$ the resulting ratio is $c^4/(4+c^2)$, reproducing the published comparison $c^4<c^2+4$. The numerical conclusions concern the complexity of describing the state of a putative fast solver. Whether a general SAT time bound forces descriptions within these budgets remains open. Priority of the positive-budget transfer is unverified. [Exact-rational audit](../audits/positive_budget_snapshot_trade_audit.py)
