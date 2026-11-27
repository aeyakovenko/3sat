# How many different queries can a fast pushdown reduction reuse?

Let $P_k$ be nonemptiness of the intersection of one PDA and $k-1$ NFAs on a common constant alphabet, with sparse transition lists of total encoded bit length $B$. Fix $s=2k$. A deterministic multitape controller has one fixed binary decision oracle. Charge its steps outside calls, the number of calls, and the sum of their explicit binary lengths, even if it reuses a query tape. Later questions may depend on earlier replies. Let $K(B)$ count the **distinct raw queries on authentic runs across all valid sparse inputs of length at most $B$**. Their lengths, names and correct labels need not be known to a uniform algorithm.

Suppose the controller decides $P_k$ with charged cost $O(B^{s-\epsilon})$, for $0<\epsilon\le s-1$. Then, for every $0<\gamma<\epsilon/(s+1)$, all sufficiently large $B$ satisfy

$$
K(B)>B^\gamma .
$$

There is also a bound close to the source exponent. For each $0<b<\sqrt s$ there is $D>0$ such that charged cost $O(B^s/2^{D\sqrt{\log_2(B+2)}})$ forces $K(B)>2^{b\sqrt{\log_2 B}}$ for all sufficiently large $B$. These conclusions hold even for an undecidable oracle. A single correct SAT call on each input could still meet them by using different formulas on different inputs. For the unrestricted choice of oracle, taking the oracle to be $P_k$ itself gives a one-query $O(B)$ controller.

## Recording an unnamed family of answers

Suppose $K$ distinct queries of maximum length $L$ occur on the family being simulated. Nonuniform advice of $O((1+K)\log(L+K+2))$ bits recovers their answers. Encode string $x$ by the pairs $(1,x_i)$ followed by an infinite zero tail. Distinct strings of length at most $L$ differ within the first $2L$ bits. On a set containing at least two keys, branch at the first bit where its keys disagree. Recurse on the two nonempty parts and label a singleton leaf by its oracle answer. For the empty family store a constant default. This compressed binary trie has at most $2K-1$ nodes when $K>0$. Store it in preorder with branching coordinates and offsets past left subtrees. Its coordinates increase strictly on every path. [Morrison's PATRICIA trie](https://doi.org/10.1145/321479.321481)

To answer an actual query of length $\ell$, scan its tape forward while traversing the advice in increasing storage order. A coordinate after the first end marker gives zero, without materializing padding. The traversal and rewind of the used portion of the advice take $O((1+\ell+K)\operatorname{polylog}(L+K+2))$ tape steps, including counters and a return to the start of the query. The decoder need only match labels on the stored family. By induction on the number of calls, every simulated query on each covered input belongs to that family and receives its true answer. Thus no alternate oracle histories need to be stored. No positive SAT witness is produced or assumed visible.

## A diagonal input carrying its own advice

For the time-constructible source clocks $T(m)$ used below, fix a language decided by a multitape machine in $O(T(m))$ with the following property. For each fixed multitape program $M$, at every sufficiently large input length $m$, no advice string of at most $\lfloor m/2\rfloor$ bits lets $M$ answer correctly on all $m$-bit inputs in $O(T(m)/\log^3 T(m))$ time. The bound holds for self-delimiting advice padded to exactly $\lfloor m/2\rfloor$ bits.

The diagonal decider reads a self-delimiting program description from the input prefix and an advice payload from the final $\lfloor m/2\rfloor$ bits. It complements the simulated program's answer on the **entire same input** and this payload if the fixed universal interpreter halts before its $T(m)$-step clock. It defaults on invalid codes and timeouts. For a fixed $M$, universal simulation costs $O_M(t\log(t+2))$ on a $t$-step computation plus input setup. For each proposed advice at each large $m$, select a string with $M$'s prefix and that advice as suffix. The presumed fast decoder halts and disagrees there. This proof does not enumerate advice. [Hennie and Stearns, two-tape simulation](https://doi.org/10.1145/321356.321362)

Apply Balasubramanian and Majumdar's compiler to that *fixed* diagonal decider, its input $x$ of length $m$, and an upper clock equal to a sufficiently large constant times $T(m)$. With $H=\log_2 T+O(1)$, Theorems 10 and 12 give relation-program size $O(mH+\operatorname{poly}(H))$. Theorem 14 bounds automaton size by $O(|\Pi|\log(|\Pi|+2)H\log(H+2)2^{H/s+O(\sqrt H)})$, with constant alphabets and sparse transitions. Binary identifiers and the construction time add polylogarithmic factors. The compiler uses the binary clock. All inputs of a common source length have an upper size bound $X_m$, even if their actual encoded lengths differ. Use the trie for the authentic queries on these compiled inputs only. Its size is bounded by the global $K(X_m)$. [Balasubramanian and Majumdar, v2, Theorems 10, 12 and 14](https://arxiv.org/html/2611.27814v2)

### Polynomial saving

First prove the conclusion with an exponent $\gamma'$ strictly between $\gamma$ and $\epsilon/(s+1)$ on the source scales. Choose a rational $z$ satisfying

$$
\frac{s}{\epsilon-\gamma'}<z<\frac1{\gamma'} .
$$

Use a clock of order $m^{s(z-1)}$, for example a power of two with exponent $\lceil s(z-1)\lceil\log_2(m+2)\rceil\rceil$. The compiler's output and construction time are at most $m^{z+o(1)}$, by the **linear** factor in its relation-program size. Choose fixed $\rho>0$ small enough that $\gamma'(z+\rho)<1$ and $(s-\epsilon+\gamma')(z+\rho)<s(z-1)$. Put $X_m=\lceil m^{z+\rho}\rceil$.

If $K(X_m)\le X_m^{\gamma'}$, all authentic queries have polynomial length in $X_m$ by the controller charge. The trie advice is $o(m)$ bits. The simulated controller costs at most $X_m^{s-\epsilon+\gamma'+o(1)}$, since each of its calls pays for at most one trie scan. The compiler also fits this bound since $s-\epsilon\ge1$. Both clocks save a fixed power of $m$ against the diagonal clock. This contradicts the diagonal property at **each** sufficiently large such $m$. Finally $K(B)$ is monotone and $X_{m+1}/X_m\to1$, giving $K(B)>B^\gamma$ throughout.

### A controller using native random access

For $k\ge2$ and $0<\epsilon\le k-1$, a deterministic logarithmic-word RAM oracle controller for $P_k$ with the same explicit-query charge and cost $O(B^{k-\epsilon})$ has $K(B)>B^\gamma$ at every sufficiently large $B$, for every $\gamma<\epsilon/k$ with $\gamma>0$.

Load the advised trie in a private random-access bank and store its child offsets explicitly. Along a true queried key of length $\ell$, all selected split coordinates are at most $2\ell+1$. Every longer key diverges from it by the first presence bit after its end, and every shorter key diverges earlier. Thus at most $2\ell+1$ direct accesses and tests suffice. With the setup paid once, the advised native clock on a compiled slice is $X_m^{k-\epsilon+o(1)}+O(K\operatorname{polylog} X_m)$. The simulation can use $O(\log X_m)$-bit host words, implementing the guest controller's actual word width. To replay on tapes, keep chronological address/value records and scan them for the last write. A read-only input access costs at most a scan of the compiled input. Since $k-\epsilon\ge1$, the tape clock is at most $X_m^{2k-2\epsilon+o(1)}$ if $K\le X_m^{\gamma'}$ with $\gamma'<1$. [Tape simulation details](pushdown-source-and-grammar-witnesses.md)

For $\gamma<\gamma'<\epsilon/k$, pick rational $s/(2\epsilon)<z<1/\gamma'$ and the same clock $T\asymp m^{s(z-1)}$. The inequalities $(s-2\epsilon)z<s(z-1)$ and $\gamma'z<1$ give both clock and advice slack. Increasing $z$ by a sufficiently small $\rho$ in the upper bound $X_m$ and interpolating consecutive scales proves the result. This counts distinct queries on many inputs of a native controller. A successful one-call reduction could create a different ordinary SAT instance on each input.

### Saving at the square-root logarithm

Write $h=\lceil\log_2(m+2)\rceil$, take $T=2^{h^2}$, and choose $a>0$ so the compiler's size and construction time are at most $X_h=\lceil 2^{h^2/s+ah}\rceil$ for large $h$. The source input factor $m$ costs only $2^{O(h)}$ here. Fix $b<b'<\sqrt{s}$. A trie with at most $2^{b'\sqrt{\log_2 X_h}}$ leaves fits $o(m)$ advice, even with its logarithmic pointer widths, since $b'/\sqrt{s}<1$. If such a trie sufficed, the base-two logarithm of the replay time, including trie scans, would be at most

$$
h^2+sa h-(D-b')\sqrt{h^2/s+ah}+O(\log(h+2)).
$$

Take $D>b'+\sqrt s(sa+1)$. This saves $\Omega(h)$ bits of clock exponent and contradicts the diagonal property. The compiler's own clock fits as $s\ge2$. Between consecutive scales, $\sqrt{\log_2 X_{h+1}}-\sqrt{\log_2 X_h}=O(1)$, so the slack $b'-b$ yields the stated bound for every large $B$.

## Consequence for a two-part SAT reduction

A controller can mark a class of calls by a uniform rule, for example a specified range of dyadic block sizes. On a compiled slice let $K$ count only the distinct marked formulas. With enough advice for their trie, a hypothetical $O(n^c)$ deterministic RAM SAT solver is needed only on **unmarked** calls. Writing $C$ for the remaining controller work and $r_*$ for the marked call count, the genuine-path deterministic tape cost is, up to polylogarithms and the source compiler,

$$
C+\sum_{i\text{ marked}}(1+\ell_i)+r_*(1+K)
     +\sum_{i\text{ unmarked}}(1+\ell_i)^{2c}.
$$

For unmarked calls use fresh memory for the native solver and the usual deterministic tape simulation. The mark must be computable before an oracle answer. A compressed trie need not recognize nonmembers, and applying it unconditionally to a new formula could change the subsequent transcript. The bound is a sufficient speedup criterion if its clock and advice both fit the diagonal budgets. No such controller is supplied. A dyadic construction still has to explain how it reconciles the private satisfying assignments of different blocks. [Pushdown source and witness-size calculation](pushdown-source-and-grammar-witnesses.md) · [Local reconciliation obstruction](diagonal.md)
