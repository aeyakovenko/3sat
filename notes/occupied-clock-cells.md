# Which changes in a word's description history survive a change of interpreter?

**Research journal, 24 November 2026.** A simulation can move individual publication times and can merge small decreases in shortest program length. On a fixed logarithmic time grid, the number of cells containing a decrease is nevertheless comparable on **every pair of efficient literal prefix-universal interpreters, for each particular word**. The comparison is unconditional. It gives an actual universal-machine upper-bound strategy for the [successive-description test](successive-description-times.md), and isolates the estimate that strategy still needs.

## A constant bound on empty stretches

For $|y|=m$, put $b=\lceil\log_2(m+2)\rceil$, $N=\lfloor m/b\rfloor$, and $T_j=2^{3m+jb}$ for $0\le j\le N$. A grid cell $j$ is occupied on $U$ if $K^U_{T_{j-1}}(y)>K^U_{T_j}(y)$; allow infinity before the first timely program. Let $A_U(m,y)$ count these cells. One may add the final partial cell to the statistic at cost at most one.

Fix efficient literal interpreters $U,V$ in the native model. Their simulations in either direction have a fixed additive name overhead and a fixed polylogarithmic step overhead, uniformly in the payload. Thus for constants $C,c_1,c_2$, all large $m$, and all indices with $0\le j\le j+C\le N$,

$$K^V_{T_{j+C}}(y)\le K^U_{T_j}(y)+c_1,\qquad K^U_{T_{j+C}}(y)\le K^V_{T_j}(y)+c_2.$$

Indeed $\log T_j\le4m$ and a factor $2^{Cb}$ absorbs the simulation slowdown. These inequalities use actual completed programs and include a slowdown that may depend on the simulated computation within the stated uniform bound.

Consider any consecutive plateau of $V$ with the same value $v$ at sample indices $a,\ldots,h$. After discarding at most $C$ cells at each end, the values on $U$ from $a+C$ to $h-C$ lie between $v-c_1$ and $v+c_2$ when $v$ is finite. They therefore have at most $c_1+c_2$ strict decreases there. When $v$ is infinite the lower inequality forces all the interior values on $U$ to be infinite as well. The same cell bound holds if the plateau has no interior. Separating the $A_V$ occupied cells from the at most $A_V+1$ constant stretches gives

$$A_U\le A_V+(A_V+1)(2C+c_1+c_2).$$

Interchanging $U,V$ proves the converse. The same argument applies inside any one subinterval of this grid. In particular, competitor-specific reordering cannot turn a positive fraction of occupied cells into a vanishing fraction on another efficient interpreter for the same words. A dense burst of many single-bit decreases inside **one** cell receives weight one in this comparison.

The native conditional construction in the [successive-description note](successive-description-times.md) has genuine decreases on disjoint blocks of a fixed number of these cells. Its final program on the constructing machine has length at most $2b+O(1)$ and finishes by $2^{(4-\epsilon)m}$ for a fixed $\epsilon>0$ (use its choice $B\ge2A$ and take $m$ large). Under linear SAT, the very same sequence of words consequently has $\Omega_{V}(m/\log m)$ occupied cells and a program of length $\le3b$ by $2^{4m}$ on **each** fixed efficient $V$, for all sufficiently large lengths depending on $V$. A program first completing right against the final deadline on an arbitrary source would lack this time margin. Timed simplicity at that exact endpoint cannot simply be transferred by adding only a compiler tag.

## From occupied cells to an interpreter with few individual decreases

Start with a specified reference $U$. Use its fixed-epoch wrapper $W$, which simulates exactly the raw $U$ name, buffers its result and publishes no earlier than $U$. The wrapper permits publications only at global physical times $C_0 2^{e_s}+\operatorname{poly}(e_s)$ with $e_{s+1}-e_s=g\lceil\log_2(e_s+2)\rceil$ for one fixed integer $g\ge1$. The construction preserves efficient literal universality. In the clock range at issue, successive logarithmic epoch times are separated by at least a fixed positive multiple of $b$, so each grid cell and the final partial cell contain only $O_g(1)$ allowed publication times. [Epoch implementation](successive-description-times.md)

Every raw strict decrease on $W$ belongs to an occupied grid cell or to the final partial cell. Hence $J_W(m,y)\le C'(A_U(m,y)+1)$ for all large $m,y$, by the comparison just proved. Moreover, if $y$ has a $W$ name of length at most $3b$ by $2^{4m}$, the **same raw name** was already timely on $U$. Consequently a sub-$m/\log m$ upper bound along merely an infinite subsequence for the occupied-cell maximum among these simple words of $U$ would supply a genuine interpreter violating the raw-count SAT consequence. This permits working with a canonical source and a sampled statistic. The unconditional [square-root construction](adaptive-description-times.md) and the matching plateau comparison leave open the required upper estimate. I found no such estimate for the reference machine.

[Finite plateau inequalities in Lean](../lean/OccupiedClockCells.lean)

## How many terminal candidates must be examined?

Fix a reference optimal native prefix interpreter $G$, use $K$ for its unbounded complexity, and represent integers by canonical binary strings. The coding theorem gives the length-mass bound

$$\sum_{|z|=s}2^{-K(z)}\le c\,2^{-K(s)}.$$

Indeed the left side is a lower semicomputable semimeasure of $s$. This also gives the bound $O_V(2^d)$ on the number of $s$-bit words with $K^V_{2^{4s}}(z)\le K(s)+d$ for any fixed $V$, by ordinary optimality. [Levin's coding theorem](https://doi.org/10.1090/surv/220)

There are infinitely many integers $L$ whose binary expansion has a name of length $K(L)+O(1)$ executable in $\mathrm{poly}(L)$ time. Let $p$ range over shortest $G$-programs for words of unbounded complexity and let $t$ be its exact halting time. Pack $(p,t)$ injectively into the binary digits of $L$, for example as $1^{|p|+1}0p\,\mathrm{bin}(t+1)$. Then $L\ge t+1$. Simulate $p$, count its steps and save the input bits it reads. This computes $L$ from $p$ within the budget. Conversely $L$ computes $p$ and running $p$ recovers its original output, hence $K(L)=|p|+O(1)$.

For any such $L$, each $L$-bit integer $m$ has a fast name of length $L+K(L)+O(1)$ by supplying the last $L-1$ bits after $p$ and running the preceding decoder. Applying the length-mass bound at $s=L$ shows that all but an $O(2^{-a})$ fraction of these integers have $K(m)\ge L+K(L)-a$. The fast names on this fraction thus have length $K(m)+a+O(1)$. Under linear SAT, feed each fast name to the fixed history selector instead of its usual encoding of $m$. The setup takes $\mathrm{poly}(L)$ time and preserves the exponential slack at its final clock. For every fixed $V$, the word it selects consequently has $\Omega_V(m/\log m)$ occupied cells and lies in a terminal dictionary of cardinality $O_V(2^a)$, on a fraction $1-O(2^{-a})$ of the lengths in each of these infinitely many blocks. For a fixed desired fraction the cardinality bound is independent of the length. The bound alone gives no way to learn the members by the initial deadline.

The additive allowance in this conclusion really depends on the interpreter. For every desired allowance $D$, build $U_H$ with a branch $0p$ that interprets $G(p)$ as the canonical integer $m$ and prints $0^m$. A literal fallback $1^H0p$ runs $G(p)$ directly. Both branches are prefix-free and the fallback retains efficient literal universality. Projection to length gives $K(y)\ge K(m)-c_0$ for every $m$-bit $y$, with $c_0$ independent of $H$. If $H>D+c_0+1$, every nonzero $m$-bit word costs more than $K(m)+1+D$ on $U_H$, while $K^{U_H}(0^m)=K(m)+1$. Thus the dictionary within $D$ bits of the smallest **unbounded** output complexity at each length is exactly $\{0^m\}$. On the high-density lengths just constructed this word already has complexity at most $K(m)+a+O(1)$ by $2^{3m}$ and can undergo at most $a+O(1)$ further decreases. If $H$ also covers $a$ and the fixed decoding constants, the same singleton assertion holds within $D$ bits of the smallest **deadline-bounded** output complexity at $2^{4m}$ on these lengths. This prevents a uniform choice of terminal slack from yielding the conditional history lower bound across interpreters.
