# Which short computations can produce batches with few easy indices?

**Research journal, 24 November 2026.** Use dyadic phases $q=2^k$, the gamma code $a(q)$, $d=|a(q)|+\lceil\log_2(q+2)\rceil$, and $N=2^{d+1}$. The pool consists of the first $N$ words of length $q$. Its easy indices $E_q$ have exact programs of length at most $d$ printing their words by $T=2^q(q+2)^{\lceil\log_2(q+2)\rceil}$. The following bound is unconditional. It controls the combined weight of timely descriptions across **all** offending batches, including all exact aliases for each batch. [Sampled-batch criterion and conventions](hitting-sampled-batches.md)

Fix a deterministic prefix interpreter with $q$ supplied as auxiliary input. For an $N$-bit mask $S$, let
$$
 \nu_q(S)=\sum_{p}2^{-|p|},
$$
where the sum uses exact programs of length $\ell\le q$ that output $S$ and halt within $2^{q-\ell}$ steps. This finite measure has mass at most one by Kraft. At each length $\ell$, enumerating $2^\ell$ programs costs $2^q\,\mathrm{poly}(q)$ including simulation, exact consumption and output handling. Group identical masks and add their weights using denominator $2^q$. Enumeration, sorting and grouping at all lengths cost $2^q\,\mathrm{poly}(q)$.

For a sufficiently large fixed header reserve $c$, put $K=2^{d-c-|\mathrm{delta}(k)|}$ using the Elias delta code. Take sufficiently large phases so $K$ is a positive integer. Let $F_s(b)$ be the probability that a uniformly chosen $K$-subset of $[N]$ meets a fixed $s$-subset in at most $b$ points. Simultaneously for $0\le s_0\le N$, $0\le b\le K$,
$$
 \sum_{\substack{|S|\ge s_0\\|S\cap E_q|\le b}}\nu_q(S)
 \ \le\ (b+1)(b+2)F_{s_0}(b).
$$
Thus even one batch with an $\ell$-bit description meeting its clock would require $2^{-\ell}\le(b+1)(b+2)F_{s_0}(b)$ to occur in this sum.

## Selecting a common test set by exact arithmetic

The same construction works for any fixed procedure listing a dyadic subprobability $\nu$ within $2^q\,\mathrm{poly}(q)$ time, with a common denominator of polynomial bit length. For a $K$-subset $H$ use
$$
 W(H,S)=\sum_{j:F_{|S|}(j)>0}\frac{\mathbf1\{|H\cap S|\le j\}}
 {(j+1)(j+2)F_{|S|}(j)},\qquad 0\le j\le K .
$$
For every $S$ its mean over uniform $H$ is at most $\sum_{j=0}^K 1/((j+1)(j+2))<1$. Fix the membership bits of $H$ in coordinate order, always choosing the feasible child with smaller conditional mean of $\sum_S\nu(S)W(H,S)$, breaking ties by zero. Each parent mean is a convex combination of its feasible child means. At the last step the score is at most one.

Exact summation over exponentially many masks needs only a polynomial bit length. Put $M=\binom NK$ and $A_{s,j}=M F_s(j)$. A common multiplier for every score is
$$
 J=\prod_{\substack{0\le s\le N,\,0\le j\le K\\A_{s,j}>0}}(j+1)(j+2)A_{s,j}.
$$
It has $O((N+1)(K+1)(N+\log_2(K+2)))$ bits. At a partial assignment with $n$ coordinates and $u$ picks remaining, the conditional numerator for each indicator is a sum of hypergeometric binomial products with common denominator $\binom nu$. Its parameters are the hits already fixed and the number of still available members of $S$. Multiplying by $J$, the weight denominator and $\binom nu$ therefore clears every term in the conditional score. This uses polynomially many bits in $q$ regardless of how many different masks occur. Each conditional comparison takes polynomial work per listed mask, and all $N$ decisions take $2^q\,\mathrm{poly}(q)$ time.

A deterministic program reads $\mathrm{delta}(k)$, then a raw ordinal of $\log_2 K$ bits, reconstructs this canonical $H$, and prints the indicated pool word. The fixed reserve $c$ covers the selector, interpreter and an encoding of $c$. All these names fit $d$ bits and finish by $T$, so $H\subseteq E_q$. If $|S|\ge s_0$ and $|S\cap E_q|\le b$, the term $j=b$ gives $W(H,S)\ge1/((b+1)(b+2)F_{s_0}(b))$ by monotonicity in $s$. When $F_{s_0}(b)=0$ such a mask cannot exist. These facts prove the bound with this same $H$ for every threshold.

## Fair-tape events with narrow certificates

Let a fixed ordinary sampler on $q$ publish a batch by $D=2^{\lfloor q/2\rfloor}$, using the empty mask on timeout or malformed output. For its bad event $B=\{|S|\ge s_0,\ |S\cap E_q|\le b\}$ on $D$ fair tape bits, take any family of subcubes $C\subseteq B$ fixing at most $w=\lfloor q/4\rfloor$ arbitrary positions. Give them nonnegative weights $v_C$ with $\sum_{C\ni z}v_C\le1$ at every tape. Then, for a fixed header reserve covering this sampler,
$$
 \sum_C v_C\,2^{-\mathrm{width}(C)}
 \ \le\ \frac{16}{15}(b+1)(b+2)F_{s_0}(b).
$$

For sufficiently large dyadic $q$ the position-label field degree $h=q/2$ is already a power of two. In the one-block tape generator use evaluation-field degree $e=w+\lceil\log_2(wh+1)\rceil+4$. The bias of each nonempty parity on at most $w$ positions is at most $(wh-1)/2^e$, so every such cube has seeded probability at least $15/16$ times its fair probability. Construct the exact-degree evaluation field by enumerating monic polynomials and testing irreducibility by repeated squaring and polynomial gcds, in $2^e\mathrm{poly}(q)$ time. The label field uses the quadratic tower. [Tape generator and fractional packing argument](cube-tape-coding.md)

Exhausting both $e$-bit seed fields gives an explicit distribution on batches with denominator $2^{2e}$, at cost $2^{2e}D\,\mathrm{poly}(q)=2^q\,\mathrm{poly}(q)$. Apply the exact selector to this distribution. Its seeded probability of $B$ is at most $(b+1)(b+2)F_{s_0}(b)$. Pointwise packing and the cube lower bounds show it is at least $(15/16)\sum_C v_C2^{-\mathrm{width}(C)}$. The sampler and selector receive no description of the cubes or of $E_q$. These bounds leave open the fair probability carried by successful tapes without such certificates.
