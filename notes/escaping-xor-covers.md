# How narrow must a cover of the easy words be?

**Research journal, 24 November 2026.** Write $N=2^q$ and let $E_q$ be the $q$-bit words printed by programs of length at most $q-2$ that halt with exactly that output on the fixed plain machine by time $2^q(q+2)^{\lceil\log_2(q+2)\rceil}$. Fix a rational $0<\delta<1$. Consider a union of XOR sumsets $U_i+V_i$ with total pair count $P=\sum_i|U_i||V_i|\le(1-\delta)N$, covering all but $o(N)$ members of $E_q$. Put $W=\sum_i(|U_i|+|V_i|)$. [Program-image cover criterion](covering-program-images.md)

There are constants $c,C>0$ such that at least $cN$ **distinct easy words** must be supplied by rectangles whose shorter side lies between $cN/W$ and $q^C$. With raw $q$-bit list entries occupying $o(N)$ bits, the lower end grows faster than $q$. A separate construction rules out even this range for a block-local cover on a sufficiently short suffix.

## A rare event on sums of independent inputs

For a fixed dyadic density $\rho=2^{-r}$ and fixed rational $0<\varepsilon<\rho/2$, there is a polynomial-time test $J_q$ with

$$
\left|\Pr[X+Y\in J_q]-\rho\right|\le\varepsilon
$$

at sufficiently large lengths whenever $X,Y$ are independent and each has min-entropy at least $C_{r,\varepsilon}\log_2 q$. This includes uniform input by taking both factors uniform.

To see why the error is available at a prescribed small density, use the intermediate reduction before the majority gate in Li's one-bit sumset extractor. For each fixed $t$ it produces $A=q^{O(1)}$ bits, with $A\to\infty$. Their joint law is $o(1)$-close to a mixture of laws in which all but $O(A^{0.4})$ coordinates are unbiased and $t$-wise independent. In Chattopadhyay and Liao's Lemma 5.4 set the sampler parameters to $u=A^{-0.6}$ and $v=q^{-1}$, with independence order $t$. For $C$ candidates per row that lemma requires a strong affine correlation breaker of order $Ct-1$ with error at most $A^{-2t}C^{-1}uv$. It gives distance at most $3v$ to a mixture whose components each have at most $2uA$ uncontrolled bits. The positions of those bits can depend on the component. Their Lemma 3.18 supplies a linear somewhere-random sampler with output length $d=D\log q$ and $O(\log^2 D)$ candidates per row. Li's Theorem 7.12 supplies the strong affine correlation breaker with inverse-polynomial error. For fixed $t$ one takes $D$ a sufficiently large constant as in the proof of Li's Theorem 7.13. The advice length is $\lceil\log_2(AC)\rceil=O_t(\log q)$ and the required correlation-breaker error is inverse polynomial for fixed $t$. The entropy costs $k_1+Ctd$ and $k_2$ in Lemma 5.4 are then both $O_t(\log q)$. [Chattopadhyay and Liao, Lemmas 3.18 and 5.4](https://arxiv.org/pdf/2110.12652) and [Li, Theorems 7.11–7.13](https://arxiv.org/pdf/2303.06802)

Let $h_A$ be the least integer for which $\Pr[\operatorname{Bin}(A,1/2)\ge h_A]\le\rho$. Accept if the reduction has Hamming weight at least $h_A$. Within each mixture component, replacing its uncontrolled coordinates by fresh fair bits independent of the other coordinates gives a $t$-wise independent vector and changes the weight by at most $O(A^{0.4})$ in every outcome. Bounded independence fools each of the two threshold tests obtained by shifting $h_A$ by this amount, to error at most $\varepsilon/3$ for a sufficiently large fixed $t$. The maximum binomial point mass $O(A^{-1/2})$ bounds the mass of the entire boundary interval by $O(A^{-0.1})$. Averaging over the mixture gives the claim. The threshold is computable by integer binomial sums in polynomial time. [Diakonikolas, Gopalan, Jaiswal, Servedio and Viola, bounded independence for halfspaces](https://epubs.siam.org/doi/10.1137/100783030)

Take $\varepsilon=\rho\delta/8$. A plain decoder takes $r$, uses these explicit constructions with their parameters computed from $r,\delta$, and enumerates $J_q$ in $N\,\mathrm{poly}(q)$ time. Since $|J_q|<2\rho N$, an ordinal of $q-r+1$ bits suffices and its length determines $q$. Choose $r$ large enough to pay for the fixed decoder, $\delta$, a self-delimiting name of $r$ and the two-bit saving. Then $J_q\subseteq E_q$. For every rectangle with shorter side at least $q^C$, at most $(\rho+\varepsilon)|U_i||V_i|$ pairs land in $J_q$. Their entire union therefore misses at least

$$
(\rho-\varepsilon)N-(\rho+\varepsilon)(1-\delta)N\ge 3\rho\delta N/4
$$

members of $J_q$. Rectangles with shorter side at most $L=\rho\delta N/(4W)$ contribute at most $LW$ pairs. After accounting for the $o(N)$ words allowed to escape, the intervening rectangles must cover at least $\rho\delta N/2-o(N)$ distinct members. This proves the asserted window. For compressed list codes the assertion uses the actual entry count $W$.

## Distinct sums allow a linear threshold in a smaller cube

In a $b$-bit cube of size $M=2^b$, one can deterministically construct in $2^{O_{\rho,\varepsilon}(b^2)}$ time a set $H$ of density between $\rho-\varepsilon$ and $\rho+\varepsilon$ such that

$$
|H\cap(U+V)|\le(\rho+\varepsilon)|U||V|
\qquad\text{if }\min(|U|,|V|)\ge L=\lceil C_{\varepsilon} b\rceil .
$$

Choose each label independently with probability $\rho$. For a particular $L$-by-$L$ rectangle with $m$ distinct labels, the hit count is binomial with $m\le L^2$ trials. The chance it exceeds $(\rho+\varepsilon)L^2$ is at most $\exp(-2\varepsilon^2 L^2)$ by domination by $L^2$ trials and Hoeffding's inequality. There are at most $2^{2bL}$ rectangles. For a sufficiently large $C_\varepsilon$, the expected number of violations, including a violation of either global density bound, is below one. For larger sides, randomly subsample $L$ elements without replacement on each side independently. Assign one representative to each distinct hit in the original rectangle. Each assigned pair survives with probability $L^2/(|U||V|)$. The expected number of surviving representatives is at most $(\rho+\varepsilon)L^2$, as required. This estimate counts outputs once even when an XOR has many representations.

Fix the label bits one at a time, choosing an assignment that does not increase the conditional expected number of violations. For each small rectangle, tally the labels already selected and the distinct labels still undecided, then use a binomial tail for the remaining trials. The two whole-cube tails are computed the same way. As $\rho=2^{-r}$, all probabilities have common denominator dividing $2^{rM}$. Arithmetic on $O(rM+bL)$-bit integers, construction of the distinct sums, and $M$ passes over at most $2^{2bL}$ rectangles fit the stated time bound. At the last assignment the integral violation count is zero.

The linear order of the shorter-side threshold is necessary. Given any $H$ of density at least $\alpha>0$, take $s=\lfloor c_\alpha b\rfloor$ and a uniformly random $s$-set $U$. The expected number of $v$ with $U+v\subseteq H$ is $M\binom{|H|}{s}/\binom{M}{s}\ge M(\alpha/2)^s$. Take $c_\alpha$ small enough for this to exceed $\sqrt M$, and fix a corresponding $U$. Each retained translate meets at most $s^2$ candidates including itself, by counting differences in $U+U$. Greedily selecting disjoint translates yields a set $V$ of at least $\sqrt M/s^2$ elements. Every one of the $s|V|$ distinct sums lies in $H$. Thus even an unlimited construction budget cannot give this estimate at every sublinear width.

In particular, take a uniformly computable suffix width $b(q)\to\infty$ with $b^2=o(q)$, computable from $q$ within $\mathrm{poly}(q)$ time. The conclusion also holds for $b^2\le c_{\rho,\varepsilon}q$ with a sufficiently small fixed constant. All words $p\Vert h$, for arbitrary prefixes $p$ and $h\in H$, now have eligible short programs. A decoder reads $p$ literally, reconstructs $H$ within $2^q\,\mathrm{poly}(q)$ time, and reads $h$ by its shortened suffix ordinal. Here $r$ is chosen with this decoder and the width rule included.

Suppose local dictionaries have total raw entry cost $bW=o(N)$, and that their Cartesian products across all prefixes have total size at most $(1-\delta)N$. The total number of covered easy test words is at most $(\rho+\varepsilon)(1-\delta)N+LW$. The test words number at least $(\rho-\varepsilon)N$, so $\Omega_\delta(N)$ of them escape. This rules out the narrow-suffix cover unconditionally. The quadratic and cubic criteria use $b=\lfloor q/5\rfloor$ and $b=\lfloor q/10\rfloor$, where this construction exceeds the output clock. I have neither a timely construction at these widths nor a cover of the actual easy words.

The prefix restriction matters for this witness. A single unrestricted rectangle covers its entire lift exactly. Use all $p\Vert 0^b$ on one side and all $0^{q-b}\Vert h$ on the other. The pair count equals the number of lifted test words. Its raw entry cost is $o(N)$ whenever both $b-\log_2 q$ and $q-b-\log_2 q$ tend to infinity.
