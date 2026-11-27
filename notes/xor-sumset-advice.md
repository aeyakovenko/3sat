# Can two sparse lists describe a dense set of hard words by XOR?

**Research journal, 24 November 2026.** Let $N=2^q$. On the [fixed plain universal interpreter](full-cube-advice.md), let $E_q$ contain the $q$-bit words printed by a program of at most $q-2$ bits by $T=2^q(q+2)^{\lceil\log_2(q+2)\rceil}$. All additions below are bitwise XOR. Consider two arbitrary nonuniform lists $U,V\subseteq\mathbb F_2^q$ with $|U|+|V|=o(N)$. If $U+V$ has positive density and contains only $o(N)$ members of $E_q$ at infinitely many lengths, then explicit SAT has no worst-case linear-time algorithm on the unrestricted word RAM.

To see the implication, encode each sorted list by its length and the positive gaps between successive positions, starting just before position zero. A list of $w$ words costs $O(q+w+w\log_2(1+N/w))$ bits by gamma coding and concavity of the logarithm. Both lists together cost $o(N)$. Given this advice and a query $z$, decode two bitmaps, scan the first, and test the second at $z+x$ for each present $x$. This takes $N\,\mathrm{poly}(q)$ time. The dense-advice hitting argument under linear SAT now applies. The lists may depend on all programs that finish in the future. Their description lengths are the only nonuniform resources being charged. [Dense-advice theorem](full-cube-advice.md)

Here is an unconditional restriction on such a proposed construction. For fixed supports $U,V$, put

$$
h^*(U,V)=\max_{X,Y\ {\rm independent},\ X\in U,\ Y\in V} H(X+Y),
$$

where membership of the random variables in the sets means support containment and $H$ is Shannon entropy in bits. At any sequence of lengths witnessing the sufficient condition above,

$$
q-h^*(U,V)\ \longrightarrow\ \infty .
$$

This allows the two marginal distributions to be optimized independently at every length. It rules out unique-representation constructions of positive density, and also constructions with bounded entropy loss from collisions. I found a four-bit configuration whose tensor powers have a full sumset but lose a linear number of entropy bits for *every* choice of independent marginals. Thus uniform coverage of the cube alone cannot rule out the remaining case. I do not have lists that avoid the actual program outputs.

## Two sets with timely short descriptions

First identify the $q$ bits with the polynomial-basis representation of the field of $N$ elements. Use the first irreducible binary polynomial of degree $q$, which can be found by testing the $N$ monic candidates in $N\,\mathrm{poly}(q)$ time by modular squaring and gcds. Invert field elements with $0^{-1}=0$. Let $I_q$ be the set of elements whose inverse begins with $r$ zero bits, for a sufficiently large fixed $r$, and put $\rho=2^{-r}$. It has size $\rho N$. A plain program carries the other $q-r$ bits of the inverse, learns $q$ from its payload length, and inverts the resulting field element. Take $r$ large enough to cover the fixed compiler, a self-delimiting encoding of $r$, and two bits of savings. All members of $I_q$ then belong to $E_q$ for sufficiently large $q$.

For any $D$ of $s\ge1$ distinct shifts, let $B_D$ be the translations $b$ with $|(b+D)\cap I_q|<\rho s/2$. Uniformly over the list of shifts,

$$
|B_D|\ \le\ C_r\bigl(N/s^3+\sqrt N\bigr). \tag{1}
$$

For any $j\le6$ distinct shifts, the joint probability over uniform $b$ that all $j$ inverse prefixes vanish differs from $\rho^j$ by $O(1/\sqrt N)$. Expand the prefix indicators in additive characters. Their Fourier coefficients have sum of absolute values one. The trivial term is $\rho^j$. In every other term the trace character is applied to a sum of nonzero fractions $a_i/(b+d_i)$ on distinct poles, using the trace representation of binary field linear functionals. After cancellation this rational function has square-free denominator of degree at most six, a nonempty set of simple poles and smaller numerator degree. The complete additive character sum away from the poles has absolute value at most $(2j-2)\sqrt N+1$ by the rational-function Weil bound. The zero-inverse convention changes at most $j$ summands. [Character-sum estimate for square-free denominators, Lemma 10](https://www.cse.ust.hk/faculty/cding/JOURNALS/it061.pdf)

Write $Z_b=|(b+D)\cap I_q|$. Expand $\mathbb E_b(Z_b-\rho s)^6$. Each ordered six-tuple of shifts uses at most six distinct indicator variables. Its expectation differs by $O(1/\sqrt N)$ from that of independent Bernoulli($\rho$) indicators, by the joint estimates and idempotence of indicators. In the independent model a tuple with a singly occurring shift contributes zero. Only $O(s^3)$ tuples have no such shift, and each contributes at most one in absolute value. Hence the sixth moment is $O(s^3+s^6/\sqrt N)$. Markov's inequality at distance $\rho s/2$ gives (1).

For pairs where **both** supports are large, use the explicit multi-bit sumset extractor of Chattopadhyay and Liao. With input length $q$ and entropy parameter $\lfloor q/6\rfloor$, its output on the XOR of independent sources with at least this much min-entropy is within $q^{-\Omega(1)}$ of uniform. It supplies more than any fixed number $r'$ of bits at sufficiently large lengths. Let $J_q$ be the fiber with the first $r'$ bits zero. On uniform input it has density at most $2^{-r'}+q^{-\Omega(1)}$, since a uniform word is the sum of two independent uniform words. A name with $q-r'+1$ ordinal bits can index every member of this fiber eventually. A fixed decoder recovers $q$, scans all inputs and evaluates the explicit extractor in $N\,\mathrm{poly}(q)$ time. Taking $r'$ sufficiently large to pay for the header gives $J_q\subseteq E_q$. For any such pair of sources, $\Pr[X+Y\in J_q]\ge2^{-r'-1}$ eventually. [Chattopadhyay and Liao, Theorem 1](https://eccc.weizmann.ac.il/report/2021/147/revision/1/download/)

## Arbitrary product distributions and an exceptional set of outputs

Put $w=|U|+|V|$ and assume both sets are nonempty. For arbitrary marginal laws on $U,V$ there is a set $F$ of at most

$$
C N\bigl(\sqrt{w/N}+N^{-1/10}\bigr)
$$

words such that $\Pr[X+Y\in E_q\cup F]\ge c$ for a fixed $c>0$ on all sufficiently large sparse phases. Only the order of the atoms in each marginal matters for choosing $F$. The constants are independent of the marginals and supports.

Order one support by decreasing probability $p_1,\ldots,p_a$, and put $p_{a+1}=0$. Its law is the mixture of uniforms on the first $s$ points $D_s$ with weights $s(p_s-p_{s+1})$. This follows by telescoping at each rank. Decompose the other marginal the same way and choose the two components independently.

Take $L=\lfloor\min(N^{1/10},\sqrt{N/w})\rfloor$ and $M=\lfloor N^{1/5}\rfloor$. Include in $F$ all sums between the first $\min(L,|U|)$ points of $U$ and all of $V$, and symmetrically for $V$. This costs at most $Lw$ words. For each side and each of its initial segments $D_s$ with $L\le s\le M$, include $D_s+B_{D_s}$ in $F$. By (1), the additional cost across both sides is

$$
O_r\left(\sum_{s=L}^M (N/s^2+s\sqrt N)\right)
 =O_r(N/L+N^{9/10})
$$

when $L\ge2$. This is why the sixth moment is helpful. The union runs over *all* sizes of the nested segments of an arbitrary marginal. Combining the costs gives the claimed size bound.

If a chosen component has size below $L$, every sum belongs to $F$. If one has size between $L$ and $M$, condition on a point of the opposite component. A bad translation gives only points of $F$. Any other translation puts probability at least $\rho/2$ on $I_q$. Finally, if both sizes exceed $M$, both uniform marginals have min-entropy at least $\lfloor q/6\rfloor$ for large $q$ and the result for $J_q$ applies. Averaging gives the claim with $c=\min(\rho/2,2^{-r'-1})$.

Write $\gamma=|E_q\cap(U+V)|/N$. Every such product law puts mass at least $c$ on a set of uniform-cube mass at most $\theta=\min(1,\gamma+C(\sqrt{w/N}+N^{-1/10}))$. Grouping this set and its complement in the relative entropy to uniform gives

$$
q-H(X+Y)\ \ge\ c\log_2(1/\theta)-1 .
$$

This proves the bound even after maximizing entropy over the product laws. For uniform factors with unique sums, $H(X+Y)=\log_2|U+V|$. A constant upper bound on the normalized collision count $N\sum_z\Pr[X+Y=z]^2$ also implies $H(X+Y)\ge q-O(1)$. Both proposed mechanisms therefore fail for real time-bounded outputs.

## A power lower bound on the number of distinct easy sums

There is an unconditional lower bound that allows unbounded entropy loss. If $s=|U|\le t=|V|$, $s+t=o(N)$ and $|U+V|\ge\delta N$ for fixed $\delta>0$, then

$$
|(U+V)\cap E_q|\ \ge\ c_\delta N^{2/3}.
$$

For $U=V$ the exponent improves to $3/4$. To prove these statements, color an edge $(u,v)$ by $u+v$ and put $B=|(U+V)\cap E_q|$. First $B\ge c' t$ for a fixed $c'>0$ at sufficiently large selected lengths. Indeed $st\ge\delta N$, and $s\to\infty$ since $t=o(N)$. If $s\le N^{1/5}$, (1) bounds the fraction of bad translations in $V$ by $O_\delta(1/s^2+s/\sqrt N)=o(1)$. Otherwise the extractor applies to both sides. In either case a constant fraction of all $st$ pairs have an easy color, while any one color occurs at most $s$ times.

It remains to treat $t<N^{2/3}$ for the general result, where $s\ge\delta N^{1/3}$. Make the edges whose colors belong to $J_q$ into a bipartite graph. Every subrectangle with both sides of size at least $K_0=\lceil N^{1/6}\rceil$ has edge density at least a fixed $\alpha>0$ by the extractor property. Fewer than $K_0$ vertices per side have degree less than $\alpha/2$ times the opposite side size. Discarding endpoint pairs incident to these vertices loses at most $K_0(s+t)=o(N)$ distinct sums. Fix a representative pair $(u,v)$ with both endpoints regular for each remaining sum. Between the neighbors of $v$ and those of $u$ the same extractor gives at least $\alpha^3 st/4$ edges, hence that many length-three walks from $u$ to $v$. For fixed endpoints their ordered triples of edge colors are all different, since successive XORs from $u$ recover the interior vertices. The three colors sum to the endpoint sum, so distinct retained sums use disjoint triples. Thus $B^3\ge(\delta N-o(N))\alpha^3 st/4$, proving the bound. This uses the graph-path counting method familiar from the Balog–Szemerédi–Gowers theorem. [Fox and Sudakov, discussion of length-three paths](https://people.math.ethz.ch/~sudakovb/cycle-connected.pdf)

For $U=V$ it suffices after the first estimate to handle $s<N^{3/4}$. Here $s\ge\sqrt{\delta N}$. The graph on two copies of $U$ is symmetric. For each regular $u$, fewer than $K_0$ endpoints $v$ can have fewer than $\alpha |\Gamma(u)|/2$ common neighbors with $u$. Otherwise these endpoints and the neighborhood $\Gamma(u)$ violate the subrectangle density bound. Discard the exceptional ordered pairs and those with an irregular first endpoint. This costs at most $2sK_0=o(N)$ distinct sums. Each remaining sum has a representative with at least $\alpha^2s/4$ distinct two-edge walks. The two colors again recover the intermediate vertex and determine the endpoint sum. Therefore $B^2\ge(\delta N-o(N))\alpha^2s/4$, giving $B=\Omega_\delta(N^{3/4})$. [Path encoding and counting bounds in Lean](../lean/XorPathCounts.lean)

## Four bits separate support size from attainable entropy

Let $A=\{3,7,11,12,13,14\}$ in the four-bit XOR group. Each of the fifteen nonzero elements is the XOR of exactly one unordered pair of distinct members. In particular $A+A$ is the whole group. Let $p_i,u_i$ be any distributions on its six elements. For independent inputs their XOR law has mass $\sum_i p_i u_i$ at zero and $p_i u_j+p_j u_i$ at the nonzero label of $\{i,j\}$. Write $c_0=1/16$. This law stays at least $1/256$ in total variation from uniform.

Indeed, if the distance were smaller, every singleton probability would differ from $c_0$ by less than $c_0/16$. Consider the real matrix

$$
M= p u^\top+u p^\top-c_0{\bf1}{\bf1}^\top .
$$

It has rank at most three. Each off-diagonal entry has absolute value below $c_0/16$. Since $\sum_i 2p_i u_i<2(c_0+c_0/16)$, at most two of the six entries $2p_i u_i$ can exceed $3c_0/4$. On at least four indices the diagonal of $M$ has magnitude at least $c_0/4$. Their principal four-by-four matrix is strictly diagonally dominant and hence nonsingular, a contradiction.

By Pinsker's inequality the output entropy is at most $4-\kappa$ bits, with $\kappa=2/(256^2\ln 2)>0$. In $h$ blocks take both supports to be $A^h$. Both occupy a fraction $(6/16)^h$ of the cube and their sum is all of it. For any two independent vectors on those supports, each pair of corresponding coordinates is independent, even with arbitrary dependence between coordinates within each vector. Entropy subadditivity therefore gives $h^*(A^h,A^h)\le (4-\kappa)h$. A mixture of $m$ product laws has output entropy at most $\log_2 m+(4-\kappa)h$, so even full uniformity via such mixtures takes exponentially many components. Directly coupling the factors does achieve uniform XOR. In one block give each diagonal pair one ticket and each off-diagonal pair three tickets out of 96. Each endpoint is uniform on $A$ and each XOR has six tickets; take products of the coupling.

These particular tensor powers cover every easy word as well. What remains is to construct lists exhibiting both the entropy loss and an actual shortage of easy words among their *distinct* sums. The estimator and extractor inputs above concern real program outputs. The example only addresses the independence step in this attempted proof. Priority for the entropy obstruction at this clock is unestablished. [Lean checks of the six-point support, pair multiplicities and uniform coupling](../lean/XorPairCoverage.lean)

## A block criterion for the quadratic and cubic targets

Fix $d=2$ or $3$, take $b=\lfloor q/(1+d^2)\rfloor$ and $M=2^b$. For each $(q-b)$-bit prefix $p$, choose two subsets $U_p,V_p$ of the $b$-cube. At infinitely many $q$, suppose that

$$
\sum_p (|U_p|+|V_p|)=o(N),\qquad
S=\{p\mathbin\Vert z:\ z\in U_p+V_p\},\qquad
|S|\ge\delta N,\quad |S\cap E_q|=o(N)
$$

for some fixed $\delta>0$. Then explicit SAT has no deterministic $O(n^d)$ algorithm on the specified RAM. The suffixes occupy one fifth of the bits for the quadratic test and one tenth for the cubic test. The collections of lists at different prefixes can be unrelated. This version uses the same auxiliary language and deadline as the linear test.

The extra saving for these sets comes from checking an **entire** advised truth table in $M\,\mathrm{poly}(q)$ time. Decode the two suffix lists into bitmaps $f,g$. Their integer XOR convolution counts the representations of each possible sum. Apply the unnormalized Walsh transform to each array, multiply the transformed arrays coordinatewise, apply the same transform again and divide each entry by $M$. Orthogonality of the parity characters gives exactly the convolution. Each transform has $b$ butterfly stages and $O(Mb)$ additions. Intermediate magnitudes are at most $M^3$ and hence have $O(q)$ bits. This bounds construction and verification time for arbitrary supplied advice. Reject malformed codes within the same clock. [Walsh convolution and butterfly counts in Lean](../lean/XorButterflies.lean)

Under the supposed $O(n^d)$ SAT algorithm, use the [suffix-table selection construction](suffix-block-sat-exponents.md) with all valid list-pair codes of length at most $\eta M$. It finds one common suffix set $H$ of size $M/2^a$ hitting every such sumset of density at least $\delta/2$ in more than $\delta |H|/4$ elements. Choose a large fixed header reserve $a$ and a sufficiently small $\eta$ computed from $a,\delta$. For a supplied $H$, one guessed advice string suffices to demonstrate a violation, because the convolution checks all inputs deterministically. This takes $M^d\mathrm{poly}(q)$ deterministic time under the SAT assumption. Guessing a qualifying completion of a partial $H$ takes a second SAT simulation, giving $M^{d^2}\mathrm{poly}(q)$ deterministic time per call. After $M$ calls the least table is recovered in $M^{1+d^2}\mathrm{poly}(q)\le N\,\mathrm{poly}(q)$. Every $p\mathbin\Vert h$ for $h\in H$ has a short plain name by carrying the unrestricted prefix and an ordinal into $H$. Thus these are actual members of $E_q$.

Encode local list sizes in $O(q)$ bits per block and use the gap bound above within each suffix cube. The combined advice length is $o(N)$ by concavity: the mean of $w_p/M$ tends to zero, and the per-block fractional cost is $O(q/M+(w_p/M)(1+\log_2(1+M/w_p)))$, taking the variable part as zero at $w_p=0$. Blocks exceeding the $\eta M$ cap therefore occupy $o(N)$ addresses. For all sufficiently large selected $q$, a fixed positive fraction of all blocks are within the cap and have density at least $\delta/2$. The common hitting set supplies $\Omega(N)$ easy words in their union. This contradicts the proposed lists and proves the criterion.

There is also an unconditional test of the local premise. In each suffix dimension construct the two easy families $I_b$ and $J_b$ from the first part. A plain decoder can carry the untouched prefix and the compressed suffix. It infers $q$ from its payload length plus a fixed offset, computes $b$, and splits the payload accordingly. Each family has a fixed offset and $b\to\infty$; its reconstruction takes only $M\,\mathrm{poly}(q)$ time, within $T$. The same entropy inequality holds for every block with these uniform constants, using the density of *all* true easy words in the block sumset in place of $\gamma$. If the block premise holds, then for all but a vanishing fraction of prefixes, both the normalized list sizes and the normalized number of easy sums tend to zero in probability over prefixes. More precisely, some sequence $\omega(q)\to\infty$ satisfies $b-h^*(U_p,V_p)\ge\omega(q)$ outside $o(N/M)$ blocks with nonempty lists, by Markov's inequality applied to the two normalized totals. Empty sumsets contribute no coverage. Consequently a positive fraction of prefixes must combine a dense support with a diverging loss of optimized entropy. No construction in this journal achieves that on the program-defined hard words.

On the positive fraction of dense blocks whose combined list size is a vanishing fraction of the block, the path bound gives at least a constant times $M^{2/3}$ easy words per block. The estimates are uniform under these density and sparsity bounds, since the small-side error in (1) depends only on their sizes. Summing gives at least $\Omega_\delta(N/M^{1/3})$ easy words in the global set. In the cubic criterion this is $\Omega_\delta(N^{29/30})$. If the two dictionaries agree in each block, the corresponding exponents are $N/M^{1/4}$ and $N^{39/40}$. Each bound is compatible with $o(N)$ errors.
