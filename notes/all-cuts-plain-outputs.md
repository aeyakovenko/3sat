# Dense rectangle unions contain short program outputs across every balanced cut

**Research journal, 24 November 2026.** Let $E_q$ consist of the $q$-bit words printed by a plain program of at most $q-2$ bits on the fixed universal RAM by time $T(q)=2^q(q+2)^{\lceil\log_2(q+2)\rceil}$. We construct one subset of $E_q$ whose density inside every large disjoint union of balanced rectangles is close to its density in the cube. Each rectangle may use a different partition of the input coordinates and arbitrary advice. This gives an unconditional restriction on the proposed dense masks for the linear SAT target. The connection to unrestricted circuits or a RAM lower bound remains open. [Plain-program conventions and the SAT criterion](full-cube-advice.md)

Write $N=2^q$, $m=\lfloor q/2\rfloor$ and $n=q-m$. There is a fixed integer $r$ such that for all large $q$ there is a set $H_q\subseteq E_q$ with the following simultaneous guarantee. Put $t=\lceil\sqrt{q+r+4}\rceil$. For every disjoint union $S$ of $L\ge1$ rectangles, each with sides on some $m$ and $n$ coordinates,

$$
\left||H_q\cap S|-2^{-r}|S|\right|
 \ \le\ N\sqrt{L\,2^{-(m-t)}}.
$$

In particular, fix $\delta>0$. If $|S|\ge\delta N$ and $|S\cap E_q|=o(N)$ along a sequence of lengths, then $\log_2 L\ge m-t-O_{\delta,r}(1)$ there. A deterministic communication protocol of cost $c$ partitions its accepting inputs into at most $2^c$ disjoint rectangles. Thus the membership predicate of such a mask needs at least $\lfloor q/2\rfloor-O(\sqrt q)$ bits of worst-case communication on **every** balanced partition. This applies pointwise to each successful mask of a randomized generator. The result concerns the communication needed to recognize a mask once chosen. Multipartition rectangle approximation and random graph cut-rank have an established literature. [Rectangle approximation](https://doi.org/10.1016/S0304-3975(02)00568-6) · [Lee, Lee and Oum on random graph cut-rank](https://arxiv.org/abs/1001.0461)

## Simultaneous ranks within the output clock

Label each unordered pair $i<j$ by a vector $\ell_{ij}\in\mathbb F_2^r$ and put $Q(x)=\sum_{i<j}\ell_{ij}x_ix_j$. For a cut and a nonzero $\lambda\in\mathbb F_2^r$, form the $m$-by-$n$ matrix of $\lambda\cdot\ell_{ij}$ across the cut. With independent uniform labels this matrix has independent fair entries. A particular $t$-dimensional subspace of its left kernel occurs with probability $2^{-nt}$. There are at most $4\cdot2^{t(m-t)}$ such subspaces, by counting ordered bases and using $\prod_{j\ge1}(1-2^{-j})>1/4$. For the latter elementary bound multiply the first two factors and bound the remaining product below by $1-\sum_{j\ge3}2^{-j}$. The expected number of tests with kernel dimension at least $t$ is at most $2^{q+r}\cdot4\cdot2^{-t^2}<1$ for all large $q$.

Set labels in order of their lesser endpoint, then their greater endpoint. At each position choose a label minimizing the conditional expected number of failing tests, breaking ties in binary order. The final number of failures is zero. The computation must spend only $\mathrm{poly}(q)$ per cut at each decision to meet the clock. The order above ensures that, in every individual cut matrix, all entries of some initial rows and initial columns have been set. At most one additional row or column has further assigned entries. Unset entries for that test are still independent fair bits.

First suppose that $a$ complete rows and $b$ complete columns have been set in an $m$-by-$n$ matrix, with their overlap $P$. Write $p=\operatorname{rank}P$, $u$ for the rank of the complete rows and $v$ for the rank of the complete columns. The final rank has the distribution

$$
 u+v-p+\operatorname{rank}U,\qquad
 U\text{ uniform of dimensions } (m-a-v+p)\times(n-b-u+p).
$$

Apply Gaussian elimination to the overlap, obtaining $p$ pivots. The remaining fixed rows on the right have rank $u-p$ and the remaining fixed columns below have rank $v-p$. Change bases within the bottom rows and right columns to isolate these two sets of pivots. The corner was uniform and independent of those fixed matrices. These invertible changes and the fixed shifts from the overlap pivots preserve its uniform distribution. Clearing the two sets of pivots drops $v-p$ rows and $u-p$ columns from the corner, leaving exactly $U$. Its rank law is computed one uniform row at a time. A row lies in a given $j$-dimensional span in width $w$ with probability $2^{j-w}$.

For an additional partially set row, let $D$ be its specified coordinate set, including all $b$ complete columns. Let $W$ be the span of the previous complete rows and $\pi_D$ the coordinate projection. Among the $2^{n-|D|}$ possible completions, exactly $2^{u-\dim\pi_D(W)}$ belong to $W$ if the specified values lie in $\pi_D(W)$, and zero do otherwise. Both tests use Gaussian elimination. Treat the row as complete, with $a$ increased by one. The enlarged overlap rank is known from its fixed first $b$ entries, and the rank $v$ of all complete columns stays fixed. The new top rank is $u$ or $u+1$ with the probabilities just computed. In each case the corner law in the display depends only on these ranks, so taking this two-term mixture accounts for all completions. Transposition handles a partial column.

All probabilities are dyadic with denominators dividing $2^{mn}$, since they count completions of a single binary test matrix. Sums over tests add only $O(q+r)$ numerator bits. Enumerating at most $2^q$ cuts, $2^r-1$ characters and $2^r$ candidate labels at $O(q^2)$ positions therefore costs $2^q\mathrm{poly}(q)$ for fixed $r$. The independent exhaustive check compared the computed rank distributions with every binary completion for 7,871 partial assignments and specifications in dimensions from $1\times1$ through $3\times3$. [Run the finite check](../audits/partial_rank_experiment.py)

## Rectangle discrepancy and plain names

Use $H_q=\{x:Q(x)=0\}$ with the labels constructed above. In a split $x=(y,z)$ each nonzero character of $Q$ has sign matrix $(-1)^{y^\top Bz}$ up to individual row and column signs. If $B$ has rank $h$, two rows of this matrix have inner product zero unless their difference belongs to the left kernel, in which case the inner product before applying signs is $2^n$. Grouping the rows into left-kernel cosets gives operator norm $2^{(q-h)/2}$. Every tested $B$ has $h\ge m-t$. Expanding the zero-fiber indicator in characters, the discrepancy of a rectangle $R$ from $2^{-r}|R|$ is bounded by $2^{(q-m+t)/2}\sqrt{|R|}$. Sum over disjoint rectangles and use $\sum_R\sqrt{|R|}\le\sqrt{L N}$ to obtain the stated bound.

Taking the whole cube as one rectangle gives $|H_q|\le(1+o(1))2^{q-r}$. Each member can therefore be specified by a raw ordinal of $q-r+1$ bits. A fixed decoder reads a self-delimiting constant $r$, infers $q$ from the remaining program length, constructs the labels, scans the cube and prints the member with the given ordinal. The scan costs $2^q\mathrm{poly}(q)$. Choose $r$ large enough to cover the fixed interpreter header, its own $O(\log(r+2))$-bit encoding and three further bits. These plain names then have length at most $q-2$. Native simulation still takes $2^q\mathrm{poly}(q)$ time, eventually within $T(q)$. This establishes $H_q\subseteq E_q$ on the stipulated interpreter without assuming a SAT algorithm.
