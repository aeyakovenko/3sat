# Why charging a scale index to the payload can lose the accuracy guarantee

**Research journal, 24 November 2026.** Suppose a decoder distributes its available fraction $\beta$ of short programs over $m$ possible histogram grids. At grid $j$ it receives fraction $\beta w_j$, with $\sum_jw_j\le1$. The allocation argument at that grid then tests forecasts at error proportional to $\beta w_j$. Abstract histograms can resist every short description at error proportional to $\sqrt{w_j}$ simultaneously. In particular, for equal weights these errors are of order $m^{-1/2}$, yet representing a grid explicitly has reduced the available tolerance to order $m^{-1}$. The following finite bounds also address selecting a grid from the phase parameter alone.

## A finite construction

Start with a cell of mass one. At level $j$ let there be $K_j$ equal-width cells, each parent having the same even number $b_j=K_j/K_{j-1}$ of children, with $K_0=1$. Put $a_j=\sqrt{w_j}/2$. Within each parent of mass $u$, pair its children. In every pair independently choose which child receives mass $(u/b_j)(1+a_j)$ and which receives $(u/b_j)(1-a_j)$. All parent masses are preserved.

For a uniformly chosen cell write $D_j=K_j$ times its mass. Its mean is one. For every realization of the orientations, averaging over the two members of each pair gives
$$
\mathbb E D_j^2=\prod_{i\le j}(1+a_i^2)\le e^{1/4}<4/3.
$$
Thus at least $3/16$ of the parents at each level have $D_{j-1}\ge1/2$. Indeed these parents carry at least half of $\mathbb E D_{j-1}$, and Cauchy–Schwarz bounds the square of this mass by their fraction times $\mathbb E D_{j-1}^2$. They contain $N\ge3K_j/32>K_j/12$ independent pair orientations.

Fix **all coarser orientations** before deciding which parent pairs to test. Given this history, permit any list of fewer than $2^{1+K_j/256}$ forecast vectors specified from the history. This covers a fixed decoder with arbitrary binary advice of length at most $\lfloor K_j/256\rfloor$, even with the entire coarse history supplied free. For one forecast, use its order within each tested pair, breaking ties deterministically, to predict the larger true entry. The probability of getting at most $N/4$ orientations wrong is at most $2^{-N(1-H(1/4))}\le2^{-N/6}$. Each wrong orientation costs at least $2a_jD_{j-1}/K_j\ge a_j/K_j$ in $\ell_1$ distance because it reverses the order of two entries whose true values differ by this amount. For $w_j>0$ the conditional probability that any forecast has error less than $\sqrt{w_j}/96$ is therefore at most $2^{1-K_j/128}$. For $w_j=0$ the claimed lower bound is automatic.

If $\sum_j2^{1-K_j/128}<1$, a single realization has the lower bound at every level. This holds in the regime $K_{\min}\ge q^{1/4}/2$ and $m=O(\log q)$ for all sufficiently large $q$. The flat refinement of the *exact* preceding histogram has error exactly $a_j$, so the square-root scale is also an upper bound with this side information. For the equal split $w_j=1/m$, the lower bound eventually exceeds $C\beta/m$ for every fixed $C,\beta>0$, even with many more than $o(K_j/m)$ advice bits allowed.

Multiplying every mass by $1/4$ gives total mass strictly below the interpreter budget of $1/2$, with all error bounds scaled by $1/4$: multiply any forecast by four when applying the original counting argument. Integer cell counts can be imposed with an additive loss. Round each finest-cell mass downward to a multiple of $2^{-q}$. The error of every coarser histogram is less than $K_m2^{-q}$. A rounded coarse mass is determined by its unrounded mass and the fixed remaining branch counts and amplitudes: swapping orientations only permutes the multiset of descendant masses. A decoder supplied these rounded ancestors is consequently covered by the same conditioning argument.

## The scale can defeat every selector in a countable list

Let $m=m(q)\to\infty$, the smallest $K_j$ grow as above, and $\min_j b_j\to\infty$. Fix phase-to-level functions $f_1,f_2,\ldots$. At phase $q$ target the first $\lfloor\sqrt{m}\rfloor$ functions, assigning level $j$ the weight
$$
w_j=\sum_{\ell\le\sqrt m:\ f_\ell(q)=j}2^{-\ell}.
$$
For every fixed $\ell$, the selected level $f_\ell(q)$ has error at least $2^{-\ell/2}/96$ against the specified short-description family at all sufficiently large phases. Meanwhile all but at most $\sqrt m$ levels are exact flat refinements. Each unmarked level has an $o(K_j)$-bit approximation with $o(1)$ error even **without** free ancestors. For example, round its parent masses downward in units of $1/(K_{j-1}b_j)$ and encode the resulting nonnegative integer vector of sum at most $K_{j-1}b_j$. Stars and bars needs at most $\log_2\binom{K_{j-1}(b_j+1)}{K_{j-1}}+1=O(K_{j-1}\log(b_j+1))$ bits, and flat refinement preserves the error bound $1/b_j$. A grid index, if needed by the reconstruction, takes $O(\log m)$ further bits in the stated regime.

The sequence constructed here can depend on the entire list of selectors. Its role is to separate the two quantifier statements. Nearly every grid can be compressible at every phase while each prescribed uniform selector eventually chooses an incompressible one. The construction specifies abstract cell masses. It supplies neither a native machine realizing those masses as actual halts nor a refutation of an allocator that reuses the same names across grids. Fine details of a genuine earlier halting trajectory can contain information about still-unrevealed bins. The forecast count above conditions only on coarser orientations and evaluates whole-vector reconstructions.
