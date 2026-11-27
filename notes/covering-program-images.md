# Can a small collection of lists cover the words that programs actually print?

**Research journal, 24 November 2026.** The [XOR construction](xor-sumset-advice.md) sought a positive-density set of hard words directly. I tested the reverse construction. Cover almost every actual short-program output, leave a positive fraction of the cube uncovered, and describe the cover by sets of pairwise XORs. Overestimates of the program image are allowed. Their total size has to leave enough room for the uncovered set.

Keep $N=2^q$, the cutoff $T=2^q(q+2)^{\lceil\log_2(q+2)\rceil}$, and $E_q$ the actual $q$-bit outputs of plain programs of length at most $q-2$ by $T$. Suppose a collection of pairs of finite word lists $(U_i,V_i)$ has total binary encoding length $o(N)$ on infinitely many $q$ and satisfies

$$
\sum_i |U_i||V_i|\le (1-\delta)N,\qquad
\left|E_q\setminus\bigcup_i(U_i+V_i)\right|=o(N)
$$

for a fixed $\delta>0$. Use an ordinary uniform list encoding, for example a count, two lengths per pair and raw $q$-bit entries. The covered set contains at most the stated number of pairs. Its complement therefore has density at least $\delta$. Given the advice, a fixed verifier first totals the Cartesian sizes with saturation at $N+1$, returning an empty acceptance mask on invalid advice or overflow. It can then scan every pair to recognize the complement in $N\,\mathrm{poly}(q)$ time. This would exclude linear SAT by the [full-cube advice bound](full-cube-advice.md). Neither the list entries nor the choice of the decomposition need to be efficiently computable.

For the $O(n^d)$ target with $d=2$ or $3$, take the final $b=\lfloor q/(1+d^2)\rfloor$ bits as the suffix, and $M=2^b$. Supply a local collection of suffix-list pairs for each prefix. Suppose the total encoded length is $o(N)$, the total number of pairs in the Cartesian products over all prefixes is at most $(1-\delta)N$, and only $o(N)$ easy words escape their local covers. Then $O(n^d)$ SAT is impossible. In a block with Cartesian pair count $l\le M$, enumerate the local sums once into an $M$-bit array and return its uncovered positions. For larger counts return the empty mask. The sum of the returned mask sizes is at least $\sum_p(M-l_p)_+\ge\delta N$. Parsing capped advice and producing a whole returned mask cost $M\,\mathrm{poly}(q)$. The two SAT eliminations and $M$ completion queries in the suffix-table construction apply to this verifier. As usual, the blocks whose local advice exceeds a fixed positive fraction of $M$ occupy $o(N)$ positions. Actual escaping easy words bound the false positives in the retained blocks. [Suffix clock proof](xor-sumset-advice.md)

## A sufficient decomposition on actual program inputs

For the linear version, consider a proposed partition of program inputs of each length into rectangles $A_i\times B_i$ in two groups of payload bits. Include the length or branch in the rectangle identifier when partitioning multiple program lengths. Suppose that except for $o(N)$ distinct easy words, each easy word has at least one producing input in these rectangles whose output can be written $g_i(a)+h_i(b)$. Try assigning one $q$-bit value to each row and one to each column. Use their image lists as $U_i,V_i$. Disjoint rectangles inside the short program domains satisfy

$$
\sum_i |A_i||B_i|\le \sum_{\ell=0}^{q-2}2^\ell=N/2-1 .
$$

For instance, if every nonempty rectangle has both sides of size at least $l(q)$ with $l(q)/q\to\infty$, then $\sum_i(|A_i|+|B_i|)\le N/l(q)$. Raw $q$-bit entries and list framing cost $o(N)$ in all. Timeouts can be overestimated for free within the pair-count bound. This gives an explicit hypothesis about the images of authentic computations to try to prove.

## Where pointwise separation fails

One genuine interpreter branch already rules out an argument that requires separability on most *programs* in large rectangles of a given split. A fixed native program accepts two $m$-bit payloads $a,b$. Over the field of $2^m$ elements it prints $a\mathbin\Vert ab$ with a constant number of leading zeros. Choose the padding greater than the compiler header length plus two, giving eligible program lengths on the corresponding output lengths. A polynomial basis can be found by deterministic enumeration in $2^m\mathrm{poly}(m)$ time. For $a\ne0$ all outputs on this branch are distinct, and the branch then has a constant times $N$ outputs.

On distinct rows $a,a'$ and columns $b,b'$ the XOR of the four product coordinates is $(a+a')(b+b')\ne0$. For any proposed row and column functions the four modeled values have XOR zero. Thus the graph of cells where the actual and modeled outputs agree contains no four-cycle. On a rectangle of $u$ rows and $v$ columns, if $e_j$ cells agree in column $j$ and $e=\sum_j e_j$, then $\sum_j\binom{e_j}{2}\le\binom u2$. Cauchy–Schwarz gives $e^2/v-e\le u(u-1)$, hence $e\le v+u\sqrt v$. The symmetric bound holds as well. On rectangles with both sides tending to infinity the modeled fraction tends to zero uniformly. Choosing unrestricted row and column values separately for each tile cannot fix the pointwise split. [Classical four-cycle count, Kővári, Sós and Turán](https://www.impan.pl/en/publishing-house/journals-and-series/colloquium-mathematicum/all/3/1/94006/on-a-problem-of-k-zarankiewicz)

Yet this same branch has an inexpensive **image cover**. Use one list for the possible first field coordinate and one for the possible second coordinate, occupying disjoint groups of output bits. Their XORs cover the entire padded $2m$-bit cube, including the few unused outputs with $a=0$. There are only $2^{m+1}$ list entries and exactly $2^{2m}$ pairs. This pays just the branch's raw input capacity. The example gives a reason to look for covers of images that allow a different pairing of the inputs and outputs. I have no construction within the required total description and capacity budgets for the full interpreter.

## Choosing the separation rule separately for each pair

A second actual branch outputs the two field elements $(ab,a^2b)$ with the same padding. On nonzero input pairs it is injective, since the ratio of the second coordinate to the first recovers $a$. Let $Q=2^m$ and allow the predictor to choose, separately at each input, whichever of $R$ proposed models $g_j(a)+h_j(b)$ agrees. Even with this freedom it covers only an $O(R Q^{-2/3})$ fraction of the branch's inputs.

For one fixed model its bipartite agreement graph has neither a four-cycle nor a six-cycle. On a simple cycle with $k=2$ or $3$ distinct left vertices $a_i$ and distinct right vertices $b_i$ in cyclic order, the XOR of all modeled edge outputs vanishes. Writing $c_i=b_i-b_{i-1}$ cyclically, the two actual coordinates give $\sum_i a_i c_i=\sum_i a_i^2c_i=0$, and $\sum_i c_i=0$ by telescoping. The first $k$ power equations form an invertible Vandermonde matrix. This forces all $c_i=0$, impossible on the cycle. A bipartite graph on $2Q$ vertices with these two cycle lengths absent has $O(Q^{4/3})$ edges. If it has $e$ edges, pruning vertices of degree below $e/(4Q)$ leaves a nonempty subgraph of at least that minimum degree. The ball out to distance three from any vertex of that subgraph has no path collisions that would form a four- or six-cycle. Its size is at least $1+D+D(D-1)+D(D-1)^2$ for minimum degree $D\ge2$. This is at most $2Q$, giving the bound on $e$. Sum over the $R$ models. Agreement on a constant fraction thus needs at least $q/3-O(1)$ bits to select a model when $q=2m+O(1)$. The same two-coordinate image cover as before still works.
