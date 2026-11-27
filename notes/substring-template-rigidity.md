# When shared row substrings imply low rank for the fixed output table

**Research journal, 24 November 2026.** Use the actual last-bit table of the bounded candidate-selection program at cutoff zero for the lower endpoint. For the linear hypothesis let its side be $s=L$. For the quadratic and cubic hypotheses examine the local side $s=J$ before tiling. If a solver of the respective claimed complexity exists, the local table eventually equals $R_s$, the row-major lexicographically first binary matrix at distance greater than $E=\lfloor s^2/16\rfloor$ from every binary matrix of rank at most $r=\lfloor s/16\rfloor$. All cells count. The following sufficient condition only refers to the program's actual bits. [Fixed program and candidate-selection theorem](fixed-program-parity.md)

## Reusing windows of a few binary strings

Suppose changing $e$ entries of a binary $s$-by-$s$ table makes each row a contiguous length-$s$ window of one of $g$ binary strings, each of length $2s-1$. Different rows may choose the same window. Fix $0<\eta<0.01$. For all sufficiently large $s$, the original table can be approximated over $\mathbb F_2$ with

$$
\mathrm{rank}\ \le g\,s\exp\bigl(-\eta^6(\log s)^{0.35}\bigr),
\qquad
\mathrm{Hamming\ error}\ \le e+s^{1+15\eta}.
$$

For a template $w$ the window matrix has entries $w_{a+j}$, with $0\le a,j<s$. Reversing the column order gives a Toeplitz matrix. Theorem 7.27 of Dvir and Liu gives the stated rank bound with $g=1$ after changing at most $s^{15\eta}$ entries **per row** and per column of that matrix. Undo the reversal, then for each output row copy the approximant row corresponding to its chosen template and start. The assembled row space is contained in the sum of the $g$ approximant row spaces. Each chosen row carries at most $s^{15\eta}$ new errors even if many copies use the same start. The original $e$ discrepancies add by the triangle inequality. More precisely the contribution to rank of a template assigned $a$ rows is at most the smaller of $a$ and the single-template rank bound. [Dvir and Liu, Definition 1.3 and Theorem 7.27](https://theoryofcomputing.org/articles/v016a020/v016a020.pdf)

For example, take $\eta=1/200$. If $e\le s^2/32$ and $g\le\exp(\eta^6(\log s)^{0.35})/32$ on arbitrarily large actual phases, the rank is at most $r$ and the error at most $E$ eventually. This would exclude the corresponding claimed SAT time. No algorithm has to find the templates. The test for the stronger exponents concerns the local table. An approximation of the large tiled table needs separate bounds at the local side.

## What the canonical matrix already shares

At least $s-\lceil s/3\rceil$ initial rows of $R_s$ are zero for all sufficiently large $s$. To see this, put $k=\lceil s/3\rceil$ and allow just the last $k$ rows to vary. A rank-$r$ or lower $k$-by-$s$ approximant can be specified by two factors in $r(k+s)$ bits. The union of all its radius-$E$ Hamming balls on the suffix has size at most

$$
2^{r(k+s)+ksH_2(E/(ks))},
$$

where $H_2$ is binary entropy. The base-two log of this quantity divided by $s^2$ approaches $1/12+H_2(3/16)/3<0.316$, below $ks/s^2\to1/3$. Some suffix evades all approximants. Appending it after zero rows is rigid on the whole square, since restriction preserves the rank upper bound and can only decrease the error. Lexicographic minimality gives the claimed shared prefix of zero rows.

Two further constraints describe the remaining work. If $m$ rows of $R_s$ are nonzero then $m>r-1+2E/s$ for large $s$. Indeed $m\ge r$, and a row space spanned by the all-ones word and $r-1$ chosen nonzero rows represents these rows exactly. Every other nonzero row lies within $s/2$ of either zero or all ones. Also, the distance of $R_s$ to rank at most $r$ is **exactly** $E+1$. Clearing any one of its one-entries gives an earlier matrix within $E$ of some rank-$r$ or lower matrix. That approximant is at distance $E+1$ from $R_s$ and disagrees at the cleared entry. These facts give one actual template for many complete rows, conditional on the candidate selecting a correct solver. They give no sufficiently small dictionary for the remaining rows. The distance calculation misses the exclusion threshold by one entry.

## A fast rank-$O(\log s)$ table can resist many templates

Let $b=\lceil(3/2)\log_2s\rceil$. Greedily take the first $s$ allowable binary words of length $b$ in integer order. After taking a word, forbid the Hamming ball of radius $t=\lceil b/32\rceil-1$ around each of its $b$ cyclic rotations. Any two chosen words have distance at least $b/32$ under every relative rotation. With $V_b(t)=\sum_{i=0}^t\binom bi$, the number forbidden in $s$ rounds is at most $sbV_b(t)$. This is less than $2^b$ for all sufficiently large $s$, since $V_b(t)\le2^{H_2(1/32)b}$, $H_2(1/32)<0.201$ and $s\le 2^{2b/3}$.

Form row $i$ by periodically repeating seed $i$ and truncating to $s$ bits. This table has rank at most $b$ because columns with the same residue modulo $b$ coincide. A fixed RAM can construct it in $s^2\,\mathrm{poly}(\log s)$ time. Initialize a forbidden array of length $2^b=O(s^{3/2})$, scan candidates once, and for each chosen seed and rotation enumerate the masks of weight at most $t$ by listing their sets of positions. This costs $O(sbV_b(t)\,\mathrm{poly}(b))$ for marking. Reading off or printing all entries fits the claimed clock. Computing $b$ takes integer comparisons of $2^{2b}$ with $s^3$.

**Two accurately matched rows per template.** In one length-$(2s-1)$ word, three selected windows have two starts at distance at most $(s-1)/2$. Their overlap has length at least $s/2$. Two different chosen periodic rows disagree on such an overlap in at least $\lfloor s/(2b)\rfloor b/32$ places, at whatever phases the starts induce. This exceeds $s/128$ for sufficiently large $s$. If both rows were within $s/256$ edits of their respective windows, their disagreement there would be at most $s/128$. Thus with $e$ total edits one needs at least $(s-256e/s)/2$ templates. Exact matches require at least $s/2$ templates. With $o(s^2)$ total errors the lower bound is $(1/2-o(1))s$.

**At the full $s^2/16$ tolerance.** A constant-fraction per-row bound of $s/256$ alone would not settle this case. If at most $s^2/16$ edits are made, at least $s/4$ rows differ from their chosen windows in at most $s/12$ positions. Partition each template from its beginning into disjoint $b$-bit chunks, dropping a possible final partial chunk. A good window contains at least $s/b-2$ full chunks. At most $(s/12)/(b/8)$ of these can have more than $b/8$ errors. For $s\ge24b$, at least $s/(4b)$ chunks therefore match a rotation of the row seed to within $b/8$ errors. Each chunk can do this for at most $bV_b(\lfloor b/8\rfloor)$ distinct seeds by counting Hamming neighbors and rotations. Counting incidences over fewer than $2s/b$ full chunks in one template bounds its number of good rows by $8bV_b(\lfloor b/8\rfloor)$. Consequently

$$
g\ \ge\ \frac{s}{32bV_b(\lfloor b/8\rfloor)}
\ =\ \Omega\!\left(\frac{s^{1-(3/2)H_2(1/8)}}{\log s}\right).
$$

The exponent exceeds $0.1846$. This estimate even holds for any $s$ distinct period-$b$ seeds. The extra separation of their rotations supplied the two-row bound above. Thus a fixed fast program may have exact rank logarithmic in the side and still require polynomially many templates at the full allowed error. Establishing sufficient window sharing for the candidate-selection program requires a property specific to its computation.

Both row and column tests can fail on the same table. For the periodic matrix $P$ above, the symmetric block matrix $\bigl(\begin{smallmatrix}0&P\\ P^{\mathsf T}&0\end{smallmatrix}\bigr)$ of side $2s$ has rank at most $2b$. Restricting a row approximation to the upper-right block preserves at most its total errors, and each outer length-$(4s-1)$ template induces three length-$(2s-1)$ templates for the restricted windows, obtained at starts $0,s,2s$, covering all possible inner starts $0,\ldots,3s-1$. Thus $o(s^2)$ edits still require $\Omega(s)$ outer templates by the two-row bound, and symmetry gives the same conclusion for column approximations.

The simultaneous obstruction also holds at the full outer tolerance. Put $P$ in both diagonal blocks and $P^{\mathsf T}$ in both off-diagonal blocks of a side-$2s$ matrix. Its rank is at most $4b$ by subadditivity. With at most $(2s)^2/16$ errors, one of the two $P$ tiles has at most $s^2/8$ errors for a row approximation. For a column approximation, transposition gives two $P$ tiles in the off-diagonal positions and the same bound applies. In either selected tile at least $s/9$ rows have at most $9s/64$ errors. Each contains at least $s/b-2-(9s/64)/(b/6)\ge s/(8b)$ aligned chunks within $b/6$ errors of a rotation when $s\ge64b$. Each inner template consequently fits at most $16bV_b(\lfloor b/6\rfloor)$ such rows. The three inner templates per outer template give, for each orientation separately,

$$
g\ \ge\ \frac{s}{432bV_b(\lfloor b/6\rfloor)}
\ =\ \Omega\!\left(\frac{s^{1-(3/2)H_2(1/6)}}{\log s}\right).
$$

The exponent is approximately $0.0249664$. The row and column approximations may choose different templates and different edit sets.

**Finite check.** At sides 128, 256 and 512 the lexicographic scan produced the requested 128, 256 and 512 seeds with respective widths 11, 12 and 14. The minimum distance over all rotations of all distinct pairs was one in each case, as permitted by these short widths. As a check on the one-entry boundary, an exhaustive four-by-four example with rank cutoff one and error cutoff one gave first qualifying row-major string `0000000000110101`. Its nearest rank-one-or-lower distance is two, and clearing any one brings that distance to one. [Run the finite checks](../audits/substring_template_experiment.py)
