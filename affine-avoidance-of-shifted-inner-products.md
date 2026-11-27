# Exact affine query depth for avoiding shifted inner products

A single indexed function gives an unconditional partial result toward the infinite-hit condition for range avoidance. For a $d$-bit vector $u$ and a $(d+m-1)$-bit vector $v$, where $1\le m\le d$, form the $m$-bit output with coordinates
$$
H_h(u,v)=\sum_{i=0}^{d-1}u_i v_{i+h}\pmod 2,\qquad 0\le h<m .
$$
Consider a deterministic algorithm returning any $m$-bit string different from $H(u,v)$ on every input. It may test affine binary forms on the full input and return arbitrary affine functions of the input at its leaves. **Its optimal depth is exactly $d-m+1$, and every run of every correct tree uses at least that many tests.** Every point belongs to an affine slice of this exact codimension where a common affine answer succeeds. Allowing a query to return $w$ arbitrary affine bits changes the optimum to $\lceil(d-m+1)/w\rceil$ queries.

## How many matches survive an affine transcript?

Write $n_0=2d+m-1$. For every affine flat $S$ of codimension $r$ in the $n_0$ input bits and every affine output $L$ on $S$,
$$
|\{x\in S:H(x)=L(x)\}|\ \ge\ |S|2^{-m}\bigl(1-(2^m-1)2^{r-d}\bigr).
$$
When $r\le d-m$ the right side is positive. This includes affine outputs that vary freely on the surviving flat.

For every nonzero $\lambda\in\mathbb F_2^m$, the scalar $\lambda\cdot H$ is a bilinear form whose matrix has row rank $d$. A linear combination of its $d$ rows with coefficients $b_i$ is the coefficient vector of the product of the binary polynomials $\sum b_iX^i$ and $\sum\lambda_h X^h$. The range of $v$ indices includes every coefficient of this product. Its vanishing forces all $b_i$ to vanish. Averaging the sign of the bilinear form plus any affine phase first over $v$ leaves at most one value of $u$ with a nonzero contribution. Every such correlation has absolute value at most $2^{-d}$ under uniform input.

Extend $L$ affinely from $S$ to the ambient space. The indicator of $S$ is an average of the $2^r$ signed characters of its defining linear equations. Multiplying by this indicator bounds the full-cube average of the sign of $\lambda\cdot(H+L)$ on $S$, with zero outside, by $2^{-d}$. Conditioning on $S$ costs $2^r$. Expand the indicator that the vector $H+L$ is zero as the average of its $2^m$ characters. The trivial character gives one and the others give the claimed error. The use of correlation bounds to obtain dispersion on varieties is classical, and the journal already uses a scalar inner product to charge affine measurements on actual SAT runs. [Golovnev, Kulikov and Williams, Lemma 5.4](https://eccc.weizmann.ac.il/report/2018/192/revision/2/download/) · [Earlier scalar SAT bound](affine-guards-for-writable-memory.md)

## A matching affine answer through each point

Test $u_0$ and all $d-m$ coordinates $u_i$ with $i\ge m$. From the answers choose $c_i=u_i$ for $i\ge m$, $c_i=0$ for $1\le i<m$, and $c_0=1+u_0$. On this whole slice $z=u+c$ has $z_0=1$ and is supported in positions $0,\ldots,m-1$. Return the affine output
$$
L_h(v)=H_h(c,v)+v_{2h}+[h=0].
$$
All indices $2h$ are in range. The row sum of pairwise products is symmetric, so in characteristic two its off-diagonal terms cancel. In detail,
$$
\sum_{h=0}^{m-1} z_h H_h(z,v)
=\sum_{i,h<m}z_h z_i v_{i+h}
=\sum_{h<m}z_h v_{2h}.
$$
Thus $\sum_h z_h(H_h(u,v)+L_h(v))=z_0=1$. This proves pointwise avoidance on the entire slice. Queries for its defining coordinates can be grouped in $w$-bit batches. Conversely, the flat cut out by any one execution's affine answers has codimension at most the number of bits returned. The lower bound applied to its affine output proves the per-run assertion. [Lean verification of the symmetric cancellation and final mismatch](ShiftedConvolutionSlice.lean)

## One uniform evaluator at all input lengths

Fix rational $0<\epsilon<1$, set $m=\lfloor n^\epsilon\rfloor$ and $d=\lfloor(n-m+1)/2\rfloor$. For sufficiently large $n$, $m\le d$. Use the first $n_0$ bits of the index as $(u,v)$ and discard at most one trailing bit. Define $C_x$ to have output $H(x)$ on every seed. At the finitely many exceptional lengths use a constant output of the required length. For a requested output bit a read-only input machine can sum $d$ products using $O(\log n)$ workspace and polynomial time, rescanning both operand positions if necessary. Integer roots for the fixed rational exponent also use $O(\log n)$ space. The evaluator satisfies the simultaneous time and space bounds in the [conditional SAT implication](near-linear-sat-and-uniform-low-space-range-avoidance.md).

Take a log-word RAM execution starting from the raw index and zero work memory. Along the execution one may retain a common control path and affine representatives of the state on a surviving affine flat. An instruction whose address, control or nonlinear arithmetic needs fixing can be handled by revealing the bounded number of word operands and loaded data actually needed, costing $O(w)$ affine tests on the current flat. Resolved addresses select the correct prior writes. All other native steps that retain the same path and affine state cost zero tests. Across $q$ charged steps, this gives an affine leaf of codimension at most $Cwq$ for an ISA constant $C$. An unused input bit can be fixed at the outset. If $Cwq\le d-m$, the matching bound gives a real input on which this execution path outputs $H$. Therefore an algorithm escaping this fixed family on every index must spend $\Omega(n/\log n)$ charged instructions **on every run** at that length. One run below the threshold at each of infinitely many lengths gives actual hits by the very same evaluator at those lengths. In contrast, a bound solely on the number of untouched words does not test free processing of all the data. [Affine RAM restriction with writable memory](affine-dimension-along-sat-runs.md) · [Input-word obstruction](unread-words-in-a-range-avoidance-index.md)

The scan-time upper bound takes the XOR of the wordwise ANDs of corresponding pieces of $u$ and the first $d$ bits of $v$. Misalignment uses at most two physical loads per piece, and the last piece is masked. Fold the parity of the one accumulator in $O(\log w)$ shifts. Flip this parity for the first output bit and fill the remaining $m-1$ bits with zeros. This takes $O(n/w+\log w)$ word operations including packed output. The exact depth above belongs to the affine-query model, and the unrestricted RAM bounds here match in order. The infinite-hit condition for arbitrary polynomial-time algorithms remains open.

The finite audit enumerates all affine answers and all flats below the avoidance threshold at $(d,m)=(2,1),(2,2),(3,2)$. For $(3,2)$ it checks 4,227,072 affine answers across 255 flats. The minimum numbers of hits are 20 on the whole cube and 4 on a hyperplane, attaining the displayed lower bound in both cases. The upper certificate is tested at every point in all three examples. [Reproducible census](shifted_convolution_slice_audit.py)
