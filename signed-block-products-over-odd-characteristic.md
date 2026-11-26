# An exact bit network below the arithmetic matrix multiplication exponent

**Result.** Let $G_d(A,B,C)$ be the zero-one indicator that the proposed binary matrix $C$ is the product of $A,B$ over $\mathbb F_2$. Over every coefficient field in which two is invertible, $G_d$ has exact nonuniform networks of binary wires and trivalent tables with volume $d^{11/5+o(1)}$. The numerical exponent uses the published upper bound on the asymptotic rank of binary matrix multiplication. The computation is exact on all input triples, including dense matrices and errors of arbitrary rank. For characteristic two the previous $O(d^2\log^2 d)$ construction is smaller. The present upper bound reduces the greatest possible exponent obtainable from this particular network lower-bound transfer to SAT from $9/8$ to $11/10$. A positive polynomial improvement over quadratic graph volume in odd characteristic remains open. [Matrix tensor, asymptotic rank over the base field, and earlier upper-bound credits](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/intro.tex) · [Characteristic-two construction](matching-characteristic-networks-for-binary-products.md) · [Transfer to SAT time](list-and-matrix-costs-for-ram-and-tapes.md)

The construction uses a fixed signing of a long list of Boolean products. On all inputs, its integer sum lies in a substantially shorter interval. This permits a short exact sum over multisets. A second ingredient is using different algorithms on the block grid and inside each block. Neither step evaluates the contraction in the claimed volume in ordinary deterministic time.

## A signing with a small lookup table

Suppose $M$ Boolean terms are determined by $3d^2$ input bits. There are fixed integer signs $\sigma_\ell$ such that on every input
$$
           \left|\sum_{\ell<M}\sigma_\ell e_\ell\right|\le L,
           \qquad L=\min\{M,\lceil5d\sqrt M\rceil\}.
$$
For the nontrivial range $M\ge d^2$, the signs have a lookup table with $O(d\sqrt M\log(M+2))$ bits. Divide the indices into blocks of size $g=\max(1,\lfloor\sqrt M/d\rfloor)$, shortening the last block. Give each block its own independent random binary vector $a$ and bit $b$. At offset $u$ take the sign $(-1)^{a\cdot u+b}$ using a fixed binary representation. Distinct offsets in the same block have pairwise independent unbiased signs, including offset zero. For a fixed input the signed block sums $X_i$ are independent, have mean zero, and satisfy $|X_i|\le g$ and $\sum_i\mathbb E X_i^2\le M$. Set $t=d/\sqrt M$. The bound $e^z\le1+z+z^2$ for $|z|\le1$ gives $\mathbb E e^{\pm t\sum X_i}\le e^{t^2M}=e^{d^2}$. The chance of exceeding $5d\sqrt M$ in magnitude is at most $2e^{-4d^2}$. A union bound over all $2^{3d^2}$ triples fixes the seeds. Each stored vector has $O(\log(M+2))$ bits, and the number of blocks is $O(d\sqrt M)$. One block can be read for each selected label by a single batched table access. If $M<d^2$ one can use the all-positive signing and the bound $L=M$.

## Evaluating parity from the short interval

Write $S=\sum\sigma_\ell e_\ell$ over the integers. Its parity is unchanged by signing. For a fixed input inspect the coefficients up to degree $2L$ in
$$
  (1+x)^{L+S}=(1+x)^L\prod_{\ell<M}(1+x)^{\sigma_\ell e_\ell}.
$$
The left side has degree between zero and $2L$. On the right, each of $L$ dummy factors or each active positive term gives $1+x$. Each active negative term gives $1-x+x^2-\cdots$ as a formal power series. An inactive term contributes one. Weight the coefficients through degree $2L$ by $(-2)^j$ at degree $j$, then multiply by $(-1)^L$. This gives $(-1)^S$ over the integers and therefore in every field. Evaluating at $-2$ is done **after** taking coefficients through the cutoff.

To realize the sum, guess $2L$ sorted labels drawn from real terms, the $L$ distinct dummy labels, and a greatest padding symbol. Reject unused encodings. A selected real term must be active. A positive or dummy label may occur once, and a negative real label may repeat. Adjacent comparisons suffice. Give each selected position weight $-2$ times its sign; padding has weight one. Each multiset appears exactly once after its padding. The dummy choices supply the coefficients of $(1+x)^L$ without a binomial table. The tests cost $O((L+1)\log(M+2))$ gates apart from batched queries. This computation uses no division by a factorial. [Finite audit of the signed coefficients and multiplication graph](binary_product_discrepancy_audit.py)

## Fast multiplication on the grid and ordinary multiplication inside each block

Fix an exact rank decomposition over $\mathbb F_2$ for the $b\times b$ matrix product, with $r$ terms, and put $\lambda=\log_b r>2$. At grid side $B=b^j$ tensoring the decomposition gives $r^j=B^\lambda$ terms. For sides differing from an exact grid multiple, pad by zero to a square of side $Bm$, with $m=\lceil d/B\rceil$. Apply the rank algorithm on the grid of $m\times m$ blocks. For each rank index $a$ form three binary block arrays $U_a,V_a,Z_a$ by the factor and output-coefficient linear forms of the decomposition. The third array is applied to the external test matrix $Z$. The resulting binary scalar is
$$
  \langle AB,Z\rangle =
   \bigoplus_{a=1}^{r^j}\ \bigoplus_{i,h,k=1}^m
          (U_a)_{ih}(V_a)_{hk}(Z_a)_{ik}.
$$
This follows by expanding block matrix multiplication; each product has its $A$-block on the left and $B$-block on the right. Equivalently, the coefficient of every ordered pair of original block entries is the corresponding coefficient of the scalar matrix multiplication tensor. The order remains valid for noncommuting blocks.

All three tables together have $O(r^j m^2)$ bits. Applying one fixed base transform along each grid axis successively builds them with $O_b((j+1)r^j m^2)$ Boolean gates and wires. At level $a$ there are $r^a(b^2)^{j-a}m^2$ intermediate entries per bank, and each local transform uses only a fixed number of input and output wires. This explicitly pays for copies. The number of distinct *labels* in the displayed sum is the larger quantity $M=r^j m^3$.

Apply the signing and multiset construction. Every selected real label names four indices and requests only three table bits and one block seed. Sorting claimed address/value records together with initialization records for **all** table cells verifies these reads exactly. Require equality of adjacent values at equal addresses and require each legal address to have its initialization record by construction. A selected tuple has a unique consistent assignment to these read values. Sorting and all other Boolean gates are deterministic once the tuple is given. Padding and dummy positions can query fixed valid addresses, ignoring those results. Indices and seeds have logarithmic width, and multiplication, division and bit extraction on these short addresses have polylogarithmic-size Boolean circuits. Thus including external terminals and explicit copies, the volume is
$$
   O_b\big((d^2+r^j m^2+d\sqrt{r^j m^3})\operatorname{polylog}(d+2)\big).
$$
There is no separate multiplexer of the whole input for each selected term. No list of $M$ arbitrary signs is materialized. [Batched read-only inputs and copying](circuits-for-read-only-batched-word-lookups.md)

This computes the exact sign of the binary trilinear scalar. To obtain the graph, attach the inverse Walsh matrix on each test bit and contract the test bank. The identity $2^{-d^2}\sum_Z(-1)^{\langle AB-C,Z\rangle}=[AB=C]$ costs $O(d^2)$ more vertices and uses the invertibility of two. Each inverse matrix and fixed field weight is a trivalent or lower-arity table. [Scalar-to-graph and graph-to-scalar conversions](parity-and-forbidden-entries-in-the-binary-product-graph.md)

Choose $j=\lfloor\log_b(d)/(\lambda-1)\rfloor$. Then $B=\Theta_b(d^{1/(\lambda-1)})$ and $Bm=\Theta_b(d)$. The table and discrepancy exponents coincide at
$$
               e(\lambda)=2+\frac{\lambda-2}{\lambda-1}.
$$
For every $\epsilon>0$ the asymptotic-rank upper bound over $\mathbb F_2$ supplies a fixed base side and exact rank with $\lambda\le9/4+\epsilon$ (use powers of side two). The constants may depend on this base. Taking the infimum gives exponent at most $e(9/4)=11/5$. Only the upstream upper bound is used. Even the original seven-product algorithm for side two gives the same formula with $\lambda=\log_2 7$. The comparison here is with the formal arithmetic exponent; the network contracts by signed counting over binary witnesses. Known algorithmic matrix verification work concerns different computational models. Priority for this exact network construction is unestablished. [Strassen](https://doi.org/10.1007/BF02165411) · [Künnemann on nondeterministic verification](https://arxiv.org/abs/1806.09189)

## Why signing individual schoolbook triangles stops earlier

For the $d^3$ raw Boolean products $A_{ih}B_{hk}Z_{ik}$, the best possible worst-case signed range is $\Theta(d^{5/2})$. Even subtracting any sum of functions, each depending on at most two complete input banks, cannot improve the lower exponent. The signing lemma gives the upper bound. For the lower bound take arbitrary fixed signs $s_{ihk}$ and choose independent uniform sign matrices $X,T$. For each $(h,k)$ the coefficient $c_{hk}=\sum_i s_{ihk}X_{ih}T_{ik}$ is a sum of $d$ independent signs. Its second moment is $d$ and its fourth moment is at most $3d^2$. Hölder's inequality gives $\mathbb E|c_{hk}|\ge\sqrt{d/3}$. Fix $X,T$ attaining at least the expected sum of the absolute coefficients and choose $Y_{hk}$ to match each sign. Then $\sum s_{ihk} X_{ih}Y_{hk}T_{ik}\ge d^{5/2}/\sqrt3$. Evaluate the Boolean polynomial at $(1+uX)/2,(1+vY)/2,(1+wT)/2$ for independent global signs $u,v,w$. Averaging after multiplying by $uvw$ extracts one eighth of that signed trilinear sum and kills every two-bank correction. Consequently some Boolean input has residual magnitude at least $d^{5/2}/(8\sqrt3)$.

There is a related limit on more general static integer lifts. Suppose an integer function $f$ on the Boolean cube has the required triangle parity modulo two at every input, and its real multilinear interpolant has degrees at most $a,b,c$ in the three banks. If subtraction of arbitrary two-bank corrections leaves absolute error at most $R$, then
$$
                      R(abc)^2=\Omega(d^{5/2}).
$$
Indeed the unique multilinear coefficients of $f$ are integers by Boolean finite differences. Its $(1,1,1)$ coefficient tensor reduces modulo two to the formal triangle tensor. Thus each middle-coordinate slice has at least $d$ odd entries and Frobenius norm at least $\sqrt d$. For any real matrix $D$ and independent random sign vectors $X,T$, $U=X^\mathsf T D T$ has $\mathbb E U^2=\|D\|_F^2$ and $\mathbb E U^4\le9\|D\|_F^4$. For the latter, condition on $T$, use the sign fourth-moment bound, and apply Cauchy–Schwarz to the squared row forms before the second use of that bound. Hence $\mathbb E|U|\ge\|D\|_F/3$. Aligning the middle-bank signs once again gives signed-cube norm $\Omega(d^{5/2})$ for the $(1,1,1)$ tensor.

To bound the same tensor from above, extend $f$ and the corrections multilinearly to $[0,1]^{3d^2}$. The extension of the residual stays in $[-R,R]$ by averaging vertex values. For fixed Boolean arrays evaluate this extension at $(uA,vB,wZ)$ for $u,v,w\in[0,1]$. Its derivative once in each scalar, at the origin, kills the corrections and extracts the $(1,1,1)$ tensor at those arrays. The corrections may individually have very high degree. First take the alternating sum over setting each whole bank to its supplied argument or to zero. This kills the corrections, costs at most $8R$ in norm, and leaves a polynomial of bank degrees at most $a,b,c$. Markov's inequality on $[0,1]$ bounds its mixed derivative by $8(2a^2)(2b^2)(2c^2)R$, successively in the three scalars. Difference of two Boolean indicators represents each sign input, so conversion back to the sign cube costs at most a further factor eight. In particular a uniform range $O(d^2\operatorname{polylog}d)$ in this model requires at least one bank degree $d^{1/12-o(1)}$. The block construction can use high-degree parity functions of the original bits as individual linear-form values. This accounts for why the raw-triangle obstruction does not apply to it.

## Other fixed finite input fields

The same $11/5$ upper exponent holds for the graph of matrix multiplication over any fixed finite input field $K$, with scalar tables over any field $F$ of different characteristic. Let $p=\operatorname{char} K$ and fix a nonzero $\mathbb F_p$-linear functional $\ell:K\to\mathbb F_p$. For $E=AB-C$ and $Z\in K^{d\times d}$ put $v=\ell(\sum_{ij}E_{ij}Z_{ij})$. If $E\ne0$, the map from $Z$ to $v$ is onto by varying a coordinate with nonzero coefficient. Its fibers have equal cardinalities. If $E=0$, it is identically zero. Consequently
$$
 [AB=C]=|K|^{-d^2}\sum_Z \bigl([v=0]-[v=1]\bigr)
$$
holds in $F$. The denominator is invertible even when $F$ has no primitive $p$-th root of unity.

Use the block algorithm over $K$. Each primitive term is the integer representative $e\in\{0,\ldots,p-1\}$ of $\ell$ applied to its three-factor product. Include the $d^2$ corrections representing $-\ell(C_{ij}Z_{ij})$. Replace each term by $\sigma e$ with $\sigma=1-p[h=0]$, using pairwise independent uniform $\mathbb F_p$-valued affine hashes inside each seed block and independent seeds between blocks. The binary digits of the offset are distinct vectors over $\mathbb F_p$ and can be used as the hash argument. The multiplier has mean zero and is congruent to one modulo $p$. Each summand has magnitude at most $(p-1)^2$. The preceding exponential-moment calculation with constants depending only on $K$ fixes seeds giving $|S|=O_K(d\sqrt{M+d^2})$ simultaneously on all $|K|^{4d^2}$ inputs. Reducing $S$ modulo $p$ gives the required $v$.

For each index use up to $(p-1)^2$ separately labeled signed unit factors, with exactly $|\sigma e|$ of them active. Use the multiset construction on these unit factors. To recover the required output weights, view the truncated identity as a polynomial, then substitute $x=\tau-1$ in the cyclic group ring $F[\tau]/(\tau^p-1)$. After multiplication by $\tau^{-L}$ it equals $\tau^S$. This bookkeeping can be implemented entirely by scalar tables over $F$: for each finite selected slot branch between adding one to a running residue and contributing weight $-1$. The first branch represents $\tau$ and the second represents $-1$. Initialize the residue to $-L$ modulo $p$ and give the final residue weight $[0]-[1]$, meaning one at zero, minus one at one, and zero elsewhere. A padding slot has a single continuation of weight one, and occurrences of negative unit factors contribute their formal-series signs as before. The residue needs only constant space per slot. Summing the legal encodings of $Z$, rejecting invalid element encodings if present, and multiplying by the normalization proves the claim. For matching characteristic the earlier graph construction already has volume $d^{2+o(1)}$. Thus switching between fixed finite input fields does not restore the full formal rank exponent for this graph.

## Consequence for extracting formal rank

Combining the bit-graph upper bound with the preprint's formal lower bound $\operatorname{rank}_F(T_d)\ge d^{9/4}$ gives
$$
           \frac{\operatorname{rank}_F(T_d)}{V_F(G_d)}
                    \ \ge\ d^{1/20-o(1)}
$$
for the binary multiplication graph and $\operatorname{char}F\ne2$. In particular, a procedure extracting a formal bilinear rank decomposition from **every** exact bit network for that graph cannot guarantee only a polylogarithmic multiplicative loss. More generally a universal inequality $\operatorname{rank}_F(T_d)\le d^{o(1)}V_F(G_d)^\gamma$ would require $\gamma\ge45/44$. This comparison uses both directions of the upstream rank result, while the graph network construction itself only used its upper bound. The formalization checks the signed-binomial identities; the signing, block layout and total volume are manuscript proofs. [Upstream rank corollary](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/intro.tex) · [Lean coefficient check](upstream-checks/SignedBinomialEvaluation.lean)

A graph-volume lower exponent $2+\delta$ would exclude SAT clocks only strictly below $1+\delta/2$ by the existing transfer. This upper bound forces $\delta\le1/5$ for this graph. In particular the endpoint $11/10$ itself cannot be excluded by that exponent comparison. No lower bound on the execution time of an unrestricted SAT solver follows from the construction.
