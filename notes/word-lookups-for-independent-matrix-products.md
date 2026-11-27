# Word lookups for many independent binary matrix products

Put $h=d^2$, $m=2^{4h}$ and $N=mh$. Each input block consists of $m$ independent binary $d$-square matrices and has $N$ bits. A logarithmic-word RAM computes all $m$ products in $O(m)$ word operations, including preparation of its lookup table. There is also an ordinary 3-CNF family of encoded length $\Theta(N)$ whose satisfiability is the scalar contraction $\sum_b\operatorname{tr}(A_b B_b Z_b)$, with an $O(m)$-time fast path for a correct general SAT solver.

For this family the matrix exponent $\omega=9/4$ in the cited preprint gives the following estimates. A shared bilinear predictor with geometric border rank below a constant fraction of $m d^{9/4}$ agrees with the **entire vector** of products on at most $2^{-\Omega(N)}$ of uniform inputs. With rank $O(N)$ its maximum absolute sign correlation on a uniformly selected output bit is $(\log N)^{-1/8+o(1)}$ in order of exponent. With rank $O(m)$ the corresponding exponent is $-9/8$. Thus even average-case extraction of a single shared low-rank predictor from a fast native run has a logarithmic cost on these direct sums. The number of independent small products matters for applying this observation to a proposed proof about one large product. [Pinned square exponent and field convention](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/107.md)

## Uniform computation and explicit SAT layout

Each $h$-bit matrix occupies a constant number of words. Precompute the $h$-bit product for every pair of matrices by the elementary multiplication algorithm in $O(2^{2h}\operatorname{poly}(d))=o(m)$ operations. Even an additional table of all $2^{3h}$ trace bits takes $o(m)$ time and words to prepare. Concatenating two or three tile identifiers gives a table address fitting in a logarithmic word, since $\log_2 m=4h$. Stream the inputs once to write the product of each pair, or XOR the entries of the trace table selected by the input triples. The output vector takes $O(m)$ words. All parameters and table contents can be generated uniformly.

For a SAT verdict, pin $2^{3h}$ Boolean variables $T_{a,b,z}$ to the public trace bits. Introduce a chain $p_0,\ldots,p_m$, pin its endpoints to zero and one, and impose $p_i=p_{i-1}\mathbin{\oplus}T_{A_i,B_i,Z_i}$ by four clauses per row. Each pin can use the four sign patterns on two extra distinct dummy variables. Choose fixed-width names with a bank tag and enough bits for all rows. Only copies of $A_i,B_i,Z_i$ in the selected table-variable indices vary. Thus every clause has three distinct variable names, and $\Theta(m)$ clauses of $\Theta(\log m)$ bits give encoded length $\Theta(N)$. The endpoint check is equivalent to the claimed trace sum. A general solver verifies the layout and repeated fields in $O(m)$ word operations. It may use the table pins actually supplied after checking their syntax and placement; it then follows the chain. On all other inputs it can use a complete SAT solver. Uniform inputs in the agreement theorem below mean uniform matrices inserted into this explicit layout. [Packed parity-chain encoding](spanning-trees-for-a-packed-sat-verdict.md)

## Simultaneous compression of the tiles

Write $T=\bigoplus_{b=1}^{m} M_d$ for the tensor of the scalar contraction. For any binary trilinear $U$ of border rank at most $s$ over $\overline{\mathbb F}_2$ put $p=\operatorname{srk}_{\mathbb F_2}(T-U)$. Group a minimal slice decomposition by its three possible singleton factors. Intersecting the kernels of the linear factors in each input block gives three subspaces of total codimension at most $p$. On their product $T$ and $U$ coincide.

The subspaces may initially couple all $m$ tiles. Over the algebraic closure consider the product of the three Grassmannians of subspaces of their respective dimensions. The locus where the restriction of $T$ has border rank at most $s$ is closed, by writing the coefficient tensor in local frames. It is nonempty and invariant under the product, over tiles, of the three upper-triangular groups at their index spaces. These groups act by row change and inverse column change, preserving the trace. The Borel fixed-point theorem gives a fixed triple in this closed projective locus. The diagonal torus acts with distinct weights on the matrix units of each mode, even across different tiles since their diagonal parameters are independent. Hence the fixed subspaces are direct sums of coordinate subspaces, with a total of at most $p$ missing coordinates. Triangular shears make each surviving coordinate pattern closed up and to the right, with a missing entry forcing the entire rectangle below and left of it to be missing.

Write $p_b$ for the number of holes in tile $b$ across its three modes. The single-tile trimming lemma leaves a square multiplication of side $r_b=(d-\lfloor 2\sqrt{p_b/3}\rfloor)_+$. In detail, for the three mode hole counts $p_{ij}$ form the symmetric adjacency matrix on the three index sets with weights $\sqrt{p_{ij}}$. Distribute its two endpoint trims along each positive edge in inverse ratios using a positive Perron vector on its component. Their product is $p_{ij}$ and the total at an index set is at most the spectral radius $\rho$. Round every trim down. The two ends of a mode permit dropping last rows and first columns, since any remaining hole would occupy at least the product of the two trims each increased by one, which exceeds $p_{ij}$. The eigenvalues of the weighted triangle sum to zero and their squares sum to $2p_b$, giving $\rho^2\le4p_b/3$. Intersect the resulting index intervals, retaining $r_b$ indices at each of the three positions; omit tiles with $r_b=0$. This gives all surviving products **simultaneously** in the fixed triple. The corresponding restricted tensor has border rank at most $s$. Wigderson and Zuiddam treat compression of direct sums of graph tensors in Theorem 12.19. [Single-tile proof and integer checks](average-case-rank-of-binary-matrix-products.md) · [Wigderson and Zuiddam, §12.6](https://www.math.ias.edu/~avi/PUBLICATIONS/Wigderson_Zuiddam_2025.pdf)

Schönhage's asymptotic sum inequality, over the algebraic closure, gives $s\ge\sum_b r_b^\omega$. This step concerns direct sums of rectangular multiplications and uses no conjecture about additivity of general tensor rank. The function $x\mapsto(d-2\sqrt{x/3})_+^\omega$ is convex and decreasing on the nonnegative reals. Applying Jensen's inequality and $\sum_b p_b\le p$ yields
$$
   s\ \ge\ m\left(d-2\sqrt{p/(3m)}\right)_+^\omega,\qquad
   p\ \ge\ \frac{3m}{4}\left(d-(s/m)^{1/\omega}\right)_+^2.
$$
[Schönhage, *Partial and Total Matrix Multiplication*](https://doi.org/10.1137/0210032)

The full-vector predictor associated with $U$ is the bilinear map $H(A,B)$ obtained from the trace pairing with all $Z_b$. If $u$ denotes the binary analytic rank of $T-U$, then $\Pr[H(A,B)=(A_bB_b)_b]=2^{-u}$ by averaging first over $Z$. Lampert's trilinear bound gives $p\le9u+33$. In particular,
$$
 \Pr[\text{entire vector correct}]
 \ \le\ 2^{-\max\{0,\,\frac m{12}(d-(s/m)^{4/9})_+^2-11/3\}}.
$$
Twice the advantage of the scalar predictor $U$ on the random trace bit equals this same probability. Achieving full-vector agreement $2^{-o(N)}$ forces $s\ge(1-o(1))m d^{9/4}=(1-o(1))N d^{1/4}$. An input-dependent choice from $2^e$ fixed bilinear maps gains at most a factor $2^e$ on the whole-vector probability. [Lampert, Theorem 1.2](https://arxiv.org/abs/2404.19704)

The probability of predicting many *entire tiles* also admits an exponential bound even when the successful tile locations depend on the inputs. For any $1\le \ell\le m$,
$$
 \Pr[\text{at least }\ell\text{ tiles correct}]
 \ \le\ \min\left\{1,\binom m\ell
     2^{-\frac12\max\{0,\,\frac{\ell}{12}(d-(s/\ell)^{4/9})_+^2-11/3\}}\right\}.
$$
This version permits arbitrary separate-input offsets $F(A)+G(B)$. Fix a set of $\ell$ output tiles and freeze all other input tiles. On the selected factors the remaining bilinear term has border rank at most $s$, and the freezing introduces only further separate-input offsets. For each fixed output mask let $r$ be the ordinary matrix rank of the bilinear error on the two inputs. Even with arbitrary separate-input signs the absolute correlation is at most $2^{-r/2}$. Averaging over masks and using Cauchy–Schwarz gives full-vector agreement at most $(\mathbb E_Z2^{-r})^{1/2}$, the square root of the agreement bound without offsets. Apply the displayed full-vector bound to the $\ell$-tile problem, remove the conditioning, and take the union over tile sets. When $\ell\ge (1+\eta)s/d^{9/4}$ and $\log(m/\ell)=o(d^2)$, for fixed $\eta>0$, the bound is $2^{-\Omega_\eta(\ell d^2)}$. It therefore continues to hold with an adjusted constant even after choosing from $2^{o(\ell d^2)}$ predictors using both complete inputs.

## A uniform lower bound for partial outputs

For any $q$-dimensional space of requested masks in the whole output, let $R$ be the geometric border rank of the restricted tensor. For every $d,m$ and $0\le q\le md^2$,
$$
                         R\ \ge\ q\, d^{\omega-2}.
$$
For $q>0$, degenerate the mask space by blockwise change of basis as above, leaving the input modes unrestricted. We get Ferrers shapes with $q_b$ positions in each tile, summing to $q$. If $q_b>0$ its shape contains a rectangle of area at least $q_b/H_d$, where $H_d=\sum_{i=1}^d1/i$. Indeed for nonincreasing row lengths $\lambda_i$, one has $\sum_i\lambda_i\le H_d\max_i i\lambda_i$. Each such rectangle with sides $u_b,v_b$ requests a rectangular multiplication tensor of volume $u_bdv_b$. Apply the asymptotic sum inequality to the direct sum of these surviving rectangles. Using $\omega\le3$ and $q_b\le d^2$ gives
$$
  R\ \ge\ \sum_{q_b>0}(d q_b/H_d)^{\omega/3}
     \ \ge\ H_d^{-\omega/3}\, d^{\omega-2}\,q.
$$
Take the $j$th tensor power of the original restriction. Its mask space has dimension $q^j$, its underlying full multiplication tensor is a direct sum of $m^j$ tiles of side $d^j$, and its border rank is at most $R^j$. Since $H_{d^j}^{1/j}\to1$, taking roots removes the harmonic loss. This bound uses only the square exponent and the sum inequality. For a single tile the full rectangular exponent supplies a stronger result at sparse output dimensions. [One-tile comparison](predicting-entries-of-a-binary-matrix-product.md)

Allow the predictor $H$ also to add arbitrary separate-input offsets $F(A)+G(B)$. Suppose $q$ distinct output entries have bilinear error of ordinary matrix rank at most $k$. Correct these $q$ bilinear components with at most $kq$ rank-one terms, obtaining exact multiplication restricted to these masks with border rank at most $s+kq$. Thus $q(d^{\omega-2}-k)\le s$. For every other entry the sign bias in the presence of separate-input offsets has absolute value at most $2^{-k/2}$ by the normalized operator norm of a bilinear sign matrix. Averaging over a uniformly chosen entry gives, for $0<k<d^{\omega-2}$,
$$
 |\beta|\ \le\ \frac{s}{md^2(d^{\omega-2}-k)}+2^{-k/2}.
$$
Choose $k=\lfloor d^{1/8}\rfloor$ for large $d$. At $s=\Theta(N)$ the upper bound is $O(d^{-1/4})$ and at $s=\Theta(m)$ it is $O(d^{-9/4})$. Conversely, compute completely a fixed set of as many tiles as the budget permits and return zero elsewhere. The cited arithmetic upper exponent and formal bilinearization give exact binary rank at most $d^{9/4+o(1)}$ per tile. Each fully computed tile has bias one, and every other entry has positive bias as a binary dot product. Since $m$ is exponential in $d^2$, rounding the number of computed tiles loses a negligible term in either budget. This proves the exponents in the introduction.

The compression theorem, sum inequality, analytic-rank theorem, and square exponent are external mathematical inputs. The literature check did not establish priority for these combined agreement rates on an explicit family of native RAM computations. The fast computation has separate small products which fit in a word. A method that uses the index sharing across all entries of one large matrix multiplication can avoid this example. An unrestricted SAT time exclusion is still open. [SAT and a single large multiplication](verifying-matrix-products-from-sat.md)

The finite audit exhausts all 8,224 triples of Ferrers masks through side three, finding a simultaneous square with the stated size in each case. It also checks every entry of the side-two trace lookup table against an independently calculated product and solves 175 small width-three chains, including repeated tile queries. The asymptotic sum and agreement bounds are mathematical arguments above. [Executable audit](../audits/matrix_tile_lookup_audit.py)
