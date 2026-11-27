# Testing a long list of forecast equalities over a finite field

Can hashing remove the square-root dependence on the number of inspected addresses? For the truncated suffix tree, it does remove this dependence in **probabilistic degree over a finite field**. A single hashed test can itself have exponential real factorization norm. This entry derives both statements and checks what lower bound would close the gap. [Real-valued approximation](adaptive-default-polynomial.md) · [Distributional SAT cut](sparse-reply-sat-cuts.md)

## A probabilistic polynomial for an adaptive decision with few forecast errors

Use the leaf expansion of the tree lemma with caps $r,q,k$, keeping the exact tests for pin values and nonforecast work replies. Fix $(x,Z,y)$. Its compatible token strings form a prefix-free collection: at each node the program is determined by the tokens consumed and the fixed input, and a terminating leaf has no descendant. Pad each string to length $q$ with zeros. This gives an injection into binary strings with at most $k$ ones. Thus at most $V(q,k)=\sum_{i=0}^{\min(q,k)}\binom qi$ signed leaves can have nonzero exact factors, even if the tree has far more leaves or word values.

For one leaf take its vector $u$ of failed forecast equalities, each component a test of one whole word. Over a fixed prime field $\mathbb F_p$ draw $h=\lceil\log_p(V(q,k)/\eta)\rceil$ independent uniform linear functionals on that vector. Use
$$
 \prod_{i=1}^h (1-\langle a_i,u\rangle^{p-1}).
$$
All-zero vectors pass surely. Each nonzero vector passes with probability $p^{-h}$. Multiply by the leaf's exact factors. Sum the results for leaves of each of the two verdict labels separately in the field. A union bound over compatible leaves proves that, for **each** fixed input, with probability at least $1-\eta$ the two polynomials give the exact two verdict indicators, including both zeros on abstention. Distinct leaves may use independent random coins. The degree in old pins is at most $r$. The degree in distinct work coordinates is at most $d=\min(q,k+(p-1)h)$, using exact full leaves when cheaper. For a fixed prime the depth contribution is only logarithmic in $q$ per exception. The unlimited suffix still has $q\le U$ because repeated incoming addresses are cached. This is an application of finite-field probabilistic polynomials. [Alman and Williams](https://arxiv.org/abs/1611.05558)

On a split into $m$ old and $m$ new pins, every fixed draw after substituting the true row memory $C(x)$ has field rank at most
$$
 D=V(m,r)\sum_{j=0}^{\min(d,U)}\binom Uj v^j .
$$
Expand in monomials in the old bits and products of indicators for at most $d$ word coordinates. Each term then splits into a row feature in $(x,C(x))$ and an arbitrary column coefficient. Combining contradictory values at the same work coordinate gives zero, and repeated identical indicators are idempotent. One can select separate coins for every column at once. Multiplying all features by a row indicator preserves the rank bound.

For a hypothetical SAT family with the same route-recovery properties, suppose on every balanced split every field matrix of rank $D+1$ or less agrees with the bit-valued verdict on at most $1/2+\rho$ of the entries. With the catalog size $J$ in the real cut argument, one obtains $\lambda^2\le 2J\rho+2\eta$ for the probability $\lambda$ of cheap runs with fixed advice. Indeed, on each row cylinder $A$ take a uniform default bit. For default zero use the positive verdict indicator times $1_A$, and for default one use one minus the negative verdict indicator times $1_A$. Both have field rank at most $D+1$. Before hashing the resulting predictor's expected agreement exceeds $1/2$ by half the mass of cheap runs on that cylinder. After hashing it loses at most $\eta\Pr[A]$, since the predictor outside the cylinder remains exactly the default. Sum over the disjoint cylinders and use the companion argument. This removes a query-depth factor at the cost of a strong matrix rigidity premise. For $p=2$ the present quadratic family's bit-valued verdict matrix has rank at most $m+2$ on every split by its bilinear form and the two separate local terms. The needed average-case field-rank hardness therefore fails already at that rank.

## One mask can itself have exponential real norm

Take a binary work array $x$ of length $q$. Column $y$ inspects precisely the cells with $y_j=1$, forecasting zero at all of them. Test the single default leaf with one public binary hash mask $h$. Its pass bit is $B_h(x,y)=(1+H_h(x,y))/2$, where
$$
 H_h(x,y)=(-1)^{\sum_j h_j x_j y_j}.
$$
Writing $t=|h|$, under independent uniform $x,y$ one has $2^{-q}\|H_h\|=2^{-t/2}$ and $\mathbb E H_h=2^{-t}$. If a real inner product $\langle a(x),b(y)\rangle$ approximates $B_h$ pointwise to error $\epsilon<1/2$, then
$$
 (1/2-\epsilon)2^{t/2}
 \le (\mathbb E\|a\|^2\,\mathbb E\|b\|^2)^{1/2}.
$$
Indeed $\mathbb E[H_h B_h]=(1+2^{-t})/2$, and the vector spectral inequality bounds the correlation of the approximant. The proof allows arbitrary dimension and arbitrary row and column features. A dense public mask consequently destroys the norm estimate needed to carry a fixed sampled polynomial through the real proof. This example addresses a *fixed draw*. Averaging many masks first gives a different real function, to which the displayed lower bound need not apply.

The gap for $p=3$ has a quantitative benchmark: Alman's 2026 preprint proves a constant-fraction rigidity bound for the Walsh–Hadamard transform up to rank proportional to the square of the logarithm of its dimension. Alman and Liang give agreement close to one half at a smaller rank. The estimate above pays for whole-word labels and unknown read sets in $D$ and $J$. Substituting these published bounds does not prove the needed estimate at the parameters of the SAT cut. [Alman](https://arxiv.org/abs/2608.06592) · [Alman and Liang](https://arxiv.org/abs/2502.19580)

## Averaging the masks cannot give an arbitrary cheap real factorization

A second example handles real approximants *after* randomization has been averaged. Fix $b\ge2$ and $q\ge2$. Give the row $bq$ binary work cells in $q$ blocks of size $b$. The column chooses one location and a forecast bit in each block. Read the chosen cells until the $j$th forecast error, for $1\le j\le q/2$, then output one sign. Output the other sign if the scan ends earlier. Every input has at most $j$ actual discrepancies and uses no old pin read. The full signed output matrix is exactly the $(bq,q,f)$ pattern matrix of a Hamming-weight threshold $f$ at $j$. Choosing locations and XOR masks in the definition of a pattern matrix coincides with selecting addresses and forecast bits here.

Let $A_{xy}=\langle a_x,b_y\rangle$ be any pointwise $\eta$-approximation of this matrix. With $s$ the number of entries, the normalized trace norm $\|A\|_*/\sqrt s$ is at most $(\mathbb E_x\|a_x\|^2\mathbb E_y\|b_y\|^2)^{1/2}$ by the trace norm inequality for a matrix product. For any $\epsilon\in(\eta,1)$, Sherstov's Theorem 8.1 gives the lower bound $(\epsilon-\eta)b^{\deg_\epsilon(f)/2}$ on that normalized trace norm. At fixed constant error, Paturi's threshold degree estimate in its **uniform approximation** form yields a required norm product of $b^{\Omega(\sqrt{qj})}$ with distinct parameter $b$ for the block size. For $2^{-q}\le\epsilon\le1/3$, the small-error estimate for nonconstant symmetric functions additionally gives $\deg_\epsilon(f)=\Omega(\min(q,\sqrt{q(j+\log(1/\epsilon))}))$, up to the fixed rescaling of error between the bit and sign conventions. The explicit prefactor $\epsilon-\eta$ belongs in the norm inequality at small error. These statements concern general suffixes and arbitrary hypothetical initial memories. They apply to any choice of real features that achieves pointwise approximation, regardless of the way those features were generated. The genuine SAT rows could obey extra structure. [Sherstov, Theorem 8.1](https://arxiv.org/pdf/0906.4291#page=24) · [de Wolf, Theorem 1 and the threshold estimate](https://homepages.cwi.nl/~rdewolf/publ/qc/degreesymmf.pdf)
