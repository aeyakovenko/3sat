# Linear-size bit circuits for verifying binary matrix products with sparse errors

**Theorem.** Fix $0<\epsilon<1$. Given three $d\times d$ binary matrices $A,B,C$, suppose $E=AB-C$ over $\mathbb F_2$ has at most $d^{1-\epsilon}$ nonzero entries. The deterministic, nonuniform, fan-in-two Boolean circuit complexity of deciding whether $E=0$ under this promise is $\Theta_\epsilon(d^2)$. The input has $3d^2$ bits. The upper bound counts gates over a fixed Boolean basis and permits free wire fan-out.

The proof uses sparse parity checks on both sides of the product. The shapes of the two checks vary together. This permits enough checks to detect a sparse error pattern while keeping the middle multiplication quadratic in *bit* operations.

## A stronger bound from an encoded product

**Theorem.** Let $\mathcal E_d\subseteq\mathbb F_2^{d\times d}$ be any specified family containing zero. There are deterministic nonuniform circuits of size

$$
O\!\left(d^2+d\log_2(2+|\mathcal E_d|)\right)
$$

for deciding $AB=C$ when $AB-C\in\mathcal E_d$. In particular, $O(d^2)$ gates suffice whenever $\log_2|\mathcal E_d|=O(d)$. This covers all error patterns of weight at most $O(d/\log(2d))$ and, separately, all errors of any fixed constant rank. Both families allow arbitrary single-entry errors, so the lower bound below applies to each (for a weight cutoff at least one and rank cutoff at least one).

Spielman's binary linear codes give a matrix $G\in\mathbb F_2^{M\times d}$ with $M=O(d)$, relative distance at least an absolute constant $\rho>0$, and an $O(d)$-gate circuit for $x\mapsto Gx$. Use zero padding to the next message dimension in the doubling family of the construction. No decoding circuit is needed. [D. Spielman, *Linear-Time Encodable and Decodable Error-Correcting Codes*, Theorem 19 and Lemmas 2–3](https://www.cs.yale.edu/homes/spielman/Research/ITsuperc.pdf)

For every nonzero $E$, the product encoding $GEG^\mathsf T$ has at least $\rho^2M^2$ nonzero coordinates. A nonzero row of $E$ produces at least $\rho M$ nonzero columns of $EG^\mathsf T$. Each of these columns produces at least $\rho M$ nonzero entries after left encoding. A uniformly sampled coordinate thus detects each fixed $E\ne0$ with probability at least $\rho^2$. Take $t=\lceil\ln(2+|\mathcal E_d|)/\rho^2\rceil$ independent coordinates. The chance that any nonzero promised error evades all the coordinates is at most $|\mathcal E_d|e^{-\rho^2t}<1$. Freeze a successful list, independent of the input. This argument establishes existence even for a nonconstructively defined error family.

Compute $GA$, $BG^\mathsf T$, and $GCG^\mathsf T$ by applying the linear-size encoder separately to columns or rows. Together they use $O(d^2)$ gates. At each selected coordinate $(i,j)$ compare the length-$d$ inner product of row $i$ of $GA$ and column $j$ of $BG^\mathsf T$ with the corresponding bit of $GCG^\mathsf T$. All $t$ comparisons cost $O(dt)$. Equality passes all checks, and every promised nonzero error fails at least one. The chosen coordinates need $O(t\log(2d))$ bits of nonuniform advice in addition to the choice of code circuit.

For weight at most $K\ge1$, there are at most $(1+d^2)^K$ patterns, by listing at most $K$ marked positions padded with a blank. Thus $K=O(d/\log(2d))$ suffices. For rank at most $r$, write $E=UV$, where $U$ is $d\times r$ and $V$ is $r\times d$. Zero padding handles smaller ranks. There are at most $2^{2rd}$ choices, which proves the constant-rank claim. No restriction on the Hamming weight is needed in the rank case. Both claims also apply on the compact projected SAT image described below. For a general family of $2^{O(d)}$ errors that excludes some singleton positions, only the upper bound is asserted.

For each fixed rank cutoff $r$, the coordinate list can also be constructed in polynomial time. Pad $G$ with zero coordinates to a square output length $M'$ between $M$ and $4M$. Any nonzero encoded error still has relative weight at least $\eta=\rho^2/16$. Its rank is at most $r$, so it has at most $2^r$ row types. Its support is a disjoint union of at most $2^r$ rectangles, one for each row type and its set of nonzero columns. One rectangle occupies a fraction at least $\eta/2^r$ of the whole matrix. Take an explicit constant-degree expander on the $M'$ indices, add a loop at each vertex to ensure a two-sided spectral gap, and raise its walk matrix to a constant power so its normalized nonprincipal eigenvalues have absolute value less than $\sqrt{\eta/2^r}$. The expander mixing inequality gives a positive edge count between the two sides of any rectangle of this area. Checking all ordered walk endpoints uses $O_r(d)$ inner products. This gives a polynomial-time constructible $O_r(d^2)$-gate family for the bounded-rank promise. The construction time for the circuit is separate from its gate count. [Gabber and Galil, *Explicit Constructions of Linear-Sized Superconcentrators*](https://doi.org/10.1016/0022-0000(81)90040-4) · [Spielman's encoder](https://www.cs.yale.edu/homes/spielman/Research/ITsuperc.pdf)

The sparse endpoint is also sharp for the *number of fixed scalar linear checks*. Suppose $t$ binary linear measurements distinguish zero from all matrices of weight at most $K$. Two different matrices of weight at most $\lfloor K/2\rfloor$ must have distinct syndromes, as their sum has weight at most $K$. Thus

$$
t\ \ge\ \log_2\sum_{j=0}^{\lfloor K/2\rfloor}\binom{d^2}{j}.
$$

For $2\le K\le d^2$ this is $\Omega(K\log_2(e d^2/K))$. Conversely the encoded-product argument uses $O(K\log_2(e d^2/K))$ scalar checks, using the count of all weight-$\le K$ patterns. For $K\le d^2/2$ that count is at most $(e d^2/K)^K$, and for $K>d^2/2$ it is at most $2^{d^2}$. Thus a verifier with $O(d)$ scalar linear measurements reaches the order $d/\log d$ for sparse errors. For rank at most $1\le r\le d$, the matrices supported on the first $r$ rows form an $rd$-dimensional subspace and all satisfy the promise. The measurements must be injective on it, requiring $t\ge rd$, whereas the product-code proof uses $O(rd)$ checks. These are lower bounds on the number of measurements. They do not charge the gates used to evaluate checks jointly.

The elementary sparse-check proof that follows uses no coding theorem and applies throughout the fixed-power range in the first theorem.

## Sparse parity checks

Fix $0<\delta<a<1$. For all sufficiently large $d$, set $s=\lceil d^a\rceil$. There is an $s\times d$ binary matrix $H$ with at most $q=O_\delta(1)$ ones per column such that $Hv\ne0$ for every nonzero binary vector $v$ of weight at most $d^{a-\delta}$.

Choose an even integer $q>4/\delta$. In each column independently select $q$ independent uniform rows with replacement. Each selection toggles the bit at its position. For a fixed set of $u$ columns to sum to zero, each occupied row must be selected an even number of times, so at most $r=qu/2$ rows are occupied. For $u\le d^{a-\delta}$ and $d$ large enough, $r\le s$. The probability of at least one bad set of size $u$ is at most

$$
\binom du\binom sr (r/s)^{qu}
\le \left[\frac{ed}{u}\left(\frac{e q u}{2s}\right)^{q/2}\right]^u
\le d^{-u}.
$$

The last inequality uses $u/s\le d^{-\delta}$ and $q\delta/2>2$. Summing over all positive admissible $u$ gives probability less than one. This fixes a single matrix that works for all such vectors. Its sparse description takes $O_\delta(d\log d)$ bits.

## Detecting every promised error

Take $d\ge2$, $m=\lceil 8/\epsilon\rceil$ and $\delta=1/m$. For each $a=j\delta$ with $2\le j\le m-2$, choose sparse parity checks $L_a$ and $R_a$ with respective row counts $s_L=\lceil d^a\rceil$ and $s_R=\lceil d^{1-a}\rceil$. Apply the lemma at exponents $a$ and $1-a$. For this shape compare the two matrices

$$
(L_a A)(B R_a^\mathsf T) \quad\text{and}\quad (L_a C)R_a^\mathsf T.
$$

Accept if they are equal for every shape. If $E=0$, every comparison succeeds.

If $E\ne0$, let $h$ denote its number of nonzero rows and put $x=\log_d h$. We have $0\le x\le 1-\epsilon$. Choose $a=(\lceil x/\delta\rceil+2)\delta$. Then $x+2\delta\le a <x+3\delta$ and $a\le1-5\delta$, so this shape belongs to the grid. At most $d^{a-\delta}$ rows are active. Some active row has weight at most

$$
|\operatorname{supp}E|/h\le d^{1-\epsilon-x}\le d^{1-a-\delta},
$$

since $a+\delta\le x+4\delta\le x+\epsilon$. The right check preserves that row as a nonzero row of $ER_a^\mathsf T$. Every originally zero row stays zero. Any nonzero column of this partially compressed matrix therefore has weight at most $h\le d^{a-\delta}$ and survives the left check. The selected comparison fails. This includes $h=1$, a single erroneous bit, and the largest integer error weight allowed by the promise.

## Gates and advice

For one shape, $L_a A$, $B R_a^\mathsf T$, and $L_a C$ each cost $O(qd^2)$ XOR gates. Each source entry contributes to at most $q$ target sums, and empty sums use a shared zero. Applying the right check to $L_a C$ costs $O(q s_Ld)$. Since $s_L s_R\le4d$, ordinary multiplication of the two compressed factors takes $O(ds_Ls_R)=O(d^2)$ binary AND and XOR gates. Comparing and combining all entries costs $O(s_Ls_R)$ per shape. There are $O_\epsilon(1)$ shapes. XOR can be implemented by a constant number of gates over the standard AND, OR, NOT basis. Enlarge the constant to cover the finite set of $d$ below the parity-check threshold.

For the lower bound take $A=B=C=0$ and change any single entry of $C$. Both inputs meet the promise, and their answers differ. The output depends on all $d^2$ input bits of $C$. A single output of a fan-in-two circuit with $g$ gates can depend on at most $g+1$ distinct inputs, giving $g\ge d^2-1$.

All wiring is fixed for a given dimension. The proof chooses $O_\epsilon(d\log d)$ bits of sparse check descriptions per dimension by the probabilistic method. It gives no construction of those descriptions within the stated gate bound. At the endpoint $\epsilon=1$, the promise allows one error, and parity of all entries of $E$ suffices. It can be computed as $(\mathbf1^\mathsf T A)(B\mathbf1)-\mathbf1^\mathsf T C\mathbf1$ in $O(d^2)$ gates. At $\epsilon=0$ the grid argument loses its slack. The bound above is asserted for fixed positive $\epsilon$, with constants allowed to depend on it.

## Consequence for the projected SAT instances

In the compact matrix-product mismatch projection each input matrix bit occurs once, as a designated ASCII bit of a variable identifier, and satisfying assignments are in bijection with erroneous coordinates. A circuit on the image of this projection can recover the three matrices by fixed wires, run the above test, and complement its answer. Consequently those projected formulas with at most $d^{1-\epsilon}$ assignments admit $O_\epsilon(d^2)$-gate SAT circuits. The single-bit flips of $C$ at $A=B=C=0$ still distinguish $d^2$ separate input bits, giving the matching order on this promised family. The projection's semantics and bit positions are also exercised by the [compact encoding audit](../audits/compact_product_projection_audit.py). The [projection and its size proof](compact-bit-projection-of-matrix-mismatch.md) give the same linear-order consequence up to $O(d/\log(2d))$ assignments via the encoded-product theorem. General formulas with few solutions and unrestricted matrix errors are outside this theorem.

## Prior work and scope

Künnemann gives a deterministic algorithm for sparse matrix-product verification. Bennett, Gajulapalli, Golovnev and Warton summarize its time as $\widetilde O(d^2)$ for at most $d$ erroneous entries. Their Theorem 1 gives a deterministic $O(d^{\omega(1,1,\gamma/2)+\eta})$-time algorithm for polynomially bounded integer matrices with at most $d^\gamma$ errors, for fixed $\eta>0$. Figure 2 tests a parity check separately on the rows and columns. Their Section 1.1.2.1 counts linear measurements needed for unrestricted errors, where the joint kernel must be zero. Here that kernel need only avoid low-weight vectors. The present proof charges individual Boolean gates over $\mathbb F_2$, permits nonuniform checks, and gives an exact quadratic upper bound under the stated promise. Priority for this particular circuit bound has not been established. [Künnemann, ESA 2018](https://doi.org/10.4230/LIPIcs.ESA.2018.56) · [Bennett et al., APPROX/RANDOM 2024, Theorem 1 and Sections 1.1.1–1.1.2](https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2024.42)
