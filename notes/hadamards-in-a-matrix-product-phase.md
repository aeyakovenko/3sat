# Hadamards in a circuit for the matrix-product phase

Let $M(A,B,Z)=\mathrm{tr}(ABZ)$ on three $d$-square binary matrices. Suppose a measurement-free Clifford+$T$ circuit exactly applies the diagonal sign $(-1)^M$ with clean ancillas returned to zero, up to a fixed global phase. Use the generating gates $X$, CNOT, $S$, CZ, $H$, and $T^{\pm1}$. Let $h,t$ be its Hadamard and $T$ counts. The following proof also defines an integer $\rho$ computed from the affine output constraints. For a universal constant $K$,
$$
     h-2\rho\ \ge\ \tfrac1{48}(d-t^{4/9})_+^2-K.
$$
If $h=0$ then $t\ge d^{9/4}$ exactly for $d\ge2$. Both statements use the lower exponent in the November 2026 matrix multiplication preprint. This concerns a specified quantum gate set. One coefficient in the proof is the **tensor rank over the binary field**, even though the gates have complex amplitudes. [Matrix exponent](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/107.md) · [Mazumder on Hadamard-free phase synthesis, including related tensor bounds](https://arxiv.org/abs/2610.01024)

## Path amplitudes

Write $x=(A,B,Z)$. In the computational basis, expand each Hadamard gate by a branch assigning its outgoing bit. For fixed branch variables $v\in\mathbb F_2^h$, wire values are affine in $(x,v)$: diagonal gates only contribute phases. Imposing the required final basis vector $(x,0)$ gives an affine system $Kv=Lx+c$. Its rank $\rho=\operatorname{rank}K$ is independent of $x$. Exact implementation implies a nonzero amplitude for this output at every $x$. Hence an affine choice $v_0(x)$ of a solution exists, by fixing a linear right inverse on the image of $K$. Write $v=v_0(x)+w$, $w\in\ker K$. For each fixed $w$ the resulting wire parities have linear parts in $x$ independent of $w$.

A path has weight $2^{-h/2}\exp(2\pi i P_w(x)/8)$. Its exponent $P_w$ is a sum of odd-coefficient integer lifts of affine binary parities from $T^{\pm1}$ gates, even-coefficient lifts from $S$, and four times binary polynomials of degree at most two from CZ and the input-output signs of Hadamards. For a lifted affine parity $\ell$, its signed third finite difference in independent directions from the three blocks is
$$
      4\,\ell_A(\Delta A)\ell_B(\Delta B)\ell_Z(\Delta Z)\pmod 8.
$$
If one direction preserves the parity, the difference vanishes. If all three toggle it, the alternating sum is $4$ or $-4$, equal modulo eight. Thus all $w$ give one common third-difference tensor $U$, a sum of at most $t$ pure trilinear tensors. The even lifts and the binary quadratics contribute zero. In particular $U$ has ordinary binary rank at most $t$.

Let $a=-\log_2\mathbb E(-1)^{M-U}$. Take the normalized scalar product of each path phase with the target phase. Three applications of Cauchy–Schwarz on the three input blocks bound its absolute value to the eighth power by $2^{-a}$. Indeed the eight-corner conjugated product just evaluates the phase of $M-U$ on independent, uniformly random differences. The scalar product of the *circuit* diagonal with the target has absolute value one. There are $2^{h-\rho}$ compatible paths, so
$$
           1\le2^{h/2-\rho-a/8},\qquad a\le4(h-2\rho).
$$
The average-case rank estimate gives $a\ge(d-t^{4/9})_+^2/12-11/3$, proving the assertion with $K=11/12$. When $h=0$, $a=0$ forces the trilinear forms $M$ and $U$ to coincide on every binary triple, hence their coefficient tensors coincide. Tensor powering and the imported exponent give $t\ge d^{9/4}$. Conversely, for each binary rank-one term with parity factors $p,q,r$, the identity
$$
 4pqr=p+q+r-(p\oplus q)-(p\oplus r)-(q\oplus r)+(p\oplus q\oplus r)
$$
implements its phase with at most seven $T^{\pm1}$ gates, using clean parity ancillas and CNOTs to compute and uncompute them. This gives Hadamard-free $T$-count at most seven times ordinary tensor rank. [Analytic rank estimate and earlier work](average-case-rank-of-binary-matrix-products.md)

## Application to the proposed SAT reduction

A trace-phase oracle on a coherent mask yields the entire matrix product with one query by the Bernstein–Vazirani algorithm. The hypothesis of near-linear deterministic SAT supplies the scalar trace evaluation in $d^{2+o(1)}$ native RAM time. A coherent, reversible simulation that treats random memory access as a primitive can log updates and uncompute. Replacing random access and workspace by a circuit over the gate set above incurs a cost that the reduction does not bound at the required parameters. Even an implementation with $t=d^{2+o(1)}$ is compatible with the displayed theorem if its excess $h-2\rho$ is of order $d^2$. Establishing a forced saving in the Hadamard paths of a SAT-derived implementation remains open. [Fine-grained quantum reduction, Theorem 3](https://arxiv.org/abs/2509.19528) · [Explicit SAT reductions](verifying-matrix-products-from-sat.md)

Lean checks the signed single-parity difference, the even-parity case and the seven-term identity on Boolean inputs. The path summation and analytic-rank bound are written arguments. [Lean proof](../lean/MatrixPhaseDifferences.lean)
