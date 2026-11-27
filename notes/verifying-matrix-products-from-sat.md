# What near-linear SAT would imply for matrix product verification

Suppose a deterministic logarithmic-word RAM decides explicit SAT of encoded bit length $N$ in $O(N\log^a(N+2))$ time for fixed $a\ge0$. Then it can deterministically evaluate the **full trilinear contraction**
$$
       G(A,B,Z)=\sum_{i,j,k} Z_{ij}A_{ik}B_{kj}
$$
on three binary $d$-square matrices over $\mathbb F_2$ in $d^2\operatorname{polylog}d$ time. The matrix $Z$ is arbitrary. This strengthens the earlier rank-one checksum, for which two matrix-vector products already give that time without a SAT assumption. A separate formal arithmetic statement below identifies a condition on a system of product-verification equations that would suffice to obtain a low-rank multiplication algorithm. [Earlier checksum and unique-witness construction](matrix-products-from-a-sat-trace.md)

## Two explicit reductions to decision

For proposed $C$, guess indices $i,j$ witnessing $(AB)_{ij}\ne C_{ij}$. Pad to the next power of two with zero rows and columns and enforce valid index ranges. For each $k$ select $A_{ik}$ and $B_{kj}$ by binary multiplexer trees. All $2d$ trees together use $O(d^2)$ bounded-fan-in gates. Select $C_{ij}$ with another $O(d^2)$ gates and check the parity of the $d$ selected products. Give the input bits unit pins, impose gate equivalences and require a mismatch. The resulting width-three CNF has $O(d^2)$ records with $O(\log d)$-bit variable names. Its encoded length is $O(d^2\log d)$, and a deterministic RAM can construct it in this many steps. Complementing the SAT decision therefore verifies an arbitrary proposed product in $O(d^2\log^{a+1}d)$ time.

Now guess $d^2$ bits of $C$, run this **deterministic** verifier, and check $\sum_{ij} Z_{ij}C_{ij}=1$ in $O(d^2)$ further operations. Exactly one matrix passes the verifier. This nondeterministic computation accepts precisely when $G=1$. Its clock is $T=O(d^2\log^{a+1}d)$. The packed bounded-computation encoding uses $O(T\log^2 T)$ Boolean gates for the local steps and sorted memory records and $O(T\log^3 T)=O(d^2\log^{a+4}d)$ encoded bits. It can be materialized in $T\operatorname{polylog}T$ time. The second SAT call costs $O(d^2\log^{2a+4}d)$ steps on this encoding, and the construction overhead also fits $d^2\operatorname{polylog}d$. The reduction reads the requested scalar from a single SAT decision. [Bounded-computation encoding and instruction assumptions](packed-band-transfer.md)

Freivalds' randomized verifier already checks a proposed product in quadratic arithmetic work with one-sided error. Künnemann studies nondeterministic verification and product correction under an error-count promise. Bennett, Gajulapalli, Golovnev and Warton give faster deterministic verification in sparse-error regimes. Their barrier for fixed linear sketches of the form $L_i(AB-C)R_i$ charges independent worst-case rectangular multiplications for the tests. A transfer from verification restricted to binary matrices to a low-rank formal multiplication tensor is still missing. For generic characteristic-zero inputs there are now separate arguments for real witnesses and complex equations. [Künnemann, ESA 2018](https://doi.org/10.4230/LIPIcs.ESA.2018.56) · [Bennett et al., including the hypotheses in §1.1.2](https://arxiv.org/pdf/2309.16176)

## When formal verification equations do yield a multiplication algorithm

Let $g(A,B,C)$ be a vector of polynomials computed by a division-free arithmetic circuit with $s$ nonscalar multiplication gates over a field $F$. Suppose $g(A,B,AB)=0$ as a **polynomial identity**. Suppose that at one point $(A_0,B_0,C_0=A_0B_0)$ over an extension $K$ of $F$, the matrix $J=\partial_C g(A_0,B_0,C_0)$ has column rank $d^2$. Then the tensor rank of $d$-square matrix multiplication over $K$ is at most $2s$. Additional zeroes of $g$ away from the graph are allowed.

Work in two scalar parameters $t,u$ modulo $(t^2,u^2)$. Substitute
$$
        (A_0+tA,\ B_0+uB,\ C_0+tAB_0+uA_0B)
$$
in the circuit. If we add $tuAB$ to the last coordinate, it becomes the product of the first two, and every output vanishes. Adding this term changes the mixed coefficient of output $h$ by $J_h\,\mathrm{vec}(AB)$. Indeed $tu$ annihilates both $t$ and $u$, and $(tu)^2=0$, so only the ordinary first derivative at the constant base contributes. The mixed coefficient before that addition is therefore $-J_h\,\mathrm{vec}(AB)$.

Initially the mixed coefficients are zero, and the pure $t$ and $u$ coefficients are linear forms in $A$ and $B$ respectively. This remains true for the pure coefficients throughout the circuit. Addition and multiplication by a field scalar preserve the linear span of the mixed coefficients. At a product gate with inputs $p,q$, the mixed coefficient is
$$
       p_{00}q_{11}+q_{00}p_{11}
                 +p_{10}q_{01}+q_{10}p_{01}.
$$
The first two terms use earlier mixed coefficients with constant weights. The last two add at most two products of one linear form in $A$ and one in $B$. Thus all output mixed coefficients are jointly in the span of at most $2s$ rank-one bilinear forms. A constant left inverse of $-J$ recovers every entry of $AB$ from these outputs. This proves the tensor-rank bound over the field containing the chosen point and left inverse. The argument counts nonscalar multiplications and permits arbitrary linear decoding.

OpenAI's November 24 preprint claims $\omega_F=9/4$ for formal matrix multiplication over every field. Even one rank decomposition of cost $r$ yields exponent at most $\log_d r$ by tensor powers ($d\ge2$). Thus the claimed lower bound rules out $2s<d^{9/4}$ under the two stated hypotheses, including in finite characteristic. The mixed-coefficient calculation is the usual bilinearization of a formal circuit, applied here to the normal directions of its verification equations. I have not established priority for this formulation. [OpenAI preprint](https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf) · [Formal bilinearization in its source](https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/obstruction.tex)

## The missing step from a bit verifier

An arithmetic circuit for the formal trilinear polynomial $G$ would also suffice. Its $d^2$ formal derivatives with respect to $Z_{ij}$ are exactly the entries of $AB$, and Baur–Strassen computes the entire gradient at constant-factor arithmetic cost. The SAT reduction gives agreement with $G$ on binary inputs only. Over $\mathbb F_2$ the circuit representatives $P$ and $P^2$ agree on that cube and every formal first derivative of $P^2$ vanishes. In the algebra of Boolean functions any derivation vanishes, since $f^2=f$ there and the product rule gives $D(f^2)=0$. [Baur and Strassen, *The complexity of partial derivatives*](https://web.vu.lt/mif/s.jukna/tropical/Baur-Strassen.pdf)

The graph predicate makes the missing coefficient explicit. Write $Y=AB$. Its unique representative multilinear in the Boolean proposal entries $C_{ij}$ for each binary $A,B$ is $\prod_{ij}(1+C_{ij}+Y_{ij})$. The coefficient of $\prod_{kl\ne ij}C_{kl}$ is $1+Y_{ij}$. Recovering this coefficient from an unrestricted Boolean verifier would require a way to perform extraction in degree $d^2-1$ after multilinearization.

Even an exact description of the graph as the common zero set of formal polynomials over all extensions fails to ensure the Jacobian hypothesis. The equations $(C_{ij}-(AB)_{ij})^2=0$ cut out exactly the product graph over every field of characteristic two, while their entire $C$-Jacobian is zero. This example diagnoses a failure of the inference from zero sets, independently of the cost of those particular equations. Applying either formal reduction to a Boolean RAM verifier would require a size-controlled conversion that supplies the relevant formal coefficients. The unrestricted SAT time lower bounds remain open.

Lean checks the mixed-coefficient perturbation and its directional derivative on every division-free expression in characteristic two with coefficients in $\mathbb F_2$, including the vanishing derivative of a square. The tensor-rank deduction over a general extension is the written argument above. [Formal coefficient identities](../lean/MatrixVerifierMixedCoefficient.lean)

The characteristic-zero deformation arguments and the distinction between the domains of correctness are given separately. [Real witnesses](real-witnesses-for-a-matrix-product.md) · [Complex verification equations](set-theoretic-matrix-graph-checks.md)
