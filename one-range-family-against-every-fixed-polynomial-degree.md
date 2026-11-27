# One low-space family that hits a low-degree computation path

Fix $0<\epsilon<1$ rational, $m=\lfloor n^\epsilon\rfloor$, and $s=\lfloor n^{\epsilon^2}\rfloor$. There is a **single seed-independent** family $C_x(u)=H(x)$, with polynomial-time, polylogarithmic-space bit evaluation, with the following property for **every** fixed $D\ge1$. On any path described by $o_D(n)$ binary tests of degree at most $D$ over $\mathbb F_2$, for any proposed $m$-bit output whose bits have degree at most $D$ on that path, some actual input on the path makes the proposed output equal to $H(x)$. In fact a sufficiently small constant multiple of $n$ tests suffices for the conclusion. Thus if a sequence of proposed avoiders has such a path at infinitely many lengths for a common fixed $D$, the very same evaluator hits it at those lengths.

This uses the classical generalized-inner-product discrepancy bound and the conversion from correlation to hitting low-degree varieties. The additions here are a vector output, a path-dependent candidate output, and one uniform function working for all fixed degrees. The journal already gives related scalar bounds for ordinary SAT, including a packed cubic verdict and all-fields modular guards. [Babai, Nisan and Szegedy](https://www.sciencedirect.com/science/article/pii/002200009290047M) · [Golovnev, Kulikov and Williams, Section 5.2](https://eccc.weizmann.ac.il/report/2018/192/revision/2/download/) · [Packed SAT runs](quadratic-explanations-of-packed-sat-runs.md) · [Word values over a specified field](processing-word-values-over-every-field.md)

## The construction and the correlation estimate

Partition the first $\sum_{j\le J}\lfloor n/2^j\rfloor$ input bits into consecutive slices of lengths $b_j=\lfloor n/2^j\rfloor$ for $1\le j\le J=\lfloor\log_2 n\rfloor$. Ignore a slice unless $b_j\ge m+j+1$. On a retained slice set $q_j=\lfloor(b_j-m+1)/(j+1)\rfloor$ and use $j$ banks $U_1,\ldots,U_j$ of $q_j$ bits and a bank $V$ of $q_j+m-1$ bits. Discard any spare bits. For $0\le h<m$ add to $H_h$ the quantity
$$
                   \sum_{i=0}^{q_j-1}V_{i+h}\prod_{a=1}^j (U_a)_i
                    \pmod 2 .
$$
Use zero for exceptional empty layouts. Each requested bit can be computed by repeated input scans with counters and one running parity. The seed is unused. For each fixed $D$ the slice $j=D$ is eventually present with $q_D=\Theta_D(n)$.

Take any nonzero $m$-bit mask $\lambda$ and any Boolean polynomial $Q$ in the input bits of degree at most $D$. Condition on every bit outside slice $D$. In $\lambda\cdot H$, the last bank of that slice becomes $V'_i=\sum_h\lambda_h V_{i+h}$ for $0\le i<q_D$. These $q_D$ forms are independent, by the first nonzero shifted diagonal. Complete them to a basis and condition on the extra coordinates. The affine substitutions keep $Q$ of degree at most $D$. The remaining sign is that of generalized inner product on $D+1$ independent banks of $q_D$ bits, perturbed by $Q$.

For completeness, classify each monomial of $Q$ by one of the $D+1$ banks it misses. The sign of $Q$ factors into bounded functions, each independent of its designated bank. Applying Cauchy–Schwarz once for each bank, duplicating its variables and removing its missing-bank factor, bounds the $2^{D+1}$st power of the absolute correlation by the mean of the product of all cube-corner inner-product signs. At each coordinate the cube sum in the exponent is the product of $D+1$ independent difference bits. Its sign has mean $1-2^{-D}$. Coordinates are independent. Removing the conditioning yields
$$
        |\mathbb E_x(-1)^{\lambda\cdot H(x)+Q(x)}|
           \le (1-2^{-D})^{q_D/2^{D+1}}=:\rho_D .
$$

## A test that hits the proposed output on its actual path

Fix a realized sequence of $t$ binary observations. Extend their representatives to polynomials $P_1,\ldots,P_t$ of degree at most $D$ on the full input cube. Each representative need only agree with its test on the inputs surviving the previous answers. For the designated answers, the path indicator $I$ is the product of $t$ corresponding bit indicators. It is nonzero, has multilinear degree at most $Dt$, and has mean at least $2^{-Dt}$. The last bound is the binary Reed–Muller minimum-weight bound. For example, fixing variables outside a maximum-degree monomial leaves that full monomial in the restricted polynomial on every such restriction, so at least one assignment to its own variables has value one.

Let $A$ denote the polynomial output representatives on this path. For every $m$-bit word $v$,
$$
\left|\Pr[I=1,\ H+A=v]-2^{-m}\Pr[I=1]\right|\le (1-2^{-m})\rho_D .
$$
To see this, expand the output equality in binary characters. For each nonzero mask, expanding $I$ in the signs of the individual tests gives coefficients of absolute sum at most one. The phase from any sum of tests and any masked output still has degree at most $D$. The correlation bound applies to every term. In particular every $v$, including zero, occurs on the realized path if $Dt+m\le\log_2(1/\rho_D)$. Here $m=o(n)$ and the right side is a positive $D$-dependent constant times $n$. The observations may be chosen adaptively. No density or depth assumption is made on other paths.

For a native program one may make known-control processing free as long as each stored bit used on the current path retains a degree-at-most-$D$ representative in the original input bits. A charged native operation can disclose the actual bits of its boundedly many operands, an effective address, the selected cells and control data as necessary. Before the operation these have bounded-degree representatives on the surviving inputs. Fixing $O(w)$ bits per charged step gives the theorem on the resulting path, including an affine or bounded-degree final output that need not be constant. Thus **every run** of an everywhere-avoiding program incurs $\Omega_D(n/w)$ charged instructions, for each fixed $D$ under that convention, even with arbitrarily much free bounded-degree preprocessing along the run. An unresolved branch or unresolved effective address must be accounted for in the path tests. Reusing a previously resolved word does not charge for it again.

There is a single scan-time escape. Compute $H_0$ by wordwise AND of aligned pieces across the $j+1$ banks, XOR the accumulated words, take their parity, and output the opposite bit followed by zeros. A shifted packed read takes at most two native reads per word. Remainder padding and bank boundaries cost $O(\sum_{j\le J}(j+1))=O(\log^2 n)$ word operations, and the total lengths of the banks are at most $n$. Fold the parity accumulator in $O(\log w)$ shifts. Public layout computation, including integer roots for fixed rational $\epsilon$, uses polylogarithmic time. The total is $O(n/\log n)$ word steps. This same program escapes the family at all large lengths. The unrestricted infinite-hit premise therefore still needs a family that defeats programs doing at least a full scan's worth of processing. The exact affine threshold for a single quadratic slice admits a separate matching construction. [Exact affine threshold](affine-avoidance-of-shifted-inner-products.md)

The small cases exhaust every degree-bounded phase at the tested sizes, including 32,768 degree-three phases for four banks, and check every nonzero mask. [Finite correlation and minimum-weight audit](shifted_degree_path_audit.py)
