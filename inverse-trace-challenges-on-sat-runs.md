# What can local challenges certify about an unrestricted SAT run?

There is an explicit family of width-three formulas on which a randomized proof of rejection has the following cost. Write $d$ for the number of independently varying input pins, $s$ for proof bits, $a$ for adaptive parity queries made after receiving the proof, and $k$ for the largest number of coordinates needed to certify a failed challenge. Each survey leaf may choose its own linear coordinate system. For any fixed completeness and soundness gap,

$$
                   s+a+1=\Omega(d\log k/k)
$$

in the range specified below. The number of challenges, the computation between coordinate observations, the running time of the SAT solver and its workspace are all unrestricted. A separate conclusion concerns **actual input reads**. On every input a correct deterministic solver must expose at least $d/2$ independent bits, even allowing it to read arbitrary parities of the pins. If it saves many more reads than usual on this family, the span of the bits it reads must itself carry information. We give a sharp example at $d/2$ and a tail estimate for this information cost.

## An ordinary explicit formula

Take a sufficiently large power of two $d$. Choose a public binary irreducible polynomial $P$ of degree $d$ and use the coefficient basis of $E=\mathbb F_2[Z]/P$. Write $\operatorname{inv}_0(0)=0$ and $\operatorname{inv}_0(x)=x^{-1}$ elsewhere. The sign

$$
 f(x)=(-1)^{\operatorname{Tr}_{E/\mathbb F_2}(\operatorname{inv}_0(x))}
$$

is balanced because inversion with this convention is a permutation and the trace is a nonzero linear functional. Give the formula $d$ units pinning the coefficient bits of $X$ to $x$. Introduce witnesses $Y,Q$ of degrees less than $d$. When $X=0$ require $Y=0$. Otherwise require the ordinary **polynomial** identity $XY=1+PQ$. Finally require $\operatorname{Tr}(Y)=1$. In the nonzero case division by $P$ shows that the unique field inverse supplies such a quotient, and the identity forces $Y$ to be that inverse. The zero case has trace zero. Thus $f=+1$ exactly on the unsatisfiable instances.

Compile the two ordinary polynomial products, comparisons, branch and linear trace into bounded fan-in Boolean gates, then into their width-three gate equivalences. Over $\mathbb F_2$ the polynomial multiplication circuit costs $O(d\log d\log\log d)$ gates by Cantor and Kaltofen. Hardwire $P$ and the trace coefficients for this length. Fixed-width variable identifiers and clause records give an encoded bit length $N=O(d\log^2 d\log\log d)$ with $N\ge d$. Separate successive pin signs by enough fixed records that a native input word touches at most one pin. The cost of this spacing is $O(d\log d)$ bits for any fixed word-width convention. All other words are public. Every instance is an ordinary formula with the same layout for that $d$. The size argument requires no fast uniform procedure for choosing $P$. [Cantor and Kaltofen, polynomial multiplication over arbitrary algebras](https://kaltofen.math.ncsu.edu/bibliography/91/CaKa91.pdf)

## Correlation after a parity survey

Use base-two logarithms. Suppose $(\log d)^2\le k\le d/(4096\cdot512)$ and put $b=\lfloor(\log k)/2048\rfloor$. For every width-$k$ CNF indicator $H$ in any fixed binary basis, of arbitrary clause count, Li and Zhong bound $|\mathbb E fH|$ by $\rho=5\cdot2^{-3db/(4096k)}$. Their estimate also holds with $f$ replaced by $f\chi_u$, where $\chi_u$ is any binary linear character of the field's additive group. Indeed in their Lemma 4.2 a moment term at $2t$ points has the product of characters at $A+L_0z_i$. This equals $\chi_u(\sum_i L_0z_i)$ independently of the random translation $A$. It is one on the paired tuples. On the other tuples the same absolute character-sum bound applies. Proposition 4.3 then proceeds with absolute correlations and removal of translations using coordinate flips. Corollary E.1 follows with the original constants. The argument works for each fixed basis because the field estimate is on linear subspaces and the Boolean restrictions use the chosen coordinates. [Li and Zhong, §4 and Corollary E.1](https://arxiv.org/html/2610.27127v1#A5.SS1)

For a nonempty affine cell $C=x_0+W$, the Fourier expansion of $1_C$ has $2^{\mathrm{codim}\,W}$ coefficients of absolute value $2^{-\mathrm{codim}\,W}$, indexed by $W^\perp$. Thus $|\mathbb E f1_CH|\le\rho$, even when the coordinates of $H$ are chosen specifically for $C$. The estimate is for **unnormalized** mass. The expectations hereafter are over the full uniform pin vector unless specified.

## Proof first, then coins and universal challenges

There are at most $2^s$ proof strings. For each fixed proof, first allow an adaptive survey of at most $a$ linear bits of $x$. The resulting tree has at most $2^a$ nonempty affine leaves. At each leaf select one binary linear coordinate system. The proof, survey and leaf basis are fixed before the independent verification seed. For this seed the proof passes when **all** its challenges pass. Require that for each failing input at the leaf, at most $k$ coordinate answers suffice to force failure throughout the leaf. These answers and even the offending challenge may depend on the input. This includes an arbitrary family of adaptive depth-$k$ tests in the leaf basis.

For one proof, leaf and seed, forbid every failed partial assignment by its single opposite clause. This gives a width-$k$ CNF agreeing with the pass predicate everywhere on that leaf. Intersecting the pass predicates of any $h$ seeds just combines their clauses. The width stays $k$ because the leaf basis is shared across repetitions. Summing the affine-cell estimate over the leaves and averaging over the independent seeds gives

$$
       |\mathbb E_x f(x)p_\sigma(x)^h|\le2^a\rho ,
$$

where $p_\sigma(x)$ is the probability that all challenges pass for proof $\sigma$. The number of challenges and repetitions does not occur in the right side.

Assume each unsatisfiable input has a proof with $p_\sigma(x)\ge\alpha$, while on every satisfiable input every proof has $p_\sigma(x)\le\beta$, for constants $1\ge\alpha>\beta\ge0$. Summing the signed expectations, balance gives a lower bound $(\alpha^h-2^s\beta^h)/2$. When $\beta>0$ choose $h=\lceil(s+1)\ln 2/\ln(\alpha/\beta)\rceil$, and use $h=1$ for $\beta=0$. Hence $2^{s+a}\rho\ge\alpha^h/4$. Taking logarithms proves the stated bound. In particular $s+a+k+1=\Omega(\sqrt{d\log d})$. To see this also outside the stated width range, if $k\ge\sqrt{d\log d}$ its own cost suffices. Otherwise widen the tests to $\lceil\sqrt{d\log d}\rceil$ and apply the estimate. In encoded bits this gives $\Omega(\sqrt{N/(\log N\log\log N)})$ on this family.

This applies to proofs about a fixed, globally correct SAT solver. For example, a proof may specify times and sets of permissible complete configurations and assert that each transition block preserves the claimed implication until the solver rejects. With sets fixed at a survey leaf, failure has a concrete witness consisting of a starting configuration and its execution to an excluded configuration. Fix the pin bits read by that execution. The same witness still fails on every completion in the leaf. Extra source queries in endpoint tests can also be counted in $k$ if their replies suffice to keep the membership and nonmembership facts fixed. Induction from the genuine initial state to a rejecting controller supplies soundness for an exact check. Random tests are also covered when they meet the per-input acceptance guarantees above. The proof gives a cost for these certificate systems on actual UNSAT instances. A time lower bound would further require a theorem forcing a fast solver to admit such inexpensive certificates.

Two variations locate the dependence on the verification protocol.

- If a seed changes the basis, the argument still applies whenever its tested coordinates are sums of at most $l$ coordinates of a shared leaf basis plus linear combinations of $v$ shared exceptional forms. Append those $v$ forms to the survey and fix at most $lk$ ordinary coordinates per failure. The same bound then uses parameters $(s,a+v,lk)$ in the applicable width range.
- If the prover sees the coins first, assume instead that at most $u$ proofs pass at a point for any one seed. Let proofs for a given seed share the survey and the basis on each leaf. Inclusion-exclusion for the union terminates at $u$. Every intersection of pass sets again obeys the cell bound. For union completeness $\alpha$ and soundness $\beta$, this gives $2^a\rho\sum_{j=1}^{u}\binom{2^s}{j}\ge(\alpha-\beta)/2$. For $u=1$ there are only singleton terms and surveys and bases can be chosen separately for each proof and seed. The first theorem allows arbitrary overlap and requires the proof before the seed.

## Rank and information on the actual read sequence

Put $q=2^d$. Every normalized binary Fourier coefficient of $f$ has absolute value at most $2/\sqrt q$. For nontrivial characters, the unnormalized sum is $1+K$ for a binary Kloosterman sum over $q-1$ terms. The Weil bound gives $|K|\le 2\sqrt q$, and $K$ is odd while $2\sqrt q$ is an even integer. The constant coefficient is zero. [Lachaud and Wolfmann, binary Kloosterman sums](https://doi.org/10.1109/18.54892)

Give a deterministic solver the power to inspect any linear bit of $x$ adaptively. Include any private pin met by a native input load, even when the instruction ignores its bits. Public operations and work memory may be arbitrary. A halting transcript whose queried forms span $V$ of rank $r$ determines a coset of $V^\perp$. Every point of this coset gives the same replies and verdict. On it the absolute conditional expectation of $f$ is one. The zero constant coefficient and the remaining $2^r-1$ coefficients bound this expectation by $(2^r-1)2/\sqrt q$. Consequently $r\ge d/2$ **on every input of either verdict**. The subfield of order $\sqrt q$ realizes equality as a rejection certificate. Its relative trace to itself from the degree-two extension vanishes on each of its elements, including the inverse of any of its nonzero elements. Its membership takes $d/2$ parity equations. An algorithm on the promised family can test membership first and decide the other cases by reading the remaining inputs. On ordinary formulas template validation can read public words, separately from the conditional parity-query statement.

There is a stronger constraint on which spans the solver can use frequently. Let $U_x$ be the span at termination. For a fixed space $V$ of rank $r$, if $U_x\subseteq V$ then the whole coset $x+V^\perp$ is monochromatic. The conditional expectation of $f$ on the coset is a function whose Fourier expansion retains just the frequencies in $V$. Parseval gives

$$
 \Pr[U_x\subseteq V]\ \le\ \sum_{v\in V}|\widehat f(v)|^2
 \ \le\ 4(2^r-1)/2^d .
$$

Allow a collection of subspace descriptions with lengths $\ell_i$ satisfying $\sum_i2^{-\ell_i}\le1$. On all but at most a $2^{-j}$ fraction of inputs, **every** description $i$ whose space $V_i$ contains the actual read span satisfies $\dim V_i+\ell_i\ge d-2-j$. Indeed the bad descriptions have individual probabilities at most $2^{-j-\ell_i}$. This permits choosing the description in hindsight on the real execution. In particular, with $x$ uniform, the Shannon entropy satisfies $H(U_x)+\mathbb E\dim U_x>d-2$, by taking minus the logarithm of the bound for $\Pr[U_x=V]$ and averaging. Conditioning on a specified verdict costs at most one extra bit in the tail bound. For the subfield membership test, the single early-rejection coset has mass $2^{-d/2}$ at rank $d/2$, within a constant factor of the general fixed-space upper bound.

This tests the history-compression idea suggested by deterministic linear-time MST. A short index of the future read span would force the solver to expose nearly all the independent pins. Counting unique reads alone still stops at $d$ and the explicit formula has $N\ge d$ bits. Another obstruction to a time transfer is the lack of an implication from elapsed time to the size of a sound checkpoint proof. Historical priority for the certificate and transcript formulations is unverified. [MST manuscript](https://eccc.weizmann.ac.il/report/2026/339/) · [Earlier SAT test of MST histories](dlmst-history-transfer.md)

The Lean file verifies adaptive test trees, conjunction without width growth, and cancellation in an even character product. The finite audit checks the field witnesses, Fourier identities, clause intersections and independent repetitions at small dimensions. The asymptotic estimates and their application to actual formulas above are paper arguments. [Lean lemmas](ChartChallengeIntersections.lean) · [Finite audit](inverse_trace_chart_audit.py)
