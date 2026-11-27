# What quadratic checks of a binary matrix product must compute

Let $d\ge2$ and take $A,B,C\in\mathbb F_2^{d\times d}$. The space of Boolean functions of degree at most two in these $3d^2$ bits that vanish on all correct products is **exactly** the $d^2$-dimensional span of

$$
                      C_{ij}+\sum_{k=1}^d A_{ik}B_{kj}.
$$

Here degree of a Boolean function means degree of its unique multilinear polynomial. The conclusion still holds if the check only vanishes on honest products whose two factors each contain at most two ones. Alternatively, vanishing on a strictly greater than $15/16$ fraction of the uniformly sampled honest products suffices.

This gives a finite-field cost result for checking a proposed product. Consider a list of formal quadratic equations over $\mathbb F_2$, evaluated by a division-free circuit with $s$ nonscalar multiplication gates. Accept when all equations vanish. Require completeness on the sparse honest tests above and sound detection whenever a nonzero error $C+AB$ is supported in at most $r$ rows, with the locations unknown. Then $2s$ is at least the binary tensor rank of the product of an $r\times d$ matrix by a $d\times d$ matrix. There is a converse with at most a logarithmic factor in the number of multiplication gates. It even detects an error when just one nonzero column of the error matrix has weight at most $r$.

## Isolating the coefficients on honest inputs

Substitute $C=AB$ in a multilinear quadratic polynomial $h$, then reduce powers by $x^2=x$. For an unordered pair of distinct output positions $(i,j),(i',j')$, choose distinct inner indices $k,\ell$. The monomial

$$
                 A_{ik} B_{kj} A_{i'\ell} B_{\ell j'}
$$

has four distinct variables, also when the two output positions share a row or a column. It can come only from $C_{ij}C_{i'j'}$. The inner indices match each $A$ entry to its unique $B$ partner and thus recover the two output positions. In the expansion of that pair the selected term occurs once, including the cases with a shared outer index. The coefficient must vanish, eliminating every quadratic $CC$ term.

Next, to isolate $A_{uv}C_{ij}$ take a path $A_{ik}B_{kj}$ with $k\ne v$. The monomial $A_{uv}A_{ik}B_{kj}$ has a unique $A$ partner for $B_{kj}$. No remaining other term can supply it. The symmetric choice of an inner index different from the row of the extra $B$ eliminates every $BC$ term. What remains is $q(A,B)+L(C)$ for a linear $L$. Honest vanishing gives the Boolean identity $q(A,B)=L(AB)$, proving the classification. The displayed basic residuals are independent by their $C$ coordinates. For $d=1$ the additional relation $ac+c=0$ on $c=ab$ shows why two distinct inner indices matter.

The full pullback before eliminating coefficients has degree at most two in the $A$ group and at most two in the $B$ group. All its coefficients are determined from evaluations on supports of size at most two in each group, by inclusion-exclusion on subsets of each support. For the distributional version, a nonzero multilinear polynomial of degree at most four is one on at least a $1/16$ fraction of the cube. This follows by induction, splitting on a variable of a highest-degree monomial and adding the two slices. Thus either honesty condition implies identically zero pullback. We make no optimality claim for the $15/16$ threshold. There is a classical related factorization of bilinear functions that vanish whenever $AB=0$, called the zero-product-determined property of a matrix algebra. The calculation here classifies all quadratic checks involving the *claimed output* and identifies sparse data sufficient to force the identities. [Brešar, Grašič and Sánchez Ortega](https://users.fmf.uni-lj.si/bresar/documents/zpdmatrix.pdf)

## Extracting a rectangular product on the finite cube

Apply the classification to each test. The joint vector of answers on Boolean inputs is $L(C+AB)$ for a fixed binary linear map $L$. It suffices that every nonzero error in the first $r$ rows be detected even at the single factor pair $A=B=0$. On matrices supported in those rows, $L$ is then injective and has a linear left inverse on its image. Restrict $A$ to its first $r$ rows by setting the rest to zero, set $C=0$, and apply that left inverse. This computes the entire rectangular product. This extraction also works for arbitrary XOR-AND circuits whose actual test functions have Boolean degree at most two. Its conclusion in that case is a **Boolean** multiplication circuit, with no additional AND gates.

For the formal conclusion assume the test polynomials at $C=0$ have formal total degree at most two, in addition to the Boolean hypotheses. Their mixed $(1,1)$ components now agree formally with those of $L(AB)$. A square of one variable can change a pure linear coefficient on Boolean inputs and cannot change any mixed $A_{ik}B_{k'j}$ coefficient. Truncate the original circuit at $A=tX$, $B=uY$, $C=0$, $t^2=u^2=0$. Each multiplication propagates earlier mixed terms linearly and adds just two new products of one $X$-linear and one $Y$-linear form. All mixed outputs lie in the span of these $2s$ separable products. A constant linear output decoder preserves that span. Writing $R_2(r,d,d)$ for the corresponding tensor rank over $\mathbb F_2$ gives $R_2(r,d,d)\le2s$. Only the formal outputs at $C=0$ need the degree bound. High intermediate degrees can cancel. [Simultaneous gate count](../lean/GraphVerifierMixedProducts.lean)

The formal hypothesis can also be replaced by the narrower condition that, after $C=0$, no monomial supported on precisely one $A$ variable and one $B$ variable has a repeated exponent in either variable. Higher-support terms never yield such a pair under Boolean multilinearization. Without some control of this kind, even $(A_{11}B_{11})^2$ has the correct functional mixed coefficient and zero formal $(1,1)$ component.

There is a statistical version. Give the checker at most $2^b$ random seeds before its tests. For each seed use the same degree and cost hypotheses, allowing different equations. Suppose the average probability of rejecting a uniformly sampled honest product is at most $\epsilon$. Call a seed good if all its checks vanish on every honest product. Each other seed fails on at least $1/16$ of honest pairs, so their total mass is at most $16\epsilon$. If each promised wrong instance is detected with probability greater than $16\epsilon$, some good seed detects it. Stacking all good seed circuits yields

$$
                              2^{b+1}s\ \ge\ R_2(r,d,d).
$$

This argument does not pay for enumerating witnesses. An existential witness before the equations changes their honest completeness condition and is outside the conclusion.

## Matching the error threshold

Let $w=\lceil\log_2(d+1)\rceil$ and choose distinct nonzero $\alpha_1,\ldots,\alpha_d\in\mathbb F_{2^w}$. For each error column $e$, test the $r$ field syndromes $\sum_i\alpha_i^t e_i$ for $0\le t<r$. A Vandermonde minor on any at most $r$ positions has full column rank. Expanding into binary coordinates gives a fixed binary $rw\times d$ map $P$. Compute $(PA)B+PC$ and test the entries for zero. A nonzero error column with at most $r$ changed bits cannot pass. The row set may differ in each column. Split $P$ into at most $w$ blocks of $r$ binary rows. Each block costs at most $R_2(r,d,d)$ nonscalar gates, since the surrounding linear transformations are free in this measure. The test equations are formal quadratics. The optimum cost, even with this stronger soundness requirement and full honesty, is consequently between $R_2(r,d,d)/2$ and $w R_2(r,d,d)$. This comparison concerns multiplicative cost. [Error-correcting codes in matrix verification, Bennett et al.](https://arxiv.org/abs/2309.16176)

For $r=\lceil d^\rho\rceil$, $0<\rho\le1$, apply the rectangular exponent in the linked matrix preprints. The asymptotic exponent of the optimal number of nonscalar gates is exactly

$$
                     2+\frac{(\max(0,2\rho-1))^2}{4\rho}.
$$

Indeed the rectangular tensor-rank exponent equals the arithmetic exponent by the usual blocking and tensor-power conversion. For a fixed integer shape $(r,d,d)$, tensor powers yield exponent at most $\log_d R_2(r,d,d)$ at relative dimensions $(\log_d r,1,1)$, so the stated rectangular exponent also gives a finite-size rank lower bound. Thus a deterministic $d^2(\log d)^{O(1)}$ multiplication budget in this model forces $r\le\sqrt d\,2^{O(\sqrt{\log d\,\log\log d})}$. The matching upper bound is at the exponent scale. The exponent formula is an input from the preprints. [Exact rectangular exponent and model](https://github.com/openai/math/blob/main/lean/docs/107.md)

## Consequence for the SAT attempt

An $O(n)$ deterministic SAT solver on the ordinary bit RAM would verify binary matrix products in $d^2\operatorname{polylog}d$ native steps via the explicit mismatch formula. The result above works directly on binary data. It specifies a conversion that would suffice for a contradiction: realize that computation by a deterministic nearly quadratic multiplicative-cost verifier with the stated quadratic outputs, even only for errors confined to $d^{1/2+\delta}$ rows for some fixed $\delta>0$. The SAT hypothesis does not supply that conversion. A generic execution witness already permits all Boolean gates to be checked by local quadratic equations, but the equations involve additional guessed variables. Eliminating these variables while retaining the cost and form of the checks is a separate mathematical requirement. [Explicit mismatch formula](verifying-matrix-products-from-sat.md) · [Finite-field obstruction to generic lifting](finite-fields-for-matrix-graph-checks.md)

The exhaustive audit computes the quadratic relation space on the graph at $d=2,3$ and obtains exactly the predicted dimensions 4 and 9, also using only the sparse honest evaluations. It checks syndrome detection and reconstruction on small instances. Lean verifies the pivot identifications in the coefficient proof. Historical priority for the finite-volume cost comparison and the threshold specialization has not been established. [Finite audit](../audits/quadratic_product_checks_audit.py) · [Formal coefficient lemmas](../lean/QuadraticProductChecks.lean)

Even agreement of Boolean coefficients on a large range of degrees does not perform the formal extraction. A near-quadratic Boolean circuit can match every coefficient of the matrix trilinear form of degree up to $\lfloor d^{4/3}\rfloor$ in each block by counting triangles on sparse inputs. Matching singleton inputs already fixes the whole trilinear component of the canonical Boolean polynomial, and costs only $O(\log d)$ AND gates. [Sparse Boolean tests and their circuit costs](sparse-boolean-tests-of-the-matrix-tensor.md)
