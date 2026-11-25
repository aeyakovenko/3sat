# Certifying a correct matrix product with existential real witnesses

Consider a finite real arithmetic computation tree with field operations and sign tests. The tree receives $d\times d$ real matrices $A,B,C$ and may read an existentially chosen tuple of real numbers. Require that some witness makes it accept exactly when $C=AB$. Write $T$ for a bound on the length of an accepting computation needed on each correct product. Then

$$
                  \underline R_{\mathbb C}(\mathrm{MM}_d)=O(T),
$$

where $\underline R$ denotes geometric border rank. In fact a path whose projected set of correct products has nonempty interior in the $(A,B)$ parameters already satisfies this bound. Combining this argument with the November 24 matrix preprint's $\underline R_{\mathbb C}(\mathrm{MM}_d)\ge d^{9/4}$ gives an $\Omega(d^{9/4})$ lower bound in this real verification model. The argument below is a research derivation. Its historical priority and the full proof have not been independently refereed outside this project. [Matrix preprint and formalization scope](https://github.com/openai/math/tree/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026)

Künnemann asked how efficiently a correct matrix product can be certified nondeterministically and studied several models and reductions. Here each real field operation costs one step, with a fixed finite arithmetic and sign-test tree for each dimension. [Künnemann, ESA 2018](https://arxiv.org/abs/1806.09189)

The side certified matters. An incorrect product has a certificate consisting of the indices of one wrong entry. After selecting the row and column, a finite arithmetic tree checks one dot product in $O(d)$ operations. Soundness for **every** witness on an incorrect product is what the lower bound uses. A randomized vector test has a different quantifier. Bürgisser, Karpinski and Lickteig already singled out deterministic versus randomized real matrix-product membership in Example 1 of their algebraic test-complexity work. Bürgisser later used deformations to relate testing a scalar polynomial graph to approximate computation of the polynomial. Bennett and coauthors give a verification barrier for a specified class of linear-algebraic tests. [Bürgisser, Karpinski and Lickteig](https://doi.org/10.1006/jcom.1993.1016) · [Bürgisser, Corollary 1.5](https://arxiv.org/abs/1812.06828) · [Bennett, Gajulapalli, Golovnev and Warton](https://doi.org/10.4230/LIPIcs.APPROX/RANDOM.2024.42)

## Represent one accepting path by real equations

Treat the entries $a,b$ of $A,B$ as independent indeterminates. Order $\mathbb R(a,b)$ and take its real closure $K_0$. Correctness and completeness for a fixed finite tree transfer to real closed extensions, since they are first-order statements over the reals. There is a path and a satisfying assignment at the generic correct product. If a particular path has a set of accepting $(A,B)$ parameters with nonempty real interior, choose the ordering to put the generic point in that interior. This is possible by taking an open box in it and algebraically independent infinitesimal displacements within the box.

Freeze the path and let $Z$ stand for the proposed $C$ together with its used witnesses and auxiliary registers. Express the path as polynomial equations

$$
                         g_i(a,b,Z)=0 .
$$

An arithmetic gate can be given its own output variable and one equation. For division $v=u/w$ include $wv=u$ and a witness for $w\ne0$. For a test $p>0$ use $p y^2=1$, for $p\ne0$ use $p y=1$, and for a weak nonnegative test use $p=y^2$. Reverse signs for the opposite inequalities. Equality branches give equations directly. These transformations have constant cost per instruction. They make the real solution set closed in the enlarged variables, including paths that required strict signs. All equations and the sum $\Phi=\sum_i g_i^2$ can be evaluated with $O(T)$ arithmetic gates. On this path a real zero exists over $K_0$. For **every** real zero, its $C$ coordinates equal $ab$, by path soundness. These statements persist over all real closed extensions of $K_0$. The other coordinates need not be isolated or uniquely determined.

## Select a regular nearby critical point

Let $p$ be the number of $Z$ coordinates. Adjoin $p$ new algebraically independent constants $W$ over $K_0$, take a real closure $K$ of the ordered extension, and introduce an independent positive infinitesimal $\epsilon$. Work in the real closed field of real algebraic Puiseux series over $K$. Each element has a formal expansion with a common denominator for its exponents. For a bounded series its residue is the coefficient of $\epsilon^0$. The real closed field facts used here include attainment of extrema of polynomial functions on closed bounded balls and transfer of polynomial sentences. [Basu, real closed fields and infinitesimal deformations](https://www.math.purdue.edu/~sbasu/OWF09/lecture2.pdf)

Minimize

$$
                   \Phi(a,b,Z)+\epsilon\sum_{i=1}^p(Z_i-W_i)^2.
$$

Fix one unperturbed zero $Z_0\in K_0^p$. Outside a ball about $W$ of radius strictly larger than $\|Z_0-W\|$, the objective exceeds its value at $Z_0$. A minimum $Z_\epsilon$ on this closed ball is therefore an unconstrained minimum in its interior. Comparison with $Z_0$ gives $\|Z_\epsilon-W\|\le\|Z_0-W\|$ and $0\le\Phi(a,b,Z_\epsilon)\le\epsilon\|Z_0-W\|^2$. All coordinates have nonnegative valuation, and their residues solve the original equations since a sum of real squares is zero only at a common zero. In particular

$$
                 \operatorname{res}(C_\epsilon)=ab.
$$

There is no need to differentiate a minimization operator. At this interior point the critical equations are

$$
   F(a,b,Z_\epsilon)=0,\qquad
   F=\nabla_Z\Phi(a,b,Z)+2\epsilon Z-2\epsilon W .
$$

The entries of $\epsilon W$ are algebraically independent over $K_0(\epsilon)$ and belong to $K_0(\epsilon,Z_\epsilon)$ by these equations. Hence the $p$ entries of $Z_\epsilon$ are algebraically independent over $K_0(\epsilon)$. The polynomial $\det(\operatorname{Hess}_Z\Phi(a,b,Z)+2\epsilon I)$ is nonzero as a polynomial in $Z,\epsilon$, because its leading coefficient in $\epsilon$ is $2^p$. It follows that the Jacobian $J=F_Z(a,b,Z_\epsilon)$ is invertible. This step works even when every original equation has zero gradient everywhere on the product graph.

Reverse differentiation supplies one simultaneous arithmetic circuit for all of $\nabla_Z\Phi$ with $O(T)$ nonlinear gates. Zero gradient coordinates can be represented by zero wires. The added regularizer in the gradient is affine over the coefficient field and contributes no nonscalar multiplications. The size of the Hessian and the cost of computing its inverse are immaterial in the next step because a fixed linear output map cannot increase tensor rank. [Baur and Strassen, *The complexity of partial derivatives*](https://doi.org/10.1016/0304-3975(83)90110-X)

## Differentiate at fixed perturbation, then take the residue

The partial derivations with respect to the entries of $a,b$ extend uniquely through the characteristic-zero algebraic coefficient extensions, fixing $W$. On Puiseux expansions apply them coefficient by coefficient with $\epsilon$ fixed. They commute, preserve nonnegative and strictly positive valuation bounds, and commute with taking the coefficient of degree zero. This follows directly from the series expansion and the finite product rule for each coefficient. Equivalently these extensions agree on algebraic series with the derivations obtained by differentiating their separable minimal equations.

Take independent formal directions $X$ in the first matrix and $Y$ in the second. At the selected point put $U=D_a Z_\epsilon[X]$ and $V=D_b Z_\epsilon[Y]$, linear in $X$ and $Y$ respectively. Consider the mixed coefficient of the circuit for $F$ under

$$
 (a,b,Z)\longmapsto (a+tX,\ b+uY,\ Z_\epsilon+tU+uV),
                 \qquad t^2=u^2=0 .
$$

Write that vector of coefficients as $M(X,Y)$. Differentiating $F(a,b,Z_\epsilon)=0$ twice gives

$$
           J\, D_aD_b Z_\epsilon[X,Y] = -M(X,Y).
$$

For a product of two gate values $v,w$, its mixed coefficient is $v_{00}w_{11}+v_{11}w_{00}+v_{10}w_{01}+v_{01}w_{10}$. The first two terms propagate earlier mixed outputs linearly over the Puiseux field. Each of the last two is one linear form in $X$ times one in $Y$. Input wires have zero mixed coefficient under this substitution. Thus every mixed output belongs to the linear span of at most two new separable products per nonscalar multiplication in the circuit. Division, if used at a nonzero denominator, has the same bound by equating coefficients in $vq=w$. Applying the fixed linear map $-J^{-1}$ and projecting to $C$ preserves that span. Hence the tensor of $D_aD_b C_\epsilon$ has rank $O(T)$ over the Puiseux field.

Its entries have nonnegative valuation. Their residues are the coefficients of $D_aD_b(ab)[X,Y]=XY$. To check descent, take any complex polynomial equation vanishing on the Zariski closure of tensors of rank at most the stated bound. It vanishes on sums of that many simple tensors over the complexified Puiseux field as well, by the polynomial parametrization. Specializing the integral entries at $\epsilon=0$ preserves this equation. This puts the ordinary matrix multiplication tensor in the same complex border-rank locus, as claimed. The argument applies equally to the graph of any fixed real bilinear map.

For a finite tree, a union of finitely many semialgebraic sets of dimension less than $2d^2$ has Lebesgue measure zero in $(a,b)$. Thus for almost every correct product, even its shortest sound accepting witness costs $\Omega(\underline R_{\mathbb C}(\mathrm{MM}_d))$ operations. With the cited matrix theorem, this is superlinear in the number of real input entries. The input model permits arbitrary real entries and scalar arithmetic and sign tests. The question about ordinary SAT instead charges the encoded number of **bits** on a logarithmic-word RAM.

## The attempted transfer to Boolean SAT

A linear-time SAT algorithm would give deterministic $d^2\operatorname{polylog}d$ Boolean verification of $AB=C$ over $\mathbb F_2$, and even an evaluator for the scalar matrix trilinear form. To use the theorem above one would need to turn a fast Boolean procedure into a sound short real witness relation for correct products at generic real $A,B$. Simply imposing bit equations removes all such generic inputs. The argument cannot start its deformation there.

Even correctness on all rational matrices can behave differently. In a unit-cost real arithmetic model allowing an arbitrary real constant $\theta$ transcendental over $\mathbb Q$, take $v=(1,\theta,\ldots,\theta^{d-1})$. Checking $A(Bv)=Cv$ uses $O(d^2)$ operations and is exact for rational matrices by linear independence of the powers over $\mathbb Q$. It accepts some incorrect products on real inputs for $d\ge2$, since a nonzero real row can annihilate $v$. This example is about verifying rational products in that constant model. It explains precisely why a dense collection of valid discrete inputs cannot replace generic real soundness.

On **all integer matrices** even the transcendental constant can be removed. Take the integer $q=3+\sum_{ij}(A_{ij}^2+B_{ij}^2+C_{ij}^2)$ and $v=(1,q,\ldots,q^{d-1})$. Each integer entry of $AB-C$ has absolute value strictly below $q$, by $2|ab|\le a^2+b^2$ and $|c|\le 1+c^2$. In any nonzero row, its least-index nonzero coefficient survives reduction modulo $q$ after dividing the row's evaluation by the corresponding power of $q$. Thus the same matrix-vector test is exact in $O(d^2)$ unit-cost operations, for unbounded integer entries and with only small integer constants in the program. The values can need order $d\log q$ bits. Using negative powers and reversing the column order can bound the magnitude of the vector entries, while their exact denominators still have this bit length. This is the large-integer verification technique of Korec and Wiedermann. It rules out using correctness on arbitrarily large integer grids alone to transfer the real theorem, even for one arithmetic circuit per dimension. [Korec and Wiedermann](https://doi.org/10.1007/978-3-319-04298-5_33)

Lean verifies the simultaneous two-products-per-gate span for a shared circuit, including quotients with unit base coefficient. The minimization, genericity, differentiation in the Puiseux field and border-rank specialization above remain paper arguments. [Formal gate-counting lemma](GraphVerifierMixedProducts.lean)

The regular-Jacobian case also has a direct proof over other characteristics, and checking graph equations over an algebraically closed field of characteristic zero admits a direct deformation with a factor of two in the nonscalar gate count. These are different assumptions on the verifier. The unrestricted Boolean SAT running-time bound remains open. [Boolean verifier and mixed-coefficient lemma](verifying-matrix-products-from-sat.md) · [Complex graph equations](set-theoretic-matrix-graph-checks.md)
