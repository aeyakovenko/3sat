# Recovering a matrix contraction from its Frobenius power after elementary edits

The [extension-field coefficient argument](frobenius-carries-in-an-extension-field-contraction.md) can produce a formal circuit for a Frobenius power of the matrix contraction. One possible next step is to feed field elements or commuting matrices to this circuit and recover the unpowered contraction with a linear readout. Such a readout, reusable after at most six elementary row or column additions, requires coefficient algebras of total dimension at least **$d^6$**. An extraction specialized to individual sparse triangles already needs $d^3$. These statements hold even if the encodings fed into the circuit may change arbitrarily at each request.

## The reusable readout

Fix $d\ge2$, $q=2^h$ with $h\ge1$ and the rational function field $K=\mathbb F_2(A,B,Z)$ on $3d^2$ independent entries. Set
$$T(A,B,Z)=\sum_{i,k,j} A_{ik}B_{kj}Z_{ij}.$$
Use finite-dimensional commutative $K$-algebras $E_a$, each with one fixed $K$-linear readout $\lambda_a:E_a\to K$. Write $D=\sum_a\dim_K E_a$. The algebras and readouts may contain rational functions of the **entire** symbolic input. Once chosen they are held fixed across the requested edits. On each request the decoder may form a $K^q$-linear combination of arbitrarily many scalars $\lambda_a(w^q)$ for arbitrarily chosen $w\in E_a$. Any evaluation of a formal circuit for $T^q$ in a commutative algebra outputs such a power, because the circuit identity survives substitution. Independent readouts of the same algebra can be charged by taking duplicate summands.

Let $\mathcal H$ contain products of zero, one or two matrices $I+e_{ij}$ with $i\ne j$, where $e_{ij}$ is a matrix unit. Request the actual value
$$T(P A Q,B R,Z),\qquad P,Q,R\in\mathcal H.$$
Each edit is a sequence of at most six binary row or column additions, preserves both operand ranks, and uses $O(d)$ scalar additions. The edited entries remain algebraically independent within the full data tuple.

**Theorem.** A decoder serving all these requests needs $D\ge d^6$.

* For any basis $v_1,\ldots,v_e$ of $E_a$, Frobenius additivity and $K$-linearity give
$$\lambda_a\!\left(\left(\sum_i c_i v_i\right)^q\right)
   =\sum_i c_i^q\lambda_a(v_i^q).$$
Thus all scalar answers belong to the same $K^q$-linear space $W$ of dimension at most $D$. This applies also to nonreduced commutative algebras. If input encodings lie in a common commutative subalgebra of a matrix algebra, its dimension can be used in this bound.
* The matrices in $\mathcal H$ span every binary $d$-square matrix. For $i\ne j$, $I+(I+e_{ij})=e_{ij}$. Adding $I$, $I+e_{ij}$, $I+e_{ji}$ and $(I+e_{ij})(I+e_{ji})$ gives $e_{ii}$. Expand $T(P A Q,B R,Z)$. The coefficient of $A_{ab}B_{kc}Z_{ij}$ is $P_{ia}Q_{bk}R_{cj}$. By trilinearity in $P,Q,R$, taking binary sums of the requested outputs therefore isolates **each** of the $d^6$ indicated monomials.
* These monomials are linearly independent over $K^q$. In a putative relation, clear denominators that are $q$th powers. The monomials from each resulting summand have the same exponent vector modulo $q$, different for different summands. No cancellation across them is possible.

The linear dimension is exact in the stated model. Use $E=K^{d^6}$ with one factor for each triple of entries, one from each bank. In that factor initially set just those three input entries to one and all others to zero. Perform the requested $P,Q,R$ edits in the corresponding coordinates. The unpowered contraction there is the associated binary coefficient, and raising it to $q$ preserves it. The readout weights this factor by its corresponding formal monomial and sums. The decoder pays for those coefficients if one prices its arithmetic work.

There is also an upper bound with local input encodings and a coordinate-sum readout. In the factor for entries $x,y,z$ use $K[u,v,w]/(u^q-x,v^q-y,w^q-z)$, of dimension $q^3$ with basis exponents below $q$. Initialize the three corresponding entries as $u,v,w$, compute the binary edits, and feed the resulting arguments to the powered circuit. Its value in this factor is the corresponding binary coefficient times $xyz$, in the constant coordinate. Sum the constant coordinates across factors. This gives total dimension $q^3 d^6$. For a family containing only masks that isolate one *actual triangle* each, the same proof and constructions give lower bound $d^3$, exact in the unrestricted-linear-readout model.

## Matrix traces and noncommuting encodings

The same argument applies in an associative algebra when the readout is cyclic, meaning $\lambda(uv)=\lambda(vu)$, and the actual returned element is a $q$th power. In the expansion of $\lambda((\sum_i c_i v_i)^q)$, partition the length-$q$ words by cyclic rotation. Their scalar coefficients and readouts are constant along each orbit. Every nonsingleton orbit has even size since $q$ is a power of two, so only the constant words contribute. This proves the same basis formula without commutativity. It does require an actual powered output; a commutative circuit identity need not survive an arbitrary noncommuting substitution. The cyclic power construction is classical. [Zimmermann on Külshammer's power maps](https://arxiv.org/abs/1005.2546)

For a full matrix algebra over $K$ any cyclic linear readout is $c\operatorname{tr}$ for a scalar $c$. It vanishes on off-diagonal units by cyclicity with a diagonal unit, and gives the same value on all diagonal units by applying cyclicity to $e_{ij}e_{ji}$. The basis formula now gives $c\operatorname{tr}(w^q)=c\operatorname{tr}(w)^q$. Regardless of matrix dimension, this readout contributes at most **one** independent $K^q$ direction. Thus a decoder restricted to fixed weighted ordinary traces of powered matrices would need $d^6$ traces for the linear version of the edit problem.

## Nonlinear processing after the readouts

Allow rational operations on all extracted scalars with coefficients from $K^q$ and defined denominators, keeping the same algebras and readouts. With $\beta_1,\ldots,\beta_D$ their listed basis readouts, every answer belongs to $L=K^q(\beta_1,\ldots,\beta_D)$. Each generator has $q$th power in $K^q$, so $[L:K^q]\le q^D$.

Write $n=d^2$ and enumerate the independent entries by $x_i,y_i,z_i$ in each bank. Linear combinations of the requested answers still give all $x_i y_j z_k$. The field these generate over $K^q$ has degree exactly $q^{3n-2}$. Generators are $x_1y_1z_1$ and the $3(n-1)$ ratios of a nonfirst entry to the first entry in its bank. The monomials in these generators with exponents from $0$ through $q-1$ have pairwise distinct exponent vectors modulo $q$ in the original independent variables. Nonfirst positions identify the ratio exponents, and a first position then identifies the remaining exponent. The denominator-clearing argument gives their independence; their powers reduce to $K^q$ so they also span. Hence **$D\ge 3d^2-2$** even with unrestricted rational postprocessing over $K^q$.

For polynomial postprocessing of degree at most $\ell$, also $\binom{D+\ell}{\ell}\ge d^6$, by counting monomials in the listed basis readouts. In particular a quadratic decoder needs $D=\Omega(d^3)$. The full field-degree bound after unrestricted processing is attained as a bound on the number of field generators. It makes no running-time assertion about implementing the original multiplication.

These results concern a common readout of powered values across the edits. A compiler could synthesize a different algebra and readout after an edit, mix in fresh rational coefficients outside $K^q$, or use the internal gates of the circuit to extract a root. The white-box algorithm of Andrews gives efficient root extraction for a constant number of variables, and the exponent here concerns a growing number of symbolic entries. A symbolic algebra dimension bound counts neither Boolean gates nor executed RAM instructions. Priority for this particular matrix-edit obstruction is unestablished. [Andrews, *Algebraic Hardness versus Randomness in Low Characteristic*](https://arxiv.org/abs/2005.10885) · [Lean proof that short edits span every matrix unit](FrobeniusElementaryEdits.lean) · [Finite row-space and coefficient audit](frobenius_edit_readout_audit.py)
