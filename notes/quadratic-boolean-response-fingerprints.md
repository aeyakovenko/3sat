# How short a Boolean read history can depend quadratically on a field challenge?

Let the true memory replies be zero at $T$ specified read positions. At a public challenge $a$ in $K=\mathbb F_{2^w}$, a checker accepts Boolean replies $b_j(a)$ if

$$
                  \sum_{j=0}^{T-1} b_j(a) a^j=0.
$$

Assume $w\ge2$ and that each $b_j$ is a Boolean polynomial of algebraic degree at most two in the $w$ binary coordinates of $a$. The polynomials are fixed before the challenge. The minimal length $T_*(w)$ at which a **nonzero response rule** passes at every point satisfies

$$
  2^{\lceil w/2\rceil-1}<T_*(w)\le
  \left\lfloor\frac{w\,2^w}{1+w+\binom w2}\right\rfloor+1 .
$$

For even $w$, there is also an explicit construction at $T=2^{w-2}+1$. A nonzero response rule fabricates at least one bit for at least one quarter of the challenges. A rule could still give genuine replies on the others. For a fixed genuine table with Boolean entries the same statements apply to its bitwise difference from the response.

The coordinate functions are codewords of the binary second-order Reed–Muller code. The relation between one-variable and multivariable descriptions of these codes is classical. Here the field-value test adds a different time shift to each slot before summing. [Delsarte, Goethals and MacWilliams, *On generalized Reed–Muller codes and their relatives*](https://doi.org/10.1016/S0019-9958(70)90214-7)

## Proof of injectivity at short lengths

Put $q=2^w$. Write each function on $K$ in its unique field polynomial representation of degree at most $q-1$. Every binary coordinate is of the form $\operatorname{Tr}_{K/\mathbb F_2}(ca)$ because the trace pairing is nondegenerate. Indeed the trace polynomial is nonzero of degree $q/2$, so its functional is nonzero and multiplication by any nonzero $c$ permutes $K$. Varying $c$ thus yields all $q$ binary linear functionals. Each linear form has only exponents $2^i$. Multiplying two forms and reducing modulo $z^q-z$ leaves only exponents of binary Hamming weight at most two, including the possibilities of degree zero and weight one. The relation between the univariate exponents and Boolean algebraic degree is classical. [Carlet, *Boolean Functions for Cryptography and Error Correcting Codes*](https://www.math.univ-paris13.fr/~carlet/chap-fcts-Bool-corr.pdf)

A Boolean-valued polynomial function $f$ satisfies $f^2=f$. On its reduced polynomial, squaring the coefficients permutes the exponents by doubling modulo $q-1$ on $1,\dots,q-1$ (positive multiples of $q-1$ are represented by $q-1$). It fixes exponent zero. Thus the support contains a union of full orbits. Doubling rotates the $w$ binary digits on the positive exponents. For the orbit of a single one the largest integer is $q/2$. For an orbit with two ones write $k$ for the shorter cyclic gap between them, $1\le k\le\lfloor w/2\rfloor$. Its largest exponent is

$$
                      M_k=q/2+2^{w-1-k}.
$$

A rotation places a one in the most significant position, and the better of the two choices puts the second one $k$ positions away. Distinct $k$ give distinct orbits, including the equal-gap case. In increasing order the gaps between consecutive orbit maxima, including $0$ and $q/2$, are at least $G=2^{\lceil w/2\rceil-1}$.

Use the reduced representative for each $b_j(z)$ and form the ordinary polynomial $H(z)=\sum_j z^j b_j(z)$ without reduction. For a particular orbit that occurs, let $j_0$ be the last slot in which it occurs and $M$ its largest exponent. That orbit's contribution to $H$ has degree exactly $M+j_0$ with a single nonzero leading term. If $T\le G$, the intervals $[M,M+T-1]$ for different orbit maxima are disjoint. The orbit with the largest occurring maximum therefore supplies the unique highest term of $H$. Its degree is at most $3q/4+T-1<q$. A nonzero rule cannot vanish at all the field challenges. More precisely a uniformly chosen challenge detects it with probability at least $1/4-(T-1)/q$.

## Upper bounds and exact examples

There are $m=1+w+\binom w2$ independent square-free coordinate monomials of degree at most two in each slot. The checker is an $\mathbb F_2$-linear map from $mT$ bits to the $qw$ bits representing its value at every challenge. If $mT>qw$ there is a nonzero kernel vector. Every nonzero Boolean polynomial of degree $k\le2$ takes value one on at least $q/2^k$ challenges. Fix the coordinates outside a highest-degree monomial in any way. The chosen monomial survives in the restricted polynomial, which takes value one somewhere on that subcube. A nonzero slot in the kernel vector therefore gives the claimed quarter.

For even $w$, let $L(z)=\sum_{i=0}^{w/2-1} z^{4^i}$. It defines a surjective binary-linear map of $K$ onto $\mathbb F_4$. Its values lie in that subfield since $L(a)^4=L(a)$. Every fiber has at most $q/4$ points by its polynomial degree, forcing all four fibers to have size $q/4$. The function $I(a)=[L(a)=0]$ is the product of the two affine bits requiring both coordinates of $L(a)$ to be zero. Set $b_j(a)=I(a)[z^j]L(z)$. The fingerprint is $I(a)L(a)=0$ at every challenge. The response is false on exactly one quarter of them and the number of slots is $q/4+1$.

The finite audit quits at the first linear dependency in the space of all response rules, recovers its coefficients, and independently tests it on the whole field. The preceding independent columns rule out every shorter length in the first row. For $4\le w\le9$ the retrieved word is false at every challenge. At $w=2,3$ the audit separately constructs a monic word of degree $w$ with quadratic response coefficients that passes everywhere. For a field generator $a$, a nonzero binary polynomial vanishing at $a$ must have degree at least $w$, proving those two minimal lengths in the second row.

| Field degree $w$ | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| First passing nonzero quadratic rule, $T_*(w)$ | 2 | 3 | 5 | 8 | 13 | 24 | 35 | 70 |
| First passing rule false at every challenge | 3 | 4 | 5 | 8 | 13 | 24 | 35 | 70 |

These finite values leave a gap between the general square-root lower bound and the order-$q/\log q$ dimension upper bound. This is a test of one proposed read-history checker. It places no time bound on an actual SAT decision. [Exhaustion and certificate replay](../audits/quadratic_response_fingerprint_audit.py) · [Affine rules, Boolean catalogs and the SAT test family](binary-read-catalogs-for-ram-fingerprints.md)
