# Recovering the permanent when the squared entries follow a pattern

**Research journal, 24 November 2026.** The proposed test polynomial squares the first-row entry in every term of the permanent. Its formal set-multilinear part vanishes. Nevertheless, over any field of characteristic other than two, a circuit for that polynomial gives a circuit for the formal permanent with polynomial overhead. The argument also handles an independently chosen exponent for every matrix entry and a bounded number of exceptions in each monomial.

## Inverting pure powers

Choose $e_v\in\{1,2\}$ for each of the $h=m^2$ variables. Suppose a circuit of size $s$ computes a polynomial $Q$ that agrees with $\operatorname{perm}_m$ on the Boolean cube, and every monomial uses each variable $v$ with exponent either zero or $e_v$. There is a unique multilinear polynomial $H$ such that $Q(X)=H((X_v^{e_v})_v)$. On the cube $H$ agrees with the permanent, hence the two multilinear polynomials are equal. Uniqueness follows by evaluating on the indicator vectors of subsets in order of increasing size.

Work in $\mathbb F[X][t]/(t^{m+1})$. If $e_v=1$, feed $1+tX_v$ to the circuit. If $e_v=2$, feed the degree-$m$ truncated square root of $1+tX_v$ with constant term one. To compute its coefficients $u_k$, take $u_0=1$ and
$$
 2u_k=[t^k](1+tX_v)-\sum_{j=1}^{k-1}u_j u_{k-j}.
$$
Only the field element two is inverted. The output is $\operatorname{perm}_m((1+tX_v)_v)$ modulo $t^{m+1}$. Its coefficient of $t^m$ is the formal permanent, by homogeneity. Truncating at every gate by ordinary convolution gives size $O((s+h)(m+1)^2)$ for the recovered circuit. This calculation still works when the characteristic is an odd prime at most $m$.

As a finite arithmetic check, convolution through degree $m$ recovered the leading coefficient for $m=2,3,4,6$ over the fields of sizes 3, 5, and 7, using all-squared, first-row-squared, and alternating exponent patterns. The recurrence and coefficient identity above give the general proof.

In particular the seed has $e_{1j}=2$ and all other $e_v=1$. It invalidates the proposed projection but admits this extraction. Per-entry exponents may be supplied as nonuniform advice when comparing arithmetic circuit sizes.

## Allowing exceptions to a fixed choice

Let $P$ have individual degree at most two and agree with the permanent on the cube. Suppose there is a fixed choice of the $e_v$ such that each monomial of $P$ has at most $r$ present variables whose exponent differs from that choice. Arbitrarily many of its variables may be squared. For each $v$ define
$$
 J_v P=(1-X_v^{e_v})P|_{X_v=0}+X_v^{e_v}P|_{X_v=1},\qquad D_v=J_v-\mathrm{Id}.
$$
On a monomial, $J_v$ changes a present exponent to $e_v$ and fixes absence. Operators at different variables commute. A product of $r+1$ distinct $D_v$ vanishes on every monomial covered by the hypothesis. Thus
$$
 Q=\prod_v J_v P
   =\sum_{|S|\le r}\Big(\prod_{v\in S}D_v\Big)P .
$$
Each summand on the right has a circuit using $O((s+|S|+1)3^{|S|})$ gates, by expanding the choices of substituting zero, one, or retaining the variable. The two sides agree on Boolean inputs, and the polynomial $Q$ has only the prescribed exponents. The first construction now recovers the permanent. For every fixed $r$ the overhead is polynomial in $m$ and $s$. This uses the journal's earlier truncated interpolation with a per-variable choice of target power. [Earlier interpolation lemma](partial-multilinearization.md)

## A limit even on permutation supports

The hypothesis does not follow from individual degree two. For $m\ge2$ consider
$$
  P=\operatorname{perm}_m(X)+\prod_{i=1}^m X_{ii}(1-X_{ii}).
$$
This representative has only permutation supports. On the diagonal support all $2^m$ exponent patterns occur. The coefficient of the all-ones pattern is two and each other coefficient is $1$ or $-1$. All are nonzero in the stated characteristics. For any proposed choice of exponents the complementary diagonal pattern disagrees at all $m$ positions. The extra term vanishes identically on the cube and has a linear-size circuit in $m$. This example leaves open the possibility of extracting the answer by exploiting how a circuit computes such a vanishing term.

These are circuit transformations. They supply neither a bound on general degree-two functional representatives nor a deterministic SAT time lower bound. The functional-complexity setting and its Boolean implications were studied by Forbes, Kumar and Saptharishi. The formal power series step is elementary truncation. Priority for the combination of these steps has not been established. [Forbes, Kumar and Saptharishi](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2016.33) · [Arithmetic circuit division and truncation](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.25)
