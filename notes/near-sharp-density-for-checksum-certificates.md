# Inverse-polynomial excess above the sharp pair-density obstruction suffices

For the [genuine pairwise checksum test](certifying-pairs-of-checksum-answers.md), let $d$ be the Boolean address length, $K=\mathbb F_q$ with $s=\log_2 q$, and $P$ the multiaffine interpolation of the native binary table. The desired bit is $P(o)$ at its Boolean output address. Uniform queries ask for $\mathrm{Tr}(\lambda P(p))$ with independent uniform $p,\lambda$. A uniformly sound bounded verifier certifies the XOR of two such queries on a fraction of independent uniform pairs. Two candidate binary arrays differing only at $o$ agree on exactly the fraction
$$
                      \theta_*=(1+\delta_*^2)/2,
          \qquad \delta_*=1-(1-1/q)^d.
$$
Their difference interpolant is the product of the $d$ affine Lagrange factors for $o$. Uniform masks give fair parity differences unless that product vanishes at both points. This gives an information-theoretic obstruction for inference using only certified pair equations.

For **every fixed $C>0$**, coverage greater than $\theta_*+d^{-C}$ is sufficient to certify $P(o)$ with only $\operatorname{poly}_C(d,s)$ successful pair witnesses and a single nondeterministic block. Use the original field size from the [physical checksum SAT construction](sat-on-random-checksums.md), where $q\ge d^3$ at all sufficiently large stages and $s=O(\log d)$. The standard near-native layout has $d\le j+O(\log(j+2))$ and the field rule takes $q\ge 2^{18}(d+1)(j+1)^{2A}$ with $A\ge1$. One can equivalently enforce $q\ge d^3$ directly when choosing the polynomial-size field. The [block-grid method](adaptive-queries-for-checksum-parity.md#a-positive-refinement-for-correlated-query-grids) reaches the exact obstruction with $O(s2^d)$ rows. Here every inverse-polynomial excess is available at polynomial cost, including excesses much smaller than the block-grid bound at fixed grid dimension.

## A restricted polynomial with a known leading form

Choose a uniform $d\times r$ direction matrix $A$ over $K$ for a fixed dimension $r$. Read the table polynomial on $p=o+At$ for nonzero $t\in K^r$. For each such $t$ the resulting $p$ is uniform as $A$ varies. Write $L_i(t)$ for the linear form from row $i$ of $A$. The restriction has total degree at most $d$. Its homogeneous component of degree $d$ belongs to the one-dimensional span of $G_A(t)=\prod_{i=1}^d L_i(t)$, since the unique possible degree-$d$ monomial in the original multiaffine polynomial uses every coordinate. Thus a valid linear space of candidate polynomials has basis consisting of the monomials of degree less than $d$ and this one additional form whenever nonzero. Enlarging to all degree-$d$ polynomials would discard the property used below.

Fix an odd integer $L$ and $r>L$, with $d\ge L$. Call $A$ good if every $L$ of its rows are linearly independent. For each $L$-subset, sequential exposure bounds the failure probability by $\sum_{i=0}^{L-1}q^{i-r}\le2q^{L-1-r}$. Hence failure probability is at most $2\binom dL q^{L-1-r}$. This also ensures independence of all subsets of size up to $L$.

## When can a difference have many zeros?

On a good grid let $F(t)$ be the difference of two candidate polynomials with different constants. Its constant is nonzero. We bound its zero fraction first on all $K^r$. If its degree is at most $d-1$, the polynomial root bound gives at most $(d-1)/q$. Suppose next that it has degree $d$ and does not split completely into affine linear factors over $K$, counting multiplicity. Remove all such linear factors, leaving a polynomial $E$ of degree $e\ge2$ without an affine hyperplane factor. The remainder can be reducible, nonsplit or have repeated nonlinear factors.

If $E$ has rational zeros, choose an affine $k$-flat $W$ of maximal dimension contained in its zero set. Its dimension is at most $r-2$, since a polynomial of degree less than $q$ vanishing on an entire affine hyperplane has the defining linear factor. Each $(k+1)$-flat through $W$ restricts $E$ to a nonzero polynomial divisible by the linear equation of $W$ inside that flat. The number of zeros off $W$ there is at most $(e-1)q^k$ by the ordinary total-degree root bound on the quotient. The $(q^{r-k}-1)/(q-1)$ such flats partition the points outside $W$, after removing their common $W$. Consequently the zero fraction of $E$ is at most
$$
          q^{-2}+(e-1)/(q-1).
$$
This bound also holds if there are no zeros. Adding the removed factors by a union bound gives at most $(d-1)/q+(2d+1)/q^2$. For sufficiently large $d$ and $q\ge d^3$ this is smaller than $\delta_*$, by $\delta_*\ge d/q-\binom d2/q^2$. The affine-flat count is the elementary geometric argument underlying bounds for hypersurfaces with no linear component. [Homma and Kim](https://doi.org/10.1016/j.ffa.2012.11.002)

It remains to consider $d$ linear factors. The homogeneous part of $F$ has degree $d$ and is a nonzero multiple of $G_A$. Unique factorization forces the factor normals to be precisely $L_1,\ldots,L_d$ up to rescaling and permutation. For every subset of $a\le L$ hyperplanes the intersection then has fraction exactly $q^{-a}$, for arbitrary affine offsets, by independence of the normals. Bonferroni's upper bound of odd order $L$ gives a uniform bound on the zero fraction
$$
     \sum_{a=1}^L(-1)^{a+1}\binom da q^{-a}
         \ \le\ \delta_*+\binom d{L+1} q^{-L-1}.
$$
The final inequality follows by applying the lower Bonferroni bound of order $L+1$ to independent events of probability $1/q$. Bounds for the other two cases also lie below this upper bound. Passing to uniform nonzero $t$ increases any zero probability by at most $2q^{-r}$.

## Transfer to a small witnessed linear system

Let $z(A)$ be the maximum zero fraction on nonzero parameters of a candidate difference polynomial with nonzero constant, for the stated linear space on grid $A$. For good $A$ use the preceding bound, and for all other $A$ use one. Thus
$$
 \mathbb E z(A)\ \le\ \delta_*+
      \binom d{L+1}q^{-L-1}+2q^{-r}+2\binom dL q^{L-1-r}.
$$
For a prescribed $C$ choose fixed odd $L>C+2$ and $r=2L+2$. At $q\ge d^3$ the error in this display is $o(d^{-C})$. Two independent direction matrices, nonzero parameter vectors and masks sample independent uniform query endpoints after averaging over the matrices. On any two fixed grids a pair of candidates with common constant opposite to $P(o)$ agrees with at most $(1+z(A)z(A'))/2$ of the true pair parities, by the fair-mask argument. The expected value of that bound is $(1+(\mathbb Ez(A))^2)/2$ by independence, less than $\theta_*+d^{-C}$ for all sufficiently large $d$. If the stated sufficient coverage holds, its difference from the direction-dependent bound is positive on some pair of grids. On those grids all true witnessed equations together force the true constant. This step allows the two matrices selected in the certificate to depend on the actual coverage set.

A restriction is specified by at most $D=\binom{d-1+r}{r}+1$ field coefficients. Keep the constant shared between the two grids and binary. Each witnessed pair supplies one binary row by applying the trace to its masked basis evaluations. The constant-coordinate functional lies in the span and is the XOR of at most $2s(D-1)+1$ witnessed rows. A verifier guesses matrices and that list, checks the witnesses, directly checks the zero moments for every nonconstant basis function on each grid, and requires trace one for the combined constant masks. The XOR of the witnessed answers equals $P(o)$ whenever these checks pass, including on unproductive stages and arbitrary guessed matrices. No assumption about the degree of a guessed polynomial has to be trusted. The honest restriction always lies in the specified space.

For fixed $C$ there are polynomially many rows and arithmetic operations in $d,s$. Thus the clock remains $T\operatorname{poly}_C(j)$ for pair verifier cost $T$ at stage $j$. Under a hypothetical $O(N^k)$ unrestricted deterministic SAT solver and the [native successful-detector theorem](priority-pinned-sat.md), uniform soundness and the stated coverage at $T\le 2^{\lfloor j/k\rfloor}/(j+1)^B$ infinitely often, for sufficiently large fixed $B$, would give the SAT separation for that $k$. I have not found a verifier reaching this coverage. The argument leaves open the short-certificate criterion for positive excess below all inverse polynomials. Distance and decoding over product evaluation sets have a substantial literature. Priority of this particular sparse pair-parity witness criterion is unverified. [Kim and Kopparty](https://theoryofcomputing.org/articles/v013a021/)

[Finite restriction, root and moment checks](../audits/subspace_checksum_threshold_audit.py)
