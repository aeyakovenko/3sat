# How many affine rules can supply the witnesses for a binary matrix product?

Let $D=d^2$ and let $G=\{(A,B,AB): A,B\in\mathbb F_2^{d\times d}\}$. A verifier takes public $(A,B,C)$ and an arbitrary string of witness bits. It can impose any number of binary equations $\ell m=n$ and affine equations on all these variables. Assume soundness on every public input. For any **fixed affine map from the public bits to all witness bits**, the fraction of honest products on which it supplies an accepting witness is at most
$$
                       2^{-D/125+1}.
$$
This holds with no bound on the number of equations, witness length, or witness multiplicity. Thus every complete verifier needs at least $2^{D/125-1}$ distinct affine maps to supply witnesses for all honest inputs. In particular an exact verifier must have at least $D/125-1$ auxiliary witness bits, since every possible fixed witness is a constant affine map. The exponent of the menu bound has the correct order. For one verifier $2^D$ maps suffice. The proof gives an explicit coefficient slightly larger than $1/125$.

## Eliminating a proposed witness

Substitute the affine map for the witness. The resulting accepted public set $T$ is contained in $G$. The failure of $\ell m=n$ is the union of the sets described by
$$
         (\ell=0,\ n=1)\qquad\text{and}\qquad(\ell=1,\ m+n=1).
$$
Each is empty or an affine subspace of codimension at most two. A failed affine equation gives a hyperplane or a constant verdict. Thus $T$ is obtained by forbidding affine subspaces of codimension at most two. This is also called a 2-XNF formula, a conjunction of disjunctions of at most two parity conditions. The same forbidden subspaces occur in the literature on parity limits and bounded-width CNFs of parities. [Riazanov, Sofronova and Sokolov, §2.2](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2026.112)

Write $\mu$ for the uniform distribution on $G$ and suppose $\mu(T)=2^{-b}>0$. Greedily select a maximal family of forbidden flats whose normal spaces form a direct sum. Omit empty flats; a forbidden whole space is excluded by $T\ne\varnothing$. Denote the number selected by $t$ and their combined normal span by $W$. Every other forbidden flat has a nonzero normal in $W$, since otherwise its normal space could be added to the family.

Condition on all answers to a basis of $W$. At most $3^t$ assignments to these parities avoid the selected flats, since each independent block has at most three allowed patterns. Every remaining forbidden condition has become empty, the whole cell, or a hyperplane in it. Over the binary field avoiding a hyperplane imposes the opposite affine equation. Thus $T$ within each cell is empty or a **single affine flat**. Every flat in $G$ has dimension at most $D$. For example, projecting its directions to the first factor gives a space $P$, with common kernel $K$. Its first projection has dimension at most $d(d-\dim K)$, and the possible second-factor directions above zero have images in $K$ by polarization, so contribute at most $d\dim K$. Consequently
$$
                         2^{2D-b}=|T|\le 3^t 2^D.                       \tag{1}
$$
[Full description of the graph flats](affine-certificates-on-the-binary-product-graph.md)

## The cost of avoiding independent forbidden flats

Use unnormalized character expectations $\widehat\mu(\alpha)=\mathbb E_\mu(-1)^{\langle\alpha,x\rangle}$. For this graph
$$
                      \sum_{\alpha}|\widehat\mu(\alpha)|^4\le 5 .       \tag{2}
$$
The bilinear part of a character with output coefficient matrix of rank $r$ is a bilinear form in the $D$ entries of each input factor of rank $dr$. This follows by summing over the $d$ inner matrix indices: each contributes one disjoint copy of the coefficient matrix. For this fixed bilinear form, averaging an arbitrary linear perturbation over one factor imposes an affine system of rank $dr$ on the other. Averaging over that affine fiber shows the nonzero biases have magnitude $2^{-dr}$ and there are exactly $2^{2dr}$ input-mask pairs giving them. There are at most $4\cdot 2^{(2d-r)r}$ output matrices of positive rank $r$, by factoring through rank $r$ and dividing by $|\mathrm{GL}_r(2)|\ge2^{r^2}/4$. The zero output mask contributes just the trivial character. Therefore the total in (2) is at most $1+4\sum_{r\ge1}2^{-r^2}\le5$.

For each selected forbidden flat of codimension two, use the nonnegative function $f$ which is $1$ off the flat and $6/7$ on it. In the character expansion $f=\sum_\alpha c_\alpha\chi_\alpha$ its coefficient magnitudes on the normal plane are $27/28,1/28,1/28,1/28$. Hence
$$
                       \|c\|_{4/3}=(27/28)^{1/4}.
$$
For a forbidden hyperplane use the indicator of its complement, which has norm $2^{-1/4}$ and thus also satisfies the preceding upper bound. The product of these $t$ functions is one on $T$ and is everywhere nonnegative. Since the normal spaces form a direct sum, every choice of local character contributes to a different product character. The $4/3$-norm of the product's coefficients is the product of their norms. Hölder's inequality and (2) now give
$$
          2^{-b}\le\mathbb E_\mu\prod_i f_i\le5^{1/4}(27/28)^{t/4}.
$$
With $\ell=\log_2(28/27)$ this is $4b\ge\ell t-\log_2 5$. Combining with (1) gives
$$
                 b\ge \frac{\ell D-\log_2(3)\log_2(5)}{4\log_2(3)+\ell}
                   \ge D/125-1.
$$
The argument uses products of functions on independent character blocks, an established technique in Fourier analysis. The fourth moment of the reference measure and the forced affine structure inside each surviving cell are the properties of matrix products used here. [Related product methods for the large spectrum, Lee](https://epubs.siam.org/doi/10.1137/15M1048604)

## Further consequences for witness construction

* If a family of $2^L$ Boolean circuits can furnish accepting witness strings for all correct products, and each circuit uses at most $k$ ANDs with arbitrary affine gates, then $L+k\ge D/125-1$. Fix one input bit value at each AND gate in topological order. Substituting those values into the products gives one affine map per pattern, and the pattern realized on an actual input reproduces that circuit's output there. The input is free to choose the circuit and pattern.
* To see the matching order of the exponent, impose the checks $p_{ikj}=A_{ik}B_{kj}$ and the free equations $C_{ij}=\sum_k p_{ikj}$. For each fixed matrix $A_0$, the assignment $p_{ikj}=(A_0)_{ik}B_{kj}$ is a public-affine rule. The $2^D$ rules cover all honest inputs.
* More generally, fix $w$. The complement of any union of forbidden affine subspaces of codimension at most $w$, if contained in $G$, has honest density at most $2^{-c_w D+O_w(1)}$ for some $c_w>0$. For $w=1$ the complement is a flat. For $w\ge2$ take a maximal independent family of normal spaces as above. On a block with $q=2^j$ patterns, one forbidden, choose $f=1-\epsilon\mathbf 1_{\rm forbidden}$ with $\epsilon=q/(1+(q-1)^3)$. Its coefficients have magnitudes $1-\epsilon/q$ and $\epsilon/q$ repeated $q-1$ times. Their $4/3$-norm is $(1+(q-1)^{-3})^{-1/4}$. With $M=2^w-1$ and $\psi=\tfrac14\log_2(1+M^{-3})$, we obtain $b\ge\psi t-(\log_2 5)/4$. On the other hand there are at most $M^t$ admissible cells. On each, the fixed cell equations together with clauses of width at most $w-1$ describe its accepted subset in the original ambient space: substitute the known normal in each remaining clause, removing it or an entire impossible condition. The induction hypothesis bounds the mass of each such subset, so $b\ge c_{w-1}D-t\log_2 M-O_w(1)$. These two inequalities establish the claim with $c_1=1$ and $c_w=c_{w-1}\psi/(\log_2 M+\psi)$.

## Approximate verification and fixed Freivalds challenges

The argument also bounds the probability of accepting a correct product when the verifier accepts some incorrect products. Let $U$ be an arbitrary set defined by a conjunction of width-two parity clauses, let $\eta=\mu(U)$, and let $\sigma=|U|/2^{3D}$ under independent uniform public bits. There are absolute constants $C$ and $a>0$ such that
$$
         \eta\le C\sigma^a,\qquad a=\frac{\log_2(28/27)}
                         {2\log_2(28/27)+4\log_2 3}.
$$
As above, choose $t$ independent forbidden blocks. The Fourier estimate gives $\eta\le 5^{1/4}2^{-t\ell/4}$ even for this arbitrary $U$. The decomposition of $U$ into at most $3^t$ disjoint affine flats also holds. Each flat of ambient probability $q$ has graph probability at most $(3/2)\sqrt q$. Cauchy–Schwarz and disjointness imply $\eta\le(3/2)3^{t/2}\sqrt\sigma$. Interpolating these two inequalities to cancel $t$ gives the displayed exponent. The same proof inducts to every fixed width $w$. If $\eta\le C_{w-1}\sigma^{a_{w-1}}$ at the smaller width, concavity and disjointness give $\eta\le C_{w-1}M^{t(1-a_{w-1})}\sigma^{a_{w-1}}$ on its partition, while the local Fourier bound is $5^{1/4}2^{-\psi t}$. Thus one can take $a_1=1/2$ and $a_w=a_{w-1}\psi/(\psi+(1-a_{w-1})\log_2 M)$, with $M,\psi$ as above. [Affine-section inequality](partial-coverage-for-binary-product-witnesses.md)

For example fix a public $d\times r$ binary matrix $R$ of rank $r$, and ask only for $CR=A(BR)$, the outcomes of $r$ linearly independent Freivalds challenges. This includes all true products and has ambient density exactly $2^{-dr}$, because $C\mapsto CR$ is surjective onto the $d\times r$ matrices. Suppose a binary rank-one witness system accepts only triples passing these challenges and has a witness at every true product. Substituting an affine witness rule gives a set of ambient mass at most $2^{-dr}$. The preceding inequality gives that rule honest success at most $C2^{-a dr}$. Consequently $2^{\Omega(dr)-O(1)}$ rules are required, even though wrong products passing the challenges may be accepted. The order of the exponent is sharp: compute $BR$ affinely, introduce witnesses for the individual products in $A(BR)$, and test equality to $CR$. For each fixed possible $BR$, those witnesses are affine in $A$, giving $2^{dr}$ rules. The lower bound concerns the representation of complete witnesses for these verification equations. The familiar algorithm for the checks remains fast.

## A test of the history count in deterministic linear-time MST

Suppose a certificate procedure chooses the affine witness rule by taking the maxima of $m$ fixed nonempty subsets of $r$ labels under one input-dependent total order. In addition allow $L$ bits choosing the collection or an initial state, and allow each resulting rule $k$ AND gates with free affine wiring. The MST history lemma bounds the number of distinct maxima vectors per initial choice by $\binom{r+m-1}{m}$. A complete procedure for the matrix-product mismatch formulas therefore satisfies
$$
          L+k+\log_2\binom{r+m-1}{m}\ \ge\ d^2/125-1 .
$$
More generally its success fraction on correct products is at most $2^{L+k+1-d^2/125}\binom{r+m-1}{m}$. At $m=O(d^2)$, a subquadratic-in-$d$ number $r=o(d^2)$ of labels gives a log binomial coefficient of $o(d^2)$, using the binomial estimate $\binom{m+r}{r}\le(e(m+r)/r)^r$. The exclusion still holds if the total order is computationally unbounded. In several rounds the log counts add if the choice of each round's family is fixed by the already counted history. A RAM's candidate writer set can depend on fresh input bits, so such unrecorded choices cannot be included for free. [DLMST, Lemma 3.9](https://github.com/Louiealbp/DLMST/blob/0072335716b145032b418760883daed2a89809db/final.pdf) · [Two-writer counterexample](dlmst-history-transfer.md)

An earlier attempt exposed one still-feasible forbidden pair at a time. Its two surviving children cost one and two independent parity answers, giving at most $F_{d+2}$ leaves upon reaching codimension $d$ (with overshoot at most one). Every nonzero graph parity has bias at most $2^{-d}$ by the calculation above. Thus each leaf has honest mass at most $2^{1-d}$, only giving an exponent proportional to $d$. Branching can be continued while the cell has codimension below $d$ since its size exceeds $|G|$. The fourth-moment estimate is what changes this exponent to $d^2$. Lean verifies the branching recurrence, the two forbidden patterns of a product constraint, and all four Fourier coefficients and the norm identity for each translated local test. The matrix fourth-moment and global slice bounds are written proofs. [Local Fourier identities and branching in Lean](../lean/AffineWitnessBranching.lean)

There is a linear-time example with the same exponential dependence. Take $j$ disjoint binary products of order $9$ and require all of them to be correct. A fixed program checks one constant-size block after another in $O(j)$ steps. Any affine flat in the simultaneous graph has dimension at most $81j$ by projecting to each block. The uniform graph distribution is a product of $j$ measures, so its fourth Fourier moment is at most $5^j$. Repeating (1) and the independent-block inequality now gives
$$
 b\ge j\,\frac{81\ell-\log_2(3)\log_2(5)}{4\log_2(3)+\ell}=\Omega(j).
$$
The numerator is positive. Thus every binary rank-one verifier for this easy relation needs exponentially many affine witness rules in the input length, even though a deterministic straight-line circuit of linear size computes the verdict. A general claim that a linear-time binary computation always has a sublinear logarithm of its affine witness menu would already fail here.

For a deterministic SAT solver, certifying its rejection of the explicit product-mismatch formula gives an existential system of the type above. On the fixed encoding of length $N=\Theta(d^2\log d)$ this requires at least $2^{\Omega(N/\log N)}$ affine rules. More precisely the probability on honest inputs covered by any $2^L$ rules is at most $2^{L-D/125+1}$, by a union bound. The result applies to the entire expanded Boolean witness, including intermediate gate values and any memory-routing bits. A transcript written only in native machine words can omit some of these variables. Even a short computation can generate a witness with this much nonlinear dependence. For every possible verifier the $2^{2D}$ honest inputs provide a menu of at most $2^{2D}$ constant maps by choosing one actual witness per honest input. A lower bound on the logarithm of the menu size alone can therefore never grow faster than $2D$. The theorem alone gives no superlinear RAM clock bound. Historical priority of the matrix-product application is unverified. [SAT and the verification costs](partial-coverage-for-binary-product-witnesses.md)
