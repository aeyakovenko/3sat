# How much parity information survives a bounded name fiber?

**Research journal, 24 November 2026.** Keep the output clock, counted entries and rank thresholds $J_d$ of the [parity criterion](parity-of-program-fibers.md). Put $m=q-1$ and view an eligible name index as a nonzero binary $m$-vector. Pick every coefficient of a multilinear Boolean polynomial $P$ of degree at most $e$ independently and uniformly in $\mathbb F_2$. Enter $\sum_{i\in F_x}P(i)$ in the output cell $x$. All sums below are in $\mathbb F_2$ unless used to count objects.

For each $d=1,2,3$, under deterministic $O(n^d)$ SAT there is a fixed integer $u\ge0$ such that for **every fixed $e>u$**, only a fraction

$$
2^{-\Omega_e(q^{\,e-u})}
$$

of these polynomials give matrices approximable at rank $\kappa J_d$ and error $\epsilon 2^q$ on the counted entries. The positive constants can depend on the fixed machine and on $d$. Thus Boolean selectors of fixed degree suffice even when the desired exponent in the probability bound is an arbitrarily large fixed power of $q$. For an affirmative attack I obtained exact low ranks on classes of genuine forward program maps, including ones with many-to-one behavior. I have no representation with the needed coverage of the full interpreter.

## A dimension bound for disjoint bounded fibers

Write $N=2^q$. For a set $F$ of name indices, its syndrome is the vector of its parity sums for all squarefree monomials through degree $e$. Fix $k\ge1$, $0<\alpha<1/2$, and let $u=\lfloor\log_2 k\rfloor$. If at least $\alpha N$ pairwise disjoint nonempty sets have size at most $k$, their syndromes span dimension at least

$$
D=\sum_{j=0}^{e-u}\binom{\lfloor m/3\rfloor}{j}
$$

for all sufficiently large $q$, provided $e\ge u$. To isolate one member of any individual set, repeatedly choose an affine hyperplane cut that separates two current points and keep the smaller nonempty side. After at most $u$ cuts a single point remains. Repeated tautological conditions pad the list to $u$ affine equations. For $u$ independent uniformly random affine forms, the chance of realizing these prescribed conditions on this set is at least $2^{-uk}$. Indeed one affine form has at most $2^k$ possible restrictions, equiprobable on their linear image. Consequently there exists one common map to $u$ bits whose zero bucket isolates a member in at least $2^{-uk}\alpha N$ of the sets. The isolated points are distinct.

This point set has constant density in the $m$-cube, so it realizes all patterns on some set of $\lfloor m/3\rfloor$ coordinates. Otherwise the Sauer–Shelah bound would give at most $\sum_{j<\lfloor m/3\rfloor}\binom mj=o(2^m)$ points. The monomials of degree at most $e-u$ on the shattered coordinates have linearly independent evaluations, by uniqueness of multilinear polynomials on the Boolean cube. Multiply them by the zero-bucket indicator, a product of $u$ affine forms after complementing the bits. On the isolated fibers these degree-at-most-$e$ parity sums are precisely the evaluations just counted. This proves the dimension bound. [Sauer's shattering theorem](https://doi.org/10.1016/0097-3165%2872%2990019-2)

The power of $q$ is sharp for bounded fibers alone. Partition the binary cube into parallel coordinate $u$-faces, omitting the face containing the unused zero index. Summing $P$ on a face extracts the coefficient of the product of all $u$ free variables. The resulting function of the fixed coordinates ranges over precisely the polynomials through degree $e-u$, of dimension $\sum_{j\le e-u}\binom{m-u}{j}$ before the one omitted face. There is a constant density of faces for fixed $u$.

In fact the lower bound has the same leading coefficient in $m$. For a positive-density point set $S$, write $h_t(S)$ for its degree-at-most-$t$ evaluation rank. In one coordinate with layers $S_0,S_1$,

$$
h_t(S)\ge h_t(S_0\cup S_1)+h_{t-1}(S_0\cap S_1).
$$

Polynomials independent of that coordinate supply the first summand. Differences of evaluations on the paired points in the intersection annihilate all these polynomials, and on polynomials $z\,b(x)$ give the second summand. Replacing the two layers by their union below and intersection above gives equality, since the lower layer then specifies all the values of $a(x)$ needed to evaluate $a(x)+z\,b(x)$. Take $h_{-1}=0$. Repeating the shift in every coordinate preserves cardinality and earlier downward closures, and can only decrease the evaluation rank. In the resulting downset, choose a maximal pairwise disjoint family of absent subsets of size at most $t$, with $t\ge1$. If it has $r$ members and the downset density is $c$, then $c\le(1-2^{-t})^r$ because a point in the downset contains none of the forbidden sets and the containment events are independent for a uniform cube point. Their union has $O_{c,t}(1)$ coordinates and meets every absent small subset. All small subsets outside that union are present. Evaluation on the corresponding points gives a triangular matrix with diagonal ones. Thus $h_t(S)\ge\sum_{j\le t}\binom{m-O_{c,t}(1)}j$. Applied to the isolated points with $t=e-u$, this yields a dimension bound with leading term $m^{e-u}/(e-u)!$.

## Concentration without independent fibers

Use the constants $\gamma,k,\ell$ from the rank-mask argument, so that more than $k$ names occur at fewer than $\gamma N/8$ words, and $2^{-\ell}\le\gamma/8$. Set $\alpha=\gamma/8$. Fewer than $\alpha N$ counted, nonempty small fibers can have their syndromes in any subspace of dimension less than $D$. Draw $\ell$ independent polynomials and let $W$ count the small fibers missed by all of them. To bound $\mathbb E(W/N)^D$, sample $D$ output cells independently and uniformly with replacement. A sequence of small nonempty fibers whose syndromes span dimension $r$ has conditional probability $2^{-\ell r}$ of being missed. Sequences using any other cell contribute zero.

At each extension the current span has dimension less than $D$. Fibers already in that span occupy less than $\alpha$ of the next uniform draw. Other small fibers multiply the conditional weight by $2^{-\ell}$. Iteration gives $\mathbb E[(W/N)^D]\le(\alpha+2^{-\ell})^D$, so $\Pr[W\ge\gamma N/2]\le2^{-D}$. If a fraction $\beta$ of selectors has low-rank approximants, all $\ell$ draws have them with probability $\beta^\ell$. Under the SAT assumption, jointly testing those rank factorizations forces $W\ge\gamma N/2$ on this event by the [dense-mask argument](parity-of-program-fibers.md). This gives $\beta\le2^{-D/\ell}$.

Even an indicator of a random affine zero bucket gives a simpler test. Every small nonempty fiber is hit with odd parity with probability at least $a=2^{-uk}$ by singleton isolation. After $j$ independent buckets the expected missed count is at most $N(1-a)^j$. Choose a fixed $j$ making $2(1-a)^j/\gamma<1/2$. Adjust the allowable rank and error per approximant to pay for $j$ factors. The same mask contradiction and Markov's inequality show that at least $1-2^{-1/j}$ of the affine bucket choices must resist approximation. One cannot derive concentration of missed counts from pairwise independence here. On parallel $u$-faces, a singular restriction of the affine map to the common directions makes the parity zero on every face at once.

## Exact ranks from forward maps

First split a fixed length of program data into a row parameter and $n$ further bits. For each row parameter, suppose its counted inputs partition into affine cells in these $n$ bits. On a cell of dimension $n'$ the output row is fixed, and the $s=q/2$ output-column bits are an arbitrary affine map of the $n'$ free coordinates. Allow the cell, map, output row and rank to vary without any bound on their number. Name indices in these free coordinates are affine, so the selector restricts to degree at most $e$.

If the column map has kernel dimension $h$, summing the selector on a fiber extracts the coefficient of the product of its $h$ free bits after an affine change of variables. This is zero if $h>e$. Otherwise the answer on the affine image has degree at most $e-h$. Extend a linear section affinely to the ambient column cube and multiply by the image indicator, a product of $s-n'+h$ affine factors. Thus the entire column function has degree at most $e+s-n'$, or is zero. Sums of any number of cell contributions stay in the same column-polynomial space. If $n'\ge s-t$ throughout, the full matrix has binary rank at most $\sum_{j\le e+t}\binom{s}{j}$, truncated at $s$. This is $2^{o(q)}$ when $t=o(q)$ and $e$ is fixed. A native example lets its row data choose a cyclic shift and a diagonal mask on the payload, prints the row with fixed padding, and applies the chosen shift and mask to the column. Its fibers can have exponentially different sizes. A fixed header and padding make all the inputs eligible, and the calculation applies to every selector with starting cutoff zero.

A different calculation handles maps in which both output halves depend nonlinearly on all program bits. For a total forward map $f:\{0,1\}^n\to\{0,1\}^q$ with coordinate degree bounds $d_j$, the parity pushforward is the polynomial

$$
G(z)=\sum_v P(v)\prod_{j=1}^q(1+z_j+f_j(v)).
$$

Its coefficient at $z^I$ vanishes if $e+\sum_{j\notin I}d_j<n$, because summing over the entire input cube annihilates every monomial of degree less than $n$. A Boolean indicator selecting the counted inputs can be multiplied into $P$, adding its degree to $e$.

Lean verifies the coefficient identity for an arbitrary finite list of weighted outputs with repetitions and the annihilation of every single monomial missing an input variable. [Boolean pushforwards in Lean](../lean/BooleanPushforward.lean)

Let $g=n-e-\tfrac12\sum_j d_j>0$ and $V=\sum_jd_j^2>0$. In any nonzero coefficient, at least one half of the complement of $I$ has weight at least its half-cube mean plus $g/2$. By Hoeffding, each such exceptional family has at most $2^{q/2}\exp(-g^2/(2V))$ choices on its side. The coefficient matrix is supported on their rows and columns, giving rank at most $2\cdot 2^{q/2}\exp(-g^2/(2V))$. Evaluation in each half is a linear transformation and preserves this upper bound. The same exceptional rows and columns work for any sum of maps with common coordinate bounds and a common lower bound on $n-e$.

For instance, if $n=q-O(\log q)$, the coordinate degrees are at most two, and $\omega(\sqrt q)$ coordinates are affine, then $g/\sqrt V\to\infty$ and the binary rank is $o(2^{q/2})$, enough for the linear criterion. One may first change basis independently within each output half to expose affine combinations, since these basis changes permute matrix rows and columns. If only $t=o(q)$ coordinates are quadratic, every nonzero coefficient has $|I|\le q-n+e+t=o(q)$. Its matrix therefore has rank $2^{o(q)}$, enough at all three exponents.

There is also an input-side test for quadratic maps. Make every quadratic monomial an edge between its two inputs, labeled by its output coordinate. Let $\nu$ be the largest number of vertex-disjoint edges with different labels. In the expansion of $t$ distinct output factors, at most $\nu$ chosen terms can each introduce two new input variables. Such terms are disjoint quadratic edges with distinct labels. Every other term introduces at most one new input variable, so the degree of the product is at most $t+\nu$. The pushforward consequently has total degree at most $D'=q-n+e+\nu$. Every monomial of this degree has degree at most $\lfloor D'/2\rfloor$ in at least one output half. Its coefficient matrix is supported on at most $2\sum_{j\le\lfloor D'/2\rfloor}\binom{q/2}{j}$ rows and columns in total. For $n=q-O(\log q)$, a matching deficiency $n/2-\nu=\omega(\sqrt q)$ makes this rank $o(2^{q/2})$ by a binomial tail bound. When $\nu=o(q)$ the rank is $2^{o(q)}$.

Finally, a forward circuit of arbitrary depth using XOR, constants and $a$ two-input AND gates admits an affine partition. Process the gates in topological order. When an AND has two inputs that are affine on a current cell, split that cell on the value of one input. Its output on the two resulting cells is zero or the other input. Each nonempty leaf therefore has codimension at most $a$ and the entire output map is affine on it. A final affine validity bit can be fixed at cost at most one additional equation. Apply the affine pushforward calculation with all $q$ output bits as the target. The Boolean degree across all leaves is at most $e+q-n+a+1$, regardless of the number of leaves. This bound also survives summing over lengths with a common lower bound on $n-a$. Thus $n=q-O(\log q)$ and $a\le q/2-\omega(\sqrt q)$ suffice for rank $o(2^{q/2})$. For each other target a positive linear gate budget also works: take $a\le\lambda q$ for any $0<\lambda<1/2$ with $H_2(\lambda)/2<1/(2+d^2\log_2 7)$, where $H_2$ is binary entropy. The preceding binomial rank bound then has a strictly smaller exponent than $J_d$.

## A genuine branch defeats two forward approximations

For arbitrary separate maps $(u,v)\mapsto(g(u),h(v))$, form the binary incidence matrices $M_g(y,u)=1[g(u)=y]$ and $M_h(z,v)=1[h(v)=z]$. The output parity matrix equals $M_g[P(u,v)]M_h^\top$. The selector matrix has rank $O_e(q^{\lfloor e/2\rfloor})$ by separating its monomials according to which input half has smaller degree. This estimate allows arbitrary functions and multiplicities in both maps.

Here is a fixed native branch where this product representation matters. On each of two even $b$-bit payload halves, output the triangular permutation
$$
T_1(x)=x_1,\qquad T_2(x)=x_2,\qquad
T_j(x)=x_j+x_{j-2}x_{j-1}\quad(3\le j\le b),
$$
and append the extra bit $Q_b(x)=\sum_{j=1}^{b/2}x_{2j-1}x_{2j}$. Add fixed padding in each half sufficient for the branch header. Its $2^{2b}$ distinct outputs form a constant fraction of the cube at the corresponding even lengths, and every branch execution meets the deadline with starting cutoff zero. The quadratic parts of the $T_j$, $j\ge3$, are distinct monomials. The extra bit includes $x_{b-1}x_b$, absent from all these parts. Consequently each half has only constantly many independent affine output combinations, even after a change of basis.

Moreover the XOR of the two appended output bits is a nondegenerate quadratic form on all $2b$ input bits. On an affine subspace of codimension $c$ its associated alternating form has rank at least $2b-2c$, since the orthogonal complement of the direction space has dimension $c$. A quadratic on a flat with alternating rank $r$ agrees with any affine function on at most $(1+2^{-r/2})/2$ of the flat: squaring its character bias and averaging over shifts gives zero inner average outside the radical and absolute value at most one inside. A circuit with at most $b-1$ ANDs is affine on each leaf of codimension at most $b-1$. Each leaf therefore has agreement at most $3/4$ on this XOR, and the whole circuit misses at least a quarter of the branch's names. Nevertheless every selector parity of this branch has the polynomial rank just proved. Thus even at zero starting cutoff, accurate approximation of the forward map with sufficiently few AND gates can fail on a constant-density branch whose parity matrices all have low rank.

If a proposed description changes, adds or removes the results on $o(N)$ names, it affects at most $o(N)$ output cells for every selector. Omitting all lengths below $q-\lceil\log_2 q\rceil$ this way costs $O(N/q)$ names. No argument here bounds the other discrepancies for arbitrary RAM programs.
