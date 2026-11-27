# Reindexing the program image by rational maps

**Research journal, 24 November 2026.** I tried to cover almost all actual short-program outputs using images of many-to-one maps. A map could use different preimages from the programs that originally printed the words, and several images could overlap heavily. The following unconditional obstruction applies to such covers. Its second version charges only the distinct words in the final cover and also allows arbitrary Boolean combinations of range tests.

Write $N=2^q$. Use the fixed plain interpreter, program length at most $q-2$, and deadline $T(q)=N(q+2)^{\lceil\log_2(q+2)\rceil}$. Denote its actual outputs of length $q$ by $E_q$. Identify these words with $F=\mathbb F_{2^q}$ in the first irreducible polynomial basis of degree $q$. For a source set $S\subset F$ write $L(S)=\sum_\beta|\widehat{1_S}(\beta)|$, using normalized Walsh coefficients and characters $(-1)^{\operatorname{Tr}(\beta x)}$. Every nonempty affine binary subspace has $L(S)=1$, regardless of codimension. The sources and the coefficients of all the maps below may depend arbitrarily on the full output history. [Interpreter and dense-advice criterion](full-cube-advice.md) · [Previous image-cover attempt](covering-program-images.md)

## Many pieces with a bounded total number of inputs

Let $f_i\colon F\to F$ agree off its poles with a nonconstant rational function. In characteristic two write it as $g_i(X^{2^{s_i}})$ with $g_i$ separable and put $d_i=\deg g_i$. Changing the input variable by Frobenius preserves cardinalities and Fourier norms. Thus we can use $g_i$ and the correspondingly permuted source. Pole inputs may return arbitrary values. There is a fixed $\rho>0$ such that, for every such collection,
$$
|E_q\setminus\textstyle\bigcup_i f_i(S_i)|
\ \ge\ \rho\big(N-\textstyle\sum_i|S_i|\big)
      -O\big(\sqrt N[1+\textstyle\sum_i d_i L(S_i)]\big).
$$
Constant maps can be included at an extra cost of one distinct output each. For example a fixed capacity gap $\sum_i|S_i|\le(1-\delta)N$ and $\sum_i d_i L(S_i)=o(\sqrt N)$ leave a constant fraction of the cube consisting of genuine easy words outside the cover.

Set $h(y)=1/[y(y+1)]$, assigning zero at its two poles. Let $I$ select the words for which the first $r$ coordinates of $h(y)$ vanish, where $\rho=2^{-r}$. A single nontrivial output character of $h(f(x))$, multiplied by any input character, has complete sum $O(d\sqrt N)$ for a separable degree-$d$ map $f=A/B$. To see this, take coprime $A,B$. At least one of $A$ and $A+B$ has nonzero derivative, since otherwise both $A$ and $B$ are squares over the perfect field. A polynomial with nonzero derivative has a root of odd multiplicity over the algebraic closure. The roots of $A,A+B,B$ are pairwise disjoint. Consequently
$$
h(f(X))=\frac{B(X)^2}{A(X)(A(X)+B(X))}
$$
has an odd finite pole. For $\alpha\ne0$, adding $\beta X$ to $\alpha h(f(X))$ preserves that pole. Every pole of $u^2-u+c$ has even order, so the exceptional Artin–Schreier case is excluded. The complete rational-function Weil bound applies at degree at most $2d+1$. Totalizing exceptional input points changes the sum by $O(d)$. [Mérai, Shparlinski and Winterhof, Lemma 3.1](https://www.ricam.oeaw.ac.at/files/reports/22/rep22-33.pdf)

The indicator of the first-$r$-coordinates kernel has Fourier coefficients of total absolute value one and constant coefficient $\rho$. Expanding it and $1_S$ gives a count of $\rho|S|+O(dL(S)\sqrt N)$ preimages landing in $I$. The identity map on the whole cube gives $|I|=\rho N+O(\sqrt N)$. To print an indexed member, enumerate the field, evaluate $h$, and count selected values in binary order. Finding the field polynomial by testing candidates and performing this scan costs $N\,\mathrm{poly}(q)$ steps. A raw ordinal of $q-r+1$ bits suffices eventually. The decoder recovers $q$ from the payload length and a self-delimiting header for $r$. Taking $r$ large enough pays for that header and two bits of savings, giving $I\subset E_q$. Subtracting the upper bounds on the numbers of preimages proves the claim about distinct missed outputs.

## Arbitrary collisions and Boolean combinations of ranges

There is another fixed $J_q\subset E_q$ with the following property. Let $S_i$ be arbitrary binary affine subspaces, let $R_i=f_i(S_i)$ be the corresponding nonconstant rational images, and let $C$ be any Boolean combination of the membership tests $y\in R_i$. Write $D=\sum_i d_i$. Uniformly whenever $D\log(D+2)=o(q)$,
$$
\big|\,|J_q\cap C|-\rho |C|\,\big|\le 2^{q/2+o(q)} .
$$
In particular every complement of density at least $\delta$ contains at least $(\rho\delta-o(1))N$ genuine easy words. This applies even if every source is the full cube, fibers have unequal sizes, and the sum of all input counts exceeds $N$. The same estimate holds for general sources if also $\sum_i d_i\log(2+L(S_i))=o(q)$.

For $J_q$ use the first $r$ zero coordinates of
$$
H_q(y)=\sum_{t\in P_q}\frac{1}{y-t},
$$
where $P_q$ consists of the first $q$ distinct field words and the function is set to zero on this set. It has $q$ distinct simple poles. The complete Weil bound on the line gives $|J_q|=\rho N+O(q\sqrt N)$. The ordinal decoder has the same name length as before and uses $N\,\mathrm{poly}(q)$ time, since one evaluation takes only $q$ field inversions. Enlarge the fixed $r$ if needed for both decoders.

After the Frobenius input changes, let $m_i(y)$ count the retained preimages of $y$ in $S_i$. Discard finite source poles and their assigned outputs initially, which changes the result on at most $D$ output words. For every $y$,
$$
1_{m_i(y)>0}=\sum_{a=1}^{d_i}(-1)^{a+1}\binom{m_i(y)}{a}.
$$
A Boolean function on $k\le D$ membership bits has a multilinear real expansion with coefficient absolute sum at most $3^k$ by inclusion–exclusion. Substituting the preceding identities and writing binomial coefficients as ordered counts divided by $a!$ expresses $1_C$ as a sum of tuple counts. Their coefficient absolute sum is at most $3^k\prod_i(1+d_i)\le 6^D$. Each tuple uses $j\le D$ coordinates in total, with distinct source points within each repeated map. Fourier expansion of their source restrictions costs at most $\prod_i\max(1,L(S_i))^{d_i}$ in total coefficient weight.

Fix one tuple type and its input frequencies $\beta_l$. Its equations in $y,x_1,\ldots,x_j$ are $f_{i_l}(x_l)=y$. Remove from the projective $y$-line infinity, the geometric branch values of the maps and their values at input infinity. This removes $O(D+1)$ values. Indeed a separable degree-$d$ map of projective lines has at most $2d-2$ branch values by the different form of Riemann–Hurwitz, including wild ramification. Over the open line the tuple equations give a finite étale curve. Excluding equal coordinates for repeated maps takes a union of connected components, since the diagonal of a finite étale cover is open and closed. Every geometric component remaining maps onto this open line. A component moved by Frobenius has no rational points on the open curve, because distinct components there are disjoint.

Here are uniform bounds on the geometry as $D$ varies. The cleared tuple equations have degrees at most $D+1$ each, so the sum of degrees of the projective closures of their dominating components is at most $\Delta=(D+1)^j$ by affine Bézout applied before taking closures. Each normalized component has genus $O(\Delta^2)$, by generic birational projection of the geometric curve to a plane curve of degree at most $\Delta$ and the plane genus bound. Each coordinate function $x_l$ or $y$ has pole divisor of degree at most $\Delta$, by intersecting the projective curve with a generic coordinate hyperplane. Completing the curve and deleting all points over the removed base values and $P_q$ costs $O((q+D+1)\Delta)$ points per component. In the original affine tuple count the fibers over these values also cost at most $(q+O(D+1))D^j$ points. These bounds are uniform in the map coefficients.

For sufficiently large $q$, choose $t\in P_q$ outside the $O(D+1)$ removed base values. At every geometric point over $y=t$ on each retained component the map to $y$ is unramified and all the $x_l$ are finite. For every $\alpha\ne0$ the function
$$
\alpha H_q(y)+\sum_l\beta_l x_l
$$
therefore has a simple pole there. Its pole divisor has degree at most $(q+j)\Delta$. Apply the additive character bound on the smooth projective model of each Frobenius-stable component. The odd pole excludes every geometric Artin–Schreier exception. Including the deleted points, summing over the at most $\Delta$ components, and using the bounds above gives $q(D+2)^{O(D)}\sqrt N$ per tuple type and frequency choice. The constant tuple term follows from the same bound on the line. The Fourier expansion of the zero-prefix test has total coefficient weight one. Its constant term gives exactly $\rho|C|$ when the discarded finite output exceptions are restored, up to $O(D)$. All the other coefficients together satisfy the claimed error estimate. [Bombieri's curve bound, Theorem 5 as stated in *Tracing AG Codes*](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.68/LIPIcs.ICALP.2026.68.html) · [Related estimates for exponential sums over definable sets, Kowalski](https://people.math.ethz.ch/~kowalski/exponential-definable.pdf)

Deterministic extractors for polynomial sources and images of varieties also use algebraic structure to obtain output bits close to uniform. Those source laws weight a value by the number of preimages of a sampled point. The tuple count above addresses the cardinality of the distinct image and Boolean combinations of different such images. [Dvir, Gabizon and Wigderson](https://www.cs.princeton.edu/~zdvir/papers/DvirGabizonWigderson07.pdf) · [Extractors for Images of Varieties](https://eccc.weizmann.ac.il/report/2022/169/)

A rational reindexing of much larger separable degree, or a program-specific Boolean circuit acting on a large shared table, can evade these estimates. I found no such representation covering almost all of $E_q$ while leaving a positive-density complement at the required advice and verification costs. Priority of the application to time-bounded program images is unestablished.

Lean verifies the signed subset expansion for image-complement membership and the multilinear expansion of any Boolean combination into at most $3^k$ signed monomial occurrences. The character-sum estimates and geometric bounds above are manuscript proofs. [Finite expansions](../lean/RationalRangeSieve.lean)
