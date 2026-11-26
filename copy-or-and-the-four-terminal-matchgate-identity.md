# COPY, OR and the four-terminal matchgate identity

The four-terminal tensor obtained by joining one leg of ternary Boolean COPY to one leg of ternary Boolean OR requires **exactly two planar matchgate signatures in a sum** when each external wire may have its own invertible two-dimensional change of basis. This holds over every field, including after any reordering of the four terminals. The two summands in the upper bound use the same bases. On the unmerged pair even the parity condition for the two local gates is incompatible across their common wire. These statements concern exact local signatures.

The minimum changes when the entries may be specialized from a parameter. The merged tensor is a specialization of a single transformed matchgate in every characteristic different from two. In characteristic two, a degree-two polynomial still excludes that specialization.

The distinction matters for SAT with at most two satisfying assignments. Over any field of characteristic different from two, the ordinary count $s$ already detects satisfiability by a nonzero test. To produce the normalized decision bit from the scalar, the least-degree polynomial on $s=0,1,2$ is $(3s-s^2)/2$. Its slope on the first two points is one and its slope on the last two is zero. In characteristic two the counts zero and two agree. Tracking an ordered pair of assignments instead produces the integer $s-\binom{s}{2}$, which works over every field and uses a single shared sort. The question about a Pfaffian shortcut is whether the *local tensors* in an assignment-counting network can be converted into planar matching signatures. [One-sort decision and bounded ambiguity](one-sort-for-bounded-ambiguity-sat.md)

## Which port bases can the separate gates share?

Write $u=(1,0), v=(0,1), w=u+v$. The two signatures in the standard coordinates are

$$
 E=u^{\otimes3}+v^{\otimes3},\qquad O=w^{\otimes3}-u^{\otimes3}.
$$

A planar matchgate signature vanishes on all words of one Hamming parity. A wire basis $B$ on one side of a contraction must have dual change $B^{-T}$ on the other. Independent changes are allowed on every wire. We use the parity condition and the usual four-terminal matchgate identity. Both are necessary over any field. The identities have integer coefficients and hold identically in the edge weights over the integers, so they also hold after reduction modulo a prime. [Cai and Gorenstein, Section 2 and Theorem 2.1](https://theoryofcomputing.org/articles/v010a007/v010a007.pdf)

First suppose the characteristic differs from two. Set $Z=\operatorname{diag}(1,-1)$. A parity-supported tensor is an eigenvector of the tensor product of its $Z$'s. Pull back these operators by the wire bases. For a ternary tensor $r^{\otimes3}+\lambda s^{\otimes3}$, where $r,s$ are independent and $\lambda\ne0$, each pulled-back involution permutes the two lines $Kr,Ks$. Indeed the flattening that keeps any two ports has image spanned by $r\otimes r,s\otimes s$. Only these two lines have tensor rank one in that plane, as seen from the determinant of a diagonal two-by-two matrix. Preservation of the plane by the operators on those ports makes the permutations on the two ports agree. If all three fix the lines, their two eigenvalues are opposite on each port. The product eigenvalues on the two summands then have opposite signs, inconsistent with a single eigenvalue. Hence all three operators exchange the lines.

On the common wire of $E$ and $O$, the operator $J=B^{-1}ZB$ for COPY exchanges $Ku,Kv$ and is antidiagonal. The dual-side operator $J^T$ sends $Ku$ to $Kv$, outside the two lines $Ku,Kw$ that it would have to permute for OR. Thus even different invertible bases on all the other wires cannot give compatible parities.

In characteristic two use $Q=\operatorname{diag}(0,1)$. The sum of the single-port actions of $Q$ has eigenvalue equal to the Hamming parity. For a ternary sum in the bases $(r,s)$, each of the six off-diagonal entries of the three pulled-back operators contributes to a different mixed word. All six entries must vanish if their sum sends the tensor to a scalar multiple of itself. Each diagonal operator has eigenvalues zero and one. The sums of the three eigenvalues on the two complementary words differ by $1+1+1=1$ in the field. No parity is possible for either ternary gate separately.

## Contracting the shared edge

In the rank-one lines on the two sides, the coefficient matrix of the merged tensor is $M$.

$$
 F=(u\otimes u)\otimes(w\otimes w-u\otimes u)
   +(v\otimes v)\otimes(w\otimes w),\qquad
 M=\begin{pmatrix}1&-1\\1&0\end{pmatrix}.
$$

Because $M$ is invertible, both flattening images are precisely the two-dimensional planes displayed here. Again, each contains exactly its two indicated rank-one lines.

In characteristic different from two, a pulled-back product of parity involutions preserves both planes and hence permutes both pairs of rank-one lines, with nonzero rescalings. The zero entry of $M$ is unique. Any row and column permutations preserving its zero pattern must fix its row and its column, hence must be the identity. Each individual involution therefore fixes both constituent lines on its port. After changing bases these lines are the two coordinate axes, since the parity operator has distinct eigenvalues.

In characteristic two let $D_L=Q_1\otimes I+I\otimes Q_2$ and use $D_R$ for the other two ports, with each $Q_i$ pulled back in its own basis. The equation $D_L F + F D_R^T=pF$ in flattening coordinates shows that $D_L$ preserves the image on the left and $D_R$ preserves the image on the right. In a local pair basis where the image is spanned by $00,11$, the coefficients of $01,10$ in $D_L(00)$ and $D_L(11)$ force all four off-diagonal entries of $Q_1,Q_2$ to vanish. The same argument applies on the right. Since zero and one are distinct, the transformed lines must again be coordinate axes.

In every characteristic the only possible parity bases consequently place the three nonzero coefficients at three corners of a four-point rectangle. Moving from one column to the other flips both right bits. Moving from one row to the other flips both left bits. Among the supported words there is precisely one complementary pair. The four-terminal matchgate identity for that parity is a sum with signs of the four complementary products. Take the two complementary supported words $z,\bar z$ and apply the general identity to $z\oplus e_1,\bar z\oplus e_1$. Exactly one term is nonzero. This contradicts the identity in every cyclic order and over every field.

For the matching two-term upper bound, choose the bases that send $u,v$ on the left and $w,u$ on the right to the two coordinate axes. Split the tensor by its left pair. The first summand pins both left bits to zero and has right coefficients $1,-1$ on $00,11$. The other summand is a single fully pinned configuration. A normalized two-terminal even signature with nonzero $11$ coefficient is a weighted edge, times a scalar. A one-terminal pin is an isolated terminal or a terminal with a forced matching edge. Their disjoint unions draw in any prescribed cyclic order here, since at most one component connects a pair of terminals. This realizes both summands.

## Specialization separates the characteristics

Allow a polynomial boundary tensor $F(t)$ over $K$ with prescribed value at zero. Ask for the fewest matchgate summands after separate wire basis changes over the rational function field $K(t)$. This states the degeneration precisely even when the coefficient field is finite.

Suppose $2\ne0$ in $K$. In the pair axes above, take

$$
 M(t)=\begin{pmatrix}1&-1\\1&-t^2\end{pmatrix}.
$$

Its three original entries stay fixed. Scale its second row by $-1/t$ and its second column by $1/t$, each through a diagonal change on just one port of its pair. The new matrix has diagonal entries one and both off-diagonal entries $-1/t$. Apply the Hadamard matrix with rows $(1,1),(1,-1)$ on every port. At output $x$ the resulting value vanishes if $|x|$ is odd. On even $x$ it is $2(1-1/t)$ if the first two bits have even parity and $2(1+1/t)$ otherwise. In cyclic order $1,2,3,4$ the matchgate identity reads

$$
 g_{0000}g_{1111}-g_{1100}g_{0011}
       +g_{1010}g_{0101}-g_{1001}g_{0110}=0.
$$

The first two products agree, as do the last two. Dividing by the nonzero $g_{0000}$ over $K(t)$ gives the principal Pfaffians of a four-by-four skew matrix. Its six upper entries are the normalized weight-two coefficients and its Pfaffian equals the normalized weight-four coefficient by this identity. The standard planar matchgate realization of these principal Pfaffians uses edge weights in the same field. Consequently the polynomial family $F(t)$ has a one-matchgate realization over $K(t)$, with $F(0)=F$. Port orders can be transported along the construction; existence requires a suitable cyclic order. [Cai and Gorenstein, Section 5](https://theoryofcomputing.org/articles/v010a007/v010a007.pdf)

In characteristic two define the quadratic polynomial

$$
 H(T)=\sum_{\{x,\bar x\}} T_x T_{\bar x},
$$

with one representative of each of eight complementary pairs. Swapping the two coordinates on one port preserves $H$. Scaling them by $a,b$ scales $H$ by $ab$. For an elementary shear split $T$ into its two slices $U,V$ at that port. Replacing $U$ by $U+cV$ adds $c\sum_y V_yV_{\bar y}=0$, since $y$ has three bits and complementary pairs occur twice. These changes generate every invertible two-by-two matrix. Hence under independent wire changes $H$ scales by the product of their determinants. For a planar matchgate the parity condition removes four of the eight products, and the four-terminal identity says that the other four sum to zero, independently of cyclic order. For the merged tensor in pair axes exactly one product survives and $H(F)=1$. Polynomial specialization preserves the equality $H=0$. The two-summand upper bound is therefore exact even allowing specialization in characteristic two. This proof works over extension fields as well.

This quadratic is the reduction modulo two of the classical degree-two invariant of a quadrilinear form. The matchgate obstruction uses its coincidence with the unsigned four-terminal identity in characteristic two. [Luque and Thibon, Equation 5](https://arxiv.org/pdf/quant-ph/0212069)

## Compatibility across adjacent deformed blocks

Consider a cubic bipartite network of ternary COPY and OR vertices paired along a perfect matching. Replace each matched pair by the specific polynomial tensor with coefficient matrix $M(t)$ above in its original constituent lines. Over $K(t)$ with characteristic different from two, even one remaining wire directly joining a COPY port to an OR port prevents a simultaneous matchgate basis for these blocks.

Indeed $M(t)$ is invertible and all four entries are nonzero. For any matchgate basis of one block, parity gives the same two permutations of its rank-one lines as in the exact proof, one on rows and one on columns. For a coefficient matrix with entries $a,b,c,d$ in row order, the ratio $ad/(bc)$ survives arbitrary nonzero row and column rescalings. Swapping exactly one pair inverts it. Here the ratio is $t^2$, which differs from its inverse over $K(t)$, so both permutations agree. If both fix their lines, the transformed tensor occupies four paired-bit corners on coordinate axes. It has just two nonzero complementary products. In any terminal order the four-port identity forces the two to agree up to sign. Their ratio, up to inversion, is $ad/(bc)=t^2$, which differs from both $1$ and $-1$. The only remaining possibility exchanges both pairs of lines. Each individual port operator exchanges the two constituent lines on that port.

At a COPY port this makes the pulled-back involution antidiagonal in $u,v$. Its transpose on the other end of the wire therefore takes $Ku$ to $Kv$. An OR port needs that same operator to exchange $Ku$ and $Kw$. Since $Kv\ne Kw$, the two local realizations cannot share the wire. The argument permits different terminal orders and arbitrary rational-function wire bases. It addresses the displayed deformation applied to every matched block. Other deformations or larger regroupings require their own compatibility tests.

## Sources and finite check

Valiant's Theorem 5.2 already excludes an elementary matchgrid algorithm for general 3CNF. Morton and subsequently Margulies and Morton studied Pfaffian circuits with independent edge bases and the degree-four Pfaffian constraint. The calculation above is a direct application of the classical necessary identities to this pair of local SAT signatures. The COPY calculations in both characteristics already appear in the repository's exact-cover test. Its merged COPY–exact-one tensor fails parity itself. The merged COPY–OR tensor here admits parity bases and requires the four-terminal identity. These local results allow a test of a proposed gadget even with all its external bits pinned, giving at most one internal completion for the original COPY–OR merge. A construction that preserves only the final decision on promised inputs need not realize this four-port tensor. [Valiant, Theorem 5.2](https://people.seas.harvard.edu/~valiant/focs06.pdf) · [Morton, *Pfaffian circuits*](https://arxiv.org/abs/1101.0129) · [Margulies and Morton, Sections 3–4](https://arxiv.org/abs/1311.4066) · [Earlier cover-repair test](determinant-and-matchgate-tests-for-cover-repair.md)

The audit directly contracts the two truth tables and enumerates independent invertible projective wire bases. Over $\mathbb F_2$, 16 of 1,296 four-port basis tuples have a single parity. Over $\mathbb F_3$, 256 of 331,776 tuples have a single parity. Every one fails the four-port identity in all 24 terminal orders. Over $\mathbb F_3$ each separate ternary gate allows four choices on the shared wire after varying its other bases, and the dual-compatible sets are disjoint. Over $\mathbb F_2$ both sets are empty. Run `python3 copy_or_matchgate_audit.py`. [Exhaustive audit](copy_or_matchgate_audit.py)
