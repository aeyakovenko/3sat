# How well can a low-border-rank trilinear form predict a binary matrix product?

Draw independent uniform binary $d\times d$ matrices $A,B,C$. Let $M_d(A,B,C)=\operatorname{tr}(ABC)$, where the trace is over $\mathbb F_2$. Let $U$ be any binary trilinear form on the same three inputs and suppose its tensor has border rank at most $s$ over $\overline{\mathbb F}_2$. Put $g=(d-s^{4/9})_+$. Then

$$
 \Pr[U=M_d]\ \le\ \frac12+\frac12\,2^{-\max(0,\,g^2/12-11/3)}. \tag{1}
$$

The exponent $4/9$ uses the square matrix multiplication exponent $9/4$ stated in the November 2026 matrix multiplication preprint. The compression and analytic-rank arguments below also work with $1/\omega$ in place of $4/9$, using any proven lower bound $\omega$ for the formal square exponent over the algebraic closure. In particular, for $s=d^2(\log d)^{O(1)}$, the preprint gives advantage at most $2^{-\Omega(d^2)}$ over a fair guess. Here $U$ is a trilinear tensor of bounded border rank. An arbitrary Boolean circuit of the same size need not produce such a tensor. [Matrix exponent and formal model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/107.md)

## Compressing away three groups of slices

Write $p=\operatorname{srk}_{\mathbb F_2}(M_d-U)$ for the slice rank. Each slice consists of one linear form in one block times a bilinear form in the other two. Group an optimal decomposition into three tensors $S_1,S_2,S_3$ according to the block of the linear factor, with respective counts $p_1,p_2,p_3$ summing to $p$. Each group has flattening rank at most its count in the indicated mode. Over the algebraic closure, $M_d$ is a restriction of $S_1\oplus S_2\oplus S_3\oplus U$ by identifying the inputs in the four summands.

View matrix multiplication as the tensor network on a triangle with all three edge dimensions $d$. The Wigderson–Zuiddam compression theorem removes a summand of flattening rank at most $p_i$ at a network vertex by trimming the two incident edge dimensions by nonnegative integers $a,b$ with $(a+1)(b+1)>p_i$. Its conclusion is a degeneration from the remaining summands. It applies again after each removal. Thus one can choose both endpoint trims for all three vertices in advance, provided the total reduction of each edge leaves the desired positive dimension. This application is a consequence of established tensor compression. [Wigderson and Zuiddam, Part III, Theorem 12.17](https://www.math.ias.edu/~avi/PUBLICATIONS/Wigderson_Zuiddam_2025.pdf) · [Strassen, Proposition 6.4](https://doi.org/10.1515/crll.1988.384.102)

To allocate the trims, make a second triangle whose vertices are the three matrix index sets and whose edges are the three input matrix spaces. Give edge $ij$ weight $w_{ij}=\sqrt{p_{ij}}$, where $p_{ij}$ is the slice count for that input. Let $W$ be its real symmetric weighted adjacency matrix. On each connected component of positive edges choose a positive Perron eigenvector $v$, and use any positive coordinate on an isolated vertex. Allocate the real trim $w_{ij}v_j/v_i$ to endpoint $i$ of edge $ij$. The two endpoint trims for this input have product $p_{ij}$. Round each trim **down**. The product of the two integer trims each increased by one strictly exceeds $p_{ij}$. At an index set $i$, the sum of real trims is the Perron root of its component, bounded by $\rho=\lambda_{\max}(W)$. Hence each matrix index set loses at most $\lfloor\rho\rfloor$ dimensions.

The three real eigenvalues of $W$ sum to zero and their squares sum to $2p$. The other two eigenvalues have squares summing to at least $\rho^2/2$, giving $\rho\le2\sqrt{p/3}$. We conclude that $M_r$ is a degeneration of $U$ for

$$
                 r=\bigl(d-\lfloor 2\sqrt{p/3}\rfloor\bigr)_+.
$$

For $r=0$ the rank inequality below is automatic. For $r\ge2$ the border rank of $M_r$ is at least $r^{9/4}$. Indeed, a geometric border-rank algorithm of size $h$ yields formal exponent at most $\log_r h$ by tensor powers and interpolation. For $r=1$ the bound is immediate. Since border rank is monotone under degeneration, this proves

$$
               p\ \ge\ \tfrac34\bigl(d-s^{4/9}\bigr)_+^2.                 \tag{2}
$$

The same trimming rule has a direct geometric proof. Intersect the kernels of the linear factors in each mode, giving subspaces of codimensions at most $p_i$ on whose product $M_d=U$. In the product of the three Grassmannians of these dimensions, the condition that the restriction of $M_d$ have border rank at most $s$ is closed. This follows by using local bases and the closed rank-at-most-$s$ **border** locus in the fixed tensor space. The condition is invariant under basis changes at the index sets. Over the algebraic closure, the Borel fixed-point theorem gives a triple of subspaces fixed by the three upper-triangular groups. Diagonal matrices act with distinct weights on matrix units within each mode, so each fixed subspace is a coordinate span. Upper triangular row operations move occupied cells up, and the inverse action on columns moves occupied cells right. A missing cell forces the rectangle of all later rows and earlier columns to be missing. After dropping $a$ last rows and $b$ first columns, any remaining hole would cost at least $(a+1)(b+1)$ missing cells. At every index set, the surviving interval is the intersection of its retained row and column intervals. These intervals produce the smaller matrix tensor. Lean checks the integer rectangle and trimming inequalities, including the equal-trim floor-square-root case. [Lean proof](../lean/FerrersMatrixCompression.lean)

## From slice rank to probability

For any binary trilinear form $E$, define its analytic rank $u=-\log_2 \mathbb E[(-1)^E]$. The expectation is positive, since averaging the last block first makes it the probability that the last-block linear form vanishes identically. Lampert's Theorem 1.2 gives $\operatorname{srk}(E)\le5u+4\log_2(u+1)+29\le9u+33$. Use it over the finite base field with $E=M_d-U$. Equation (2) gives $u\ge\max(0,g^2/12-11/3)$. Finally $\Pr[E=0]=(1+2^{-u})/2$, proving (1). In particular any advantage $\delta>0$ forces

$$
 s\ \ge\ \left(d-\sqrt{12\log_2(1/(2\delta))+44}\right)_+^{9/4}.
$$

Lampert's published trilinear theorem suffices here. Chen and Ye give a newer result for higher-order partition rank. [Lampert, *Slice rank and analytic rank for trilinear forms*](https://doi.org/10.19086/da.145198) · [Chen and Ye](https://arxiv.org/abs/2611.30721)

## Which predictions the estimate covers

- **Input-independent randomness.** Inequality (1) still holds if each independent random seed selects a trilinear form of border rank at most $s$, by averaging its success probability. Allowing selection to depend arbitrarily on the data changes the statement. For example, the zero form and the $d^3$ rank-one triangle monomials suffice with an unrestricted selector. When the contraction is one, some triangle monomial evaluates to one, and when it is zero the selector can use the zero form.
- **A fixed Boolean decoder of several trilinear features.** For $h:\mathbb F_2^k\to\{-1,1\}$ and features $U_1,\ldots,U_k$ with total border-rank budget $s$, expand $h$ in binary Fourier characters. Each term is the phase of a sum of a subset of the $U_i$, with border rank at most $s$. The absolute correlation with $(-1)^{M_d}$ is at most $\|\widehat h\|_1\,2^{-\max(0,g^2/12-11/3)}$, and $\|\widehat h\|_1\le 2^{k/2}$ by Parseval. The conclusion depends on both total rank and decoder norm.
- **Arbitrary pairwise factors.** Multiply the phase of $U$ by any bounded real functions of $(A,B)$, $(B,C)$ and $(C,A)$, one for each pair, all of absolute value at most one. Three applications of Cauchy–Schwarz bound the eighth power of absolute correlation by the expectation of the phase of the eight-corner alternating sum of $M_d-U$. Trilinearity makes this sum $(M_d-U)(A_0+A_1,B_0+B_1,C_0+C_1)$, whose three arguments are independent uniform. Thus the correlation is at most $2^{-\max(0,g^2/12-11/3)/8}$.

The scale of the exponential decay can already be seen at $U=0$. The bias then equals $\Pr[AB=0]$. Conditional on $A$ having rank $j$, this probability is $2^{-dj}$. The count of rank-$j$ matrices is within absolute constant factors of $2^{(2d-j)j}$, from the usual ordered-basis count. Summing over $j$ gives bias $\Theta(2^{-3d^2/4})$, since $(d-j)^2+dj=3d^2/4+(j-d/2)^2$. This simple predictor precludes a uniform bound of order $2^{-\omega(d^2)}$ on the advantage.

A near-linear SAT algorithm would evaluate this contraction exactly on a bit RAM under the journal's reduction. Extracting a predictor in the stated class from that RAM evaluator with parameters beating (1) would contradict the hypothesis. The evaluator itself is an unrestricted program. The search located earlier compression and analytic-rank theorems, and earlier error-correction results for algorithms that predict matrix outputs. Priority for their combination into the specific scalar phase inequality above remains unverified. [Contraction from SAT](verifying-matrix-products-from-sat.md) · [Hirahara and Shimizu on error correction for matrix multiplication](https://doi.org/10.4230/LIPIcs.ICALP.2025.97)

Averaging the error phase over the third matrix first gives an additional interpretation. Identify $U$ with the bilinear output matrix $H(A,B)$ under the nondegenerate trace pairing. Then $\Pr[H(A,B)=AB]=2^{-u}$, where $u$ is the analytic rank above. Consequently the whole product agrees on at most $2^{-\max(0,g^2/12-11/3)}$ of uniform input pairs. A selector allowed to choose among $2^b$ prescribed candidates, even after seeing the two factors, gains a factor of at most $2^b$ on this whole-product probability.

Choosing the three rectangle starts simultaneously improves the factor $3/4$ in (2) to one. The same geometric argument handles affine tests that mix all three matrices. [Simultaneous packing and strengthened predictor estimate](affine-restrictions-of-one-large-matrix-product.md)
