# The communication matrix of a fixed binary matrix product

Fix a binary d × d matrix C of rank r. The matrix with rows A, columns B and entries [AB=C] has the following rank over **every** coefficient field,

$$ M_{d,r}=\sum_{k=r}^d {d\brack k}_2\prod_{j=0}^{r-1}(2^k-2^j)
          =\Theta\big(2^{\lfloor(d+r)^2/4\rfloor}\big). $$

The same number is the minimum number of disjoint all-one rectangles partitioning its ones. The estimate has absolute constants. Its proof determines the whole matrix after duplicate and zero rows and columns are removed.

Let I = im C. Use the finite partially ordered set of pairs (S,f), where S is a subspace of the binary d-dimensional middle space and f is a linear surjection S → I. Order these pairs by extension of functions. A viable row A has I contained in im A. Its type is (T, A restricted to T), where T is the inverse image of I. Every type (T,g) occurs. Extend g on a complement of T by a map injective modulo I, possible since dim T ≥ r. A viable column B has ker B contained in ker C. Its type is (S,f), where S = im B and f(Bx) = Cx. Every such type occurs. Choose a linear lift I → S of f, lift C using it, then map ker C onto ker f with the remaining freedom to obtain a surjective B onto S. The available kernel has dimension d−r ≥ dim S−r.

For these types, AB = C precisely when the row type extends the column type. The resulting matrix is the zeta matrix of the poset, triangular with diagonal ones in a linear extension. Thus its rows and columns are distinct and it has full rank over every field. Each row type furnishes one all-one rectangle by taking its copies and all accepted columns. Conversely each rectangle in a disjoint partition adds at most one to the rational rank. Counting the possible domains and surjections gives the displayed sum. The Gaussian binomial is within absolute constant factors of 2^(k(d−k)), and the surjection count is within absolute constant factors of 2^(kr), since the infinite product of (1−2^(−j)) for j ≥ 1 is positive. The exponent k(d+r−k) peaks at the nearest integers to (d+r)/2. Summing its tails costs a constant factor.

This gives exact equality and a uniform interpolation between C=0 (the number of subspaces) and C=I (the order of the invertible group). For example, at d=3 the respective ranks for r=0,1,2,3 are 16,35,84,168. A cut in a binary tensor network separating the A and B input banks needs at least log₂ M binary edges when the cut exists and C is fixed. This rank calculation alone charges at most order d² edges.

## Reductions to prescribed answers

Both endpoint tests still contain an unrestricted proposed product, at constant-factor dimension blowup. To reduce AB=C to a zero product in side 3d, place [A I 0] in the first block row of the first factor and [B; C; I] in the first block column of the second factor, filling the remaining blocks with zeros. Their product has a single possibly nonzero block AB+C. Both factors always have rank d.

For the identity target, form two unipotent matrices

$$U=\begin{pmatrix}I&A&0\\0&I&B\\0&0&I\end{pmatrix},\qquad
  V=\begin{pmatrix}I&A&C\\0&I&B\\0&0&I\end{pmatrix}.$$

Their product differs from I only in the upper-right block AB+C. Thus a fixed identity target with invertible operands already suffices for any unrestricted input. The reductions copy only input coordinates and constants; each input bit occurs at most twice. These observations leave open the size of a network computing any of the three predicates in odd characteristic. The poset decomposition is elementary, and priority is unestablished. [Finite audit](rank_promised_reduction_audit.py)
