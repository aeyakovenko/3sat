# Exact operand cost of splitting a binary matrix product into rank-promised products

Consider testing a binary product by issuing several smaller proposed-product tests. Each test receives two rectangular operands and a proposed answer. Suppose the entries supplied to the tests are arbitrary affine binary functions of the original operands and answer, and every test satisfies a promise that its error has rank at most r, on *all* source inputs. How cheaply can this implement exact verification of an unrestricted product?

For square side d and 1 ≤ r ≤ d, the tests need at least **d² + d³/r nonconstant operand entries** in total. If r divides d, grouping the rows into blocks attains equality. The price counts each occurrence of a nonconstant bit in either factor of a test. All affine preprocessing, all constant entries, and the entire proposed-answer array of every test are free. Shared computation inside a single verifier can have a different cost from separately supplying the operands to each test.

## The rectangular bound

Let U, V, P have shapes a × b, b × c and a × c, with b ≥ 2. For each test i choose Xᵢ, Yᵢ and Zᵢ of compatible dimensions. Suppose

1. all the entries are affine functions of the bits of U, V, P,
2. rank(XᵢYᵢ + Zᵢ) ≤ r on every input, and
3. all tests hold exactly when UV = P.

Then the sum S of nonconstant slots in the Xᵢ and Yᵢ satisfies

$$S\ \ge\ b\min(a,c)+bac/r.$$

Write E = UV + P. Every entry of the ith test residual is a degree-at-most-two Boolean function vanishing on all correct products. Hence its residual matrix is Lᵢ(E) for a linear map Lᵢ. The quadratic classification works for rectangular products. Its proof uses two distinct inner indices to eliminate quartic terms from products of two answer bits, then cubic terms from one operand bit times one answer bit. It imposes no lower bound on the outer dimensions. Setting U = V = 0 and varying P shows the combined map L is injective. [Quadratic classification with the coefficient argument](finite-boolean-checks-for-a-matrix-product.md)

Call a row or column of Lᵢ active if it contains a nonzero entry form. Let hᵢ, wᵢ count its active rows and columns. A nonzero coordinate has the form ⟨M,E⟩ for M ≠ 0. After P = 0, its polar form has rank 2b rank(M), since each of the b independent inner indices gives an off-diagonal block with M and its transpose. The polar matrix of a product of two affine bits has rank at most two and vanishes if one factor is constant. The affine term Zᵢ contributes zero. Thus each active row requires at least b nonconstant entries in the corresponding row of Xᵢ. Each active column requires at least b nonconstant entries in the corresponding column of Yᵢ. In each test mark the operand on the side with more active rows or columns, resolving ties arbitrarily. It has at least b max(hᵢ,wᵢ) nonconstant entries.

The space im Lᵢ consists of matrices of rank at most r. Its dimension is at most r max(hᵢ,wᵢ). Here is an argument over the binary field including the small-field case. Delete inactive coordinates, transpose as necessary and write m = max(hᵢ,wᵢ), n = min(hᵢ,wᵢ). If n ≤ r the ambient dimension proves the estimate. Otherwise represent matrices as maps from an n-dimensional subspace of the field of size 2ᵐ into that field. The evaluations of linearized polynomials

$$\sum_{j=0}^{n-r-1} t_j x^{2^j}$$

form a binary space of dimension m(n−r). Every nonzero polynomial has at most 2^(n−r−1) roots, so its evaluation has rank at least r+1. This space intersects im Lᵢ trivially. Its codimension gives the claim. Since L is injective, the marked operands together have at least bac/r nonconstant entries. [Gabidulin, *Theory of Codes with Maximum Rank Distance*](https://www.mathnet.ru/php/archive.phtml?jrnid=ppi&option_lang=eng&paperid=967&wshow=paper)

There is a second cost for the opposite operands. Fix P = 0 and restrict (U,V) to the common kernel of the linear parts of every slot in those operands. Each test now has one constant operand, so all residuals are affine. A linear left inverse of L recovers UV, which must be affine on this subspace. Any subspace W of pairs where UV is affine has codimension at least b min(a,c). Indeed let K be the common kernel of all matrices U appearing in W, with dim K = k. Projection onto U has dimension at most a(b−k). For any (0,V₀) in its kernel, the polar identity on W gives UV₀ = 0 for every U in the projection, hence im V₀ lies in K. The projection kernel has dimension at most ck. Thus dim W ≤ a(b−k)+ck ≤ max(ab,bc). Each nonconstant slot imposes at most one linear constraint. The opposite operands contribute at least b min(a,c) further slots.

For square matrices divide the rows into blocks of at most r and test each block of A against the whole of B, with its matching rows of P. The cost is d² + ceil(d/r)d². This proves exact optimality at each divisor. The statement uses a common cap on each test's residual rank, including on rejected source inputs. Low-rank verification algorithms can exploit that cap over other coefficient fields. This reduction bound applies before such an algorithm is chosen. [Rank-promised verification](folded-checks-for-low-rank-product-errors.md)

## Nonlinear preprocessing

Suppose a reduction uses free XOR, constants and q binary nonlinear gates to prepare its test instances. Let S count all nonconstant operand slots of the resulting tests. The following bound survives. For any positive integer s with d−2qs ≥ 2 and s ≤ d−qs, put b = d−2qs. Then

$$S\ \ge\ b s+b s^2/r.$$

Traverse the preprocessing in topological order. When both incoming bits of a nonlinear gate are affine on the current linear subspace, fix one to its origin value by one linear constraint. On the resulting subspace the gate is affine, since every unary Boolean function is affine. All preprocessed entries become affine after at most q homogeneous constraints on (A,B,C). The same argument applies on the origin branch of an adaptive reduction that also charges one unit for each binary parity branch test and performs the conjunction of its output tests on that branch.

To retain a large product under these restrictions write the constraints as triples of masks Uⱼ, Vⱼ, Wⱼ paired with A, B, C in the entrywise inner product. Take any d × s matrix L of full column rank. Choose a d × s matrix R of full column rank orthogonal in every column to every column of every WⱼᵀL. This is possible since the latter columns span dimension at most qs. Choose inner directions for A in the orthogonal complement of the columns of all UⱼᵀL, and inner directions for B in the orthogonal complement of the columns of all VⱼR. Both allowed spaces have dimension at least d−qs. Their dot-product pairing has rank at least d−2qs by the dimension bound on its kernel. Hence they contain column bases H and G of size d × b with HᵀG = I. The substitution

$$ A=L X H^\mathsf T,\qquad B=G Y R^\mathsf T,\qquad C=L Z R^\mathsf T $$

kills each mask and carries XY+Z injectively to L(XY+Z)Rᵀ. Every test is now an affine reduction from independent s × b, b × s, s × s arrays. The rectangular bound applies, and restriction can only decrease the number of nonconstant slots.

For q+1 ≤ d/6 take s = floor(d/(3(q+1))). This gives S = Ω(d²/(q+1) + d³/(r(q+1)²)). For example r ≤ √d and S = O(d² log^k d) require q+1 = Ω(d^(1/4)/log^(k/2) d). This modest lower bound permits near-quadratic preprocessing. The unrestricted binary product graph over an odd-characteristic scalar network and the SAT time lower bounds remain open in this analysis. Priority for these reduction bounds is unestablished. [Finite checks](../audits/rank_promised_reduction_audit.py)
