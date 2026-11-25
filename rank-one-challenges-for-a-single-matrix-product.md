# How many bilinear algorithms does a single matrix product need for rank-one challenges?

Let A and B be independent uniform d by d binary matrices, and let u and v be independent uniform nonzero binary d-vectors, independent of the inputs. The requested bit is uᵀABv. A single challenge takes just d products of linear forms if the forms are allowed to depend on (u,v). How much information about the challenge does a near-quadratic bilinear algorithm need?

## A sharp menu bound

A bank precomputes at most s fixed bits of the form ℓ(A)r(B), with binary linear ℓ and r. Given the challenge, the decoder chooses one bank and a linear combination of its bits. It may add arbitrary, challenge-dependent bits f(A) and g(B). The choice of bank and coefficients may depend on (u,v) and independent coins. They must be fixed before seeing (A,B). Let K be the number of banks. Sign bias β means success probability (1+β)/2.

Fix 2 ≤ σ < 9/4, and put

$$
t_σ=\tfrac12\bigl(σ-1+\sqrt{(σ-1)^2-1}\bigr).
$$

If s ≤ d^{σ+o(1)} and β is a fixed positive constant, then for every η>0 and all sufficiently large d,

$$
\log_2 K \ge d-d^{t_σ+η}.
$$

Conversely there are menus of banks of size d^{σ+o(1)} with

$$
\log_2 K \le d-\lfloor d^{t_σ}\rfloor+1
$$

that answer every challenge on every input exactly. At σ=2 the number of bits of bank selection is d minus a saving of order d^{1/2+o(1)}. This uses the paper's separate **rectangular** theorem, in the formal division-free model over every field. The specialization is ω(1,1,t)=2+max(0,2t−1)²/(4t), whose increasing branch takes value σ at t=t_σ. All asymptotics concern d→∞. [Rectangular theorem and formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/107.md) · [Euclidean geometry in the asymptotic spectrum of tensors](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf).

## Correcting the good masks

Fix the coins with sign bias at least β. On a fraction at least β/2 of the challenges the conditional bias has magnitude at least β/2. A bilinear residual with coefficient matrix of binary rank r, even after adding arbitrary separate functions f and g, has sign bias at most 2^{-r/2}. Indeed, for the correlation E[(-1)^{aᵀMb+f(a)+g(b)}], apply Cauchy–Schwarz in a and average a first in the resulting second moment. Only pairs (b,b′) with M(b+b′)=0 survive, of probability 2^{-r}.

For each bank take the set of assigned good masks uvᵀ and let W be their binary span. Choose a basis of q≤d² actual good masks. A decoder on each basis mask has residual rank ≤k=⌈2 log₂(2/β)⌉ after its two separate functions are deleted (the rank refers to the underlying bilinear residual). Adding at most k rank-one products per basis mask corrects it exactly. Thus the tensor of AB restricted to output functionals W has rank at most s+kq≤d^{σ+o(1)}. The same bank products are shared across all q functionals.

## Counting masks and finding a rectangle in the same subspace

Write W as a subspace of d by d matrices. For each i, let U_i be the space of ith rows of its matrices whose rows with index greater than i vanish. Let λ_i be dim U_i. Row elimination gives Σλ_i=dim W. In the two conclusions below, index the dimensions in descending order *after* computing the row filtration.

1. The number of ordered nonzero pairs (u,v) with uvᵀ in W is at most Σᵢ 2^{i−1}(2^{λ_i}−1).
2. The tensor restricted to W degenerates, over the algebraic closure, to a tensor containing the rectangular multiplication ⟨i,d,λ_i⟩ for every i with λ_i>0. Here ⟨a,b,c⟩ multiplies an a by b matrix and a b by c matrix.

For (1), fix nonzero v. An echelon basis of the space of u with uvᵀ in W has distinct last pivots. At each pivot row i, v belongs to U_i. Thus its dimension is at most the number of U_i containing v. Order the row spaces by decreasing dimension. If v lies in m of them at positions i₁<⋯<iₘ, then 2^m−1=Σⱼ2^{j−1}≤Σⱼ2^{iⱼ−1}. Sum over v≠0. Each i contributes its weight once for each of the 2^{λ_i}−1 nonzero members of U_i. Nested coordinate spaces with row i of length λ_i attain equality.

For (2), take a basis of W adapted to last pivot rows. Multiply output row i by z^{-i} and the corresponding basis vector of pivot i by z^i. In the limit z→0 each vector retains exactly its leading row. The vectors in that row give a basis of U_i. The mask row action is an input change on the row index of A, so all nonzero parameter values define isomorphic restricted tensors. In the resulting direct sum of row spaces, apply one generic invertible change of columns over the algebraic closure. For each i, projection of the transformed U_i to its first λ_i columns is an isomorphism: this is a nonempty open condition for that i, and finitely many such opens intersect. Use a basis in each row reduced to the identity in its first λ_i columns. Scale column j by z^j, and rescale each row basis vector with pivot j by z^{-j}. The limit is the direct sum of coordinate rows of lengths λ_i. The column action is an input change on B. Permute rows by decreasing length and keep the first i rows and first λ_i columns. Restricting the corresponding input dimensions gives exactly the claimed dense rectangle. This proves a border-rank bound for that rectangle even though W was counted over the binary field.

The incidence calculation is related to higher weights of simplex product codes and linear sections of Segre varieties. The argument needs the *same* row dimensions both for incidence and for the border-rank obstruction. Priority for the incidence inequality by itself is not claimed. [Weight hierarchy of product codes](https://doi.org/10.1016/S1571-0653(04)00158-1) · [Segre codes and higher weights](https://doi.org/10.1016/j.ffa.2025.102766).

## Finishing the lower bound

For each fixed δ with 0<δ<1−t_σ, every positive λ_i satisfies i+λ_i≤d+d^{t_σ+δ}, for all sufficiently large d. Otherwise the longer side of the rectangle is at least d/2, and the shorter side exceeds d^{t_σ+δ}, since both are at most d. Put n=⌊d/2⌋ and t′=t_σ+δ/2. By restricting and using the cyclic and transpose symmetries of matrix multiplication we get ⟨n,n,⌈n^{t′}⌉⟩ of border rank at most d^{σ+o(1)}.

For precision, a *single* tensor with dimensions n,n,⌈n^{t′}⌉ and border rank r bounds the asymptotic exponent by log_n r. Powering, interpolating the border degeneration with subexponential overhead in the power, and padding between powers proves this over the infinite algebraic closure. For an arbitrarily large exceptional d we would obtain ω(1,1,t′)≤σ+o(1), contradicting the rectangular theorem over that field. Thus (1) gives at most d·2^{d+d^{t_σ+δ}} good challenges per bank. All banks together cover at least (β/2)(2^d−1)² challenges. Taking logarithms and absorbing the logarithmic term by choosing δ<η proves the result. Fixing the random coins required no per-input derandomization.

## Matching upper bound

Set a=⌊d^{t_σ}⌋. Fix an (a−1)-dimensional subspace H of challenge vectors u and partition by its 2^{d−a+1} cosets. The linear span of each coset has dimension at most a. Let P have a rows spanning that span, padding with zeros as necessary. The bank computes the entries of (PA)B via a rectangular bilinear algorithm. Formal division-free arithmetic algorithms yield bilinear algorithms within a constant factor in size by retaining bidegrees (0,0), (1,0), (0,1), (1,1) at each gate. The rectangular theorem over the binary field therefore gives d^{σ+o(1)} bank products. Every u in the coset is a linear combination of P's rows, so each uᵀABv is a linear decoding of those products.

## The full-mask challenge actually supplied by SAT

Replace uvᵀ by a uniform unrestricted binary mask Z. Let D=d² and y_σ=4(√σ−1). In the same model the sharp bounds on log₂K become D−d^{y_σ+o(1)} in the following precise sense: for each η>0 every constant-bias menu needs at least D−d^{y_σ+η} bits of selection, and D−⌊d^{y_σ/2}⌋² bits suffice for exact computation. At σ=2 the saving exponent is 4(√2−1), about 1.657.

For the lower bound the good masks of each bank again span a space W of dimension q with restricted border rank at most s+kq≤d^{σ+o(1)}. The arbitrary-mask theorem in the earlier note lower-bounds that rank by d^{(1+(log_d q)/4)²}, so q≤d^{y_σ+o(1)}. Each bank covers at most 2^q masks. For the upper bound take W to be all masks supported on one square block of side b=⌊d^{y_σ/2}⌋. Compute the block product with rank d^{σ+o(1)} by the rectangular formula. Group masks by their cosets modulo W. In each coset also compute the scalar for its fixed representative Z₀; the coefficient matrix of this scalar is a permutation of Z₀⊗I_d and has rank ≤d². A bank for the coset can now answer every member exactly. This family of upper bounds uses s=d^{σ+o(1)}, allowing the additive d² products even at σ=2. [Arbitrary-mask rank inequality and balanced-block construction](predicting-entries-of-a-binary-matrix-product.md).

## Consequence for the SAT bridge

One product challenge can already be answered with two matrix–vector multiplications in O(d²) bit operations, or d bilinear products when linear operations are free. A hypothetical linear SAT solver deciding whether a supplied matrix C equals AB has no obligation to provide a challenge-independent bank, linear decoding, or selection independent of A and B. The theorem identifies exactly how much dependence on the challenge the stated algebraic model can tolerate. Obtaining that model from the Boolean decision algorithm remains open. Compare [coordinate challenges](predicting-entries-of-a-binary-matrix-product.md) and [the SAT verifier](verifying-matrix-products-from-sat.md).

[Lean verification of the weighted incidence inequality and its finite summation](RankOneChallengeIncidence.lean) · [Exhaustive audit](rank_one_challenge_bank_audit.py). The audit checks all 67 binary 2 by 2 mask subspaces and all 2,825 subspaces in each of the 2 by 3 and 3 by 2 orientations, including equality for the corresponding nested-row spaces. The degeneration and asymptotic exponent argument above are on paper.
