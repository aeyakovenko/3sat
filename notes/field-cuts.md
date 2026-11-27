# A fast SAT restriction with nearly maximal communication rank on every balanced cut

## 2026-11-23 · Strengthening the cut-rank test

The bounded-degree construction in [the first cut experiment](transcript.md) has a rank lower bound c·k on balanced cuts, where c can be small. A stronger candidate lower-bound criterion could demand that *every* balanced cut come within o(k) of the maximum allowed by its dimension. There is a counterexample even to this strengthening.

For infinitely many even k there is a width-three SAT template of encoded size k·poly(log k), with k independent input signs, with the following properties.

* For every split into u and v signs, u≤v, the base-two logarithm of the real sign-matrix rank is at least u−O(k/log k). On equal splits its average is greater than k/2−2.
* One uniform promise algorithm reads the forced inputs and evaluates the template's gate list in topological order in time linear in the encoded length. The template may be chosen nonuniformly. No advice is needed by its evaluator.

The construction and bounds below are manuscript arguments. The novelty of this combination is undetermined. The classical ingredients include quadratic forms from linearized polynomials, the rank identity for graph-state phases, and probabilistic rank-width bounds for random graphs. [Schmidt](https://arxiv.org/abs/1803.04274) · [Hein, Eisert and Briegel](https://arxiv.org/abs/quant-ph/0307130) · [Lee, Lee and Oum](https://arxiv.org/abs/1001.0461)

### The quadratic function

Identify the input vector with an element x of F=GF(2^k) in a polynomial basis. Let λ:F→GF(2) be its constant-coefficient functional. Set t=⌈log₂ k⌉, and choose 2t independent uniform field coefficients a₀,…,a₂ₜ₋₁. Use

    q(x) = λ( x · Σⱼ aⱼ x^(2ʲ) ),     0 ≤ j < 2t.

On disjoint coordinate spaces U and V let B(x,y)=q(x+y)+q(x)+q(y) be its bilinear polar form. The sign matrix on U×V has log rank exactly the binary rank of B restricted to U×V. Indeed the single-side terms of q only flip row and column signs. The remaining rows are group characters on V, with exactly 2^rank distinct, mutually orthogonal characters.

**Restriction lemma.** For any ℓ≤t independent x₁,…,xℓ in U, the ℓ linear functionals B(xᵢ,−) restricted to V are jointly uniform on (V*)^ℓ. To prove surjectivity of the linear map from coefficient seeds to these functionals, suppose a dual dependence is given by y₁,…,yℓ in V. Vanishing of its pairing with every seed implies

    Σᵢ ( yᵢ xᵢ^(2ʲ) + xᵢ yᵢ^(2ʲ) ) = 0     for every 0 ≤ j < 2t.

Here λ(ac) vanishes for all a∈F only when c=0, since multiplication by a nonzero c is onto. Expand the yᵢ in an independent GF(2)-basis z₁,…,zᵣ of their span. Combining coefficients turns these equations into a homogeneous linear system over F. Its columns are the Frobenius powers of x₁,…,xℓ,z₁,…,zᵣ. These ℓ+r elements are GF(2)-independent since U∩V=0. The first ℓ+r rows form an invertible Moore matrix. Indeed, a nontrivial row dependence would yield a nonzero linearized polynomial of degree at most 2^(ℓ+r−1) vanishing on their entire 2^(ℓ+r)-element span. Thus every coefficient in the system vanishes. The coefficient of the column for xᵢ was yᵢ. This rules out any nonzero dual dependence and proves joint uniformity.

### All cuts at once

For a fixed cut with u≥t, the expected number of ordered independent t-tuples in its left kernel is at most 2^(ut)·2^(−vt)≤1, by the restriction lemma. If the kernel has dimension at least R≥t, it contains at least 2^((R−1)t) such tuples, by choosing vectors successively outside the preceding span. Set

    R = max(t, 1 + ceil((k+3)/t)).

The chance of that cut having nullity at least R is at most 2^(−k−3). For u<t the nullity bound is automatic. Summing over at most 2^k cuts gives failure probability at most 1/8.

For an equal cut the ℓ=1 case gives expected kernel cardinality 1+(2^u−1)2^(−v)<2, hence expected nullity <1 by concavity of log. Average this over equal cuts. The probability that this average nullity is at least two is less than 1/2. Both desired properties therefore hold for one and the same choice of coefficients. In the pair-load normalization in the cut journal, the average equal-cut log rank is multiplied by 2(k−1)/k. The score of the selected template is consequently within four of the universal ceiling k−1.

### Evaluation and SAT encoding

For an explicit infinite family of field presentations take k=2·3ʰ and reduce modulo P(z)=zᵏ+z^(k/2)+1 over GF(2). This is the cyclotomic polynomial of order 3^(h+1) and is irreducible: the multiplicative order of 2 modulo 3^(h+1) is 2·3ʰ. To see the order, 4−1 has 3-adic valuation one and cubing 1+3ʳu with r≥1 and 3∤u raises that valuation by exactly one. The order divides the totient and must be even, giving the asserted value. The Frobenius orbit of a primitive root of unity thus has degree k.

A product of two binary polynomials of degree below k can be computed by packing coefficients as base-2^b digits for b=⌈log₂(k+1)⌉, multiplying integers, and taking the low bit of each digit. Each convolution coefficient is at most k. Reduce modulo the trinomial with a descending scan, replacing each z^i for i≥k by z^(i−k)+z^(i−k/2). This reduction is a fixed O(k)-gate XOR network. Integer multiplication on O(k log k) bits has circuits of size k·poly(log k), using quasi-linear multitape multiplication and the time-to-circuit simulation. Successive squarings give all x^(2ʲ) with O(t) products. Including coefficient multiplications and addition, q has a k·poly(log k)-gate circuit. [Integer multiplication](https://doi.org/10.1016/j.jco.2016.03.001) · [Time-to-circuit simulation](https://scholarship.claremont.edu/hmc_fac_pub/597/)

Fix the seeds of a successful circuit, encode its gates by width-at-most-three clauses in topological order, require the output to be one, and add k unit clauses with independently chosen signs on its input wires. Each assignment to the signs forces exactly one computation. Binary indices contribute a logarithmic factor to the encoding, within the bound stated above. A RAM can evaluate any gate list in this format when promised that the units pin all its inputs. The proof needs existence of a good template at each indicated size. A fast algorithm for finding the seeds has not been supplied.

The rank test measures how much the two sides of a split depend on each other. Here many splits have nearly maximal dependence while a single arithmetic circuit computes the answer on the full input. Any successful RAM-time argument based on these cuts would need a further premise controlling how a machine can share work across them. The finite-field restriction map is tested in `field_experiment.py`.

### Every binary quadratic phase loses logarithmic rank on some balanced cut

Let A be any binary 2m-by-2m matrix, m≥4. Define δ as the maximum, over all sets S of m coordinates, of m−rank₂(A[Sᶜ,S]). Then

    δ ≥ (log₂ m − log₂ log₂ m)/2 − 4.

For a quadratic phase take A to be the matrix of its polar form. The rank identity above turns δ into the worst loss in log₂ of the real sign-matrix rank. Thus even with an arbitrary number of coefficient bits, every binary quadratic phase has a logarithmic loss on some balanced cut as m grows. Its mean loss can still be bounded by a constant.

**Proof.** Form the binary linear code C whose codeword for x in GF(2)^(2m) has paired symbol (xᵢ,(Ax)ᵢ) at each position i. It has binary dimension 2m. For a fixed balanced set S, the codewords supported inside S are precisely the x with x[Sᶜ]=0 and A[Sᶜ,S]x[S]=0. Their number is at most 2^δ.

Put a=⌊δ/2⌋+2. Since 0≤δ≤m and m≥4, we have a≤m. Require zero symbols on any m−a positions. The resulting subcode has dimension at least 2m−2(m−a)=2a, so it contains a binary subspace D of dimension exactly 2a. On D each of the m+a remaining coordinate symbols is one linear map to GF(2)². There are 2^(4a) possible maps. If a positions give the same map, setting those positions to zero imposes at most two additional independent binary equations. The resulting subspace of dimension at least 2a−2 is supported on the other m positions. But 2a−2>δ, contradicting the preceding bound. Thus each map occurs at most a−1 times and

    m+a ≤ (a−1) · 2^(4a).

If δ≥log₂ m, the displayed lower bound on δ follows directly. Otherwise a−1≤log₂ m for m≥4, while 4a≤2δ+8. Taking logarithms gives the claimed estimate. The matrix argument also applies to nonsymmetric binary matrices. Its communication-rank consequence uses the quadratic phase identity. The restriction to binary quadratic phases matters for that conclusion. The code viewpoint is related to worst-case list decoding from erasures and generalized Hamming weights. [Guruswami, discussion of erasure list decoding](https://www.cs.cmu.edu/~venkatg/pubs/papers/list-decoding-ICM.pdf)

In the four-dimensional experiment, every tested rectangle map was surjective for t=1 and t=2 across all 20,160 ordered bases. At t=2 the 64 distinct alternating forms all occurred. Their minimum rank across the three balanced coordinate cuts was zero for 10 forms and one for 54. Write P,Q,R for the three products of opposite-edge entries of any alternating four-by-four matrix. Its three cross-cut determinants are P+Q, P+R and Q+R. Their sum vanishes in GF(2), so they cannot all be one. This small identity explains the missing rank-two case independently of the enumeration.

### Retest after restrictions and changes of coordinates

Fixing some input signs before choosing the split is a stronger candidate test. For a quadratic q, substituting constants in the fixed coordinates adds only single-side terms to the surviving polar interaction. The restriction lemma already applies to the spans of *any two disjoint* sets of surviving coordinates. There are at most 3^k ordered choices of the two sets, counting discarded coordinates as a third class. Replace (k+3)/t in R by (k log₂ 3+3)/t. The same union bound gives one seed with the stated o(k) worst-case deficiency even after every partial fixing, as well as the same constant average deficit on the original equal cuts. Thus adaptively choosing which **input bits** to fix cannot rescue this numerical criterion on restrictions leaving a linear number of free coordinates on both sides.

A RAM can also store parities and use input-dependent information. There is a concrete distinction even for a fixed change of basis. Every alternating bilinear form splits into independent two-dimensional pairs and a radical. If B(e,f)=1, their span is nondegenerate; subtract suitable multiples of e and f from every remaining basis vector to make it orthogonal to that span, then continue on the complement. When the remaining form vanishes, all remaining vectors belong to the radical. In this basis, putting whole pairs on either side gives a balanced partition up to rounding with zero crossing rank, or one can split a single pair to obtain exact sizes at crossing rank at most one. This change of basis depends on the form. The union bound over coordinate restrictions does not cover such transformations, and the example identifies the role played by the representation of stored information.

Beame, Jayram and Saks give an earlier application of rapidly computable quadratic forms to variable partitions and branching-program time–space bounds. Their Fourier-matrix construction and computational model provide closer precedent than the graph-rank identity alone. [Beame, Jayram and Saks, §4.2](https://homes.cs.washington.edu/~beame/papers/branch.pdf)
