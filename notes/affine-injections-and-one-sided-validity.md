# Affine families of injective lists and one-sided permutation validity

For an alphabet of size Q encoded in binary, the largest possible dimension of an affine family of injective m-row tables into the initial interval [0,Q) is
$$
R(Q,m)=\sum_{t=1}^m\lfloor\log_2(Q/t)\rfloor=\sum_{j\ge1}\min\{m,\lfloor Q/2^j\rfloor\},\qquad 1\le m\le Q.
$$
The upper bound holds for any Q-element subset of a binary vector space. At m=Q it gives the full permutation capacity Q minus the number of ones in its binary expansion. The proof varies one row at a time and uses induction on the remaining rows.

For the hard list parameters m=2ᵏ and b=2k with k≥2, this also closes a potential loophole in using invalid table encodings. An affine encoder into q-point permutation tables of ordinary width ⌈log₂q⌉<b that produces valid outputs on every list of *either one fixed verdict* necessarily produces valid outputs everywhere. In particular, counting every invalid output as a no instance gives the same affine encoding length obstruction as requiring total validity. [Two-permutation lower and matching encoding](affine-capacity-of-explicit-permutation-tables.md)

## Upper bound

Fix a table c in the affine family c+V. Let Aᵢ be the set of possible values at position i among tables agreeing with c everywhere else. Each Aᵢ lies in the alphabet Y and has size $2^{d_i}$, where dᵢ is the dimension of the kernel of the coordinate deletion that forgets row i.

The Aᵢ are pairwise disjoint. If u lay in Aᵢ and Aⱼ, take the changes from c that place u at i or j respectively. Both belong to V, and their sum applied to c places u at both rows, contradicting injectivity. This works when one change is zero as well.

Thus some Aᵢ contains at most Q/m elements and dᵢ≤⌊log₂(Q/m)⌋. Deleting that row yields an affine family of injective (m−1)-tuples of dimension dim V−dᵢ. Induct from the zero-dimensional space of empty tuples to get the first displayed bound.

## Attainment on an initial interval

Use zero-based binary labels with leading zeros as needed. The complete aligned binary blocks contained in [0,Q) form a forest under inclusion. A block of height j has size 2ʲ, and there are ⌊Q/2ʲ⌋ complete blocks at that height. Write H=⌊log₂(Q/m)⌋. Choose m distinct height-H blocks meeting each complete height-(H+1) block. This is possible because each larger block has two candidate children, there are fewer than m such parent blocks, and at least m children in total. Take one marked leaf from each chosen block.

Put an independent Boolean parameter at every positive-height forest node containing a marked leaf. Following the *original* route of each marked leaf, XOR each bit of its address inside its forest root with the parameter at the corresponding branching node. Keep its root prefix fixed. Given the parameters, this operation preserves distinctness within every root by looking at the first branch of divergence. Given a single row address its output bits are affine in the parameters. Every parameter changes a distinct nonempty group of output positions, since in any given output bit at most one parameter occurs. Thus the rank is the exact number of occupied positive-height nodes.

For heights j≤H there are precisely m occupied nodes. For heights j>H, every complete node is occupied, since it contains a complete height-(H+1) block. This counts the second expression for R. Equivalence to the first expression follows by counting pairs (t,j) with 1≤t≤m and t2ʲ≤Q.

For the entire b-bit alphabet, the minimum codimension of an affine space consisting solely of distinct m-record lists is consequently
$$
D(m)=\sum_{t=1}^m\lceil\log_2 t\rceil=m\lceil\log_2m\rceil-2^{\lceil\log_2m\rceil}+1.
$$
At m=2ᵏ this is mk−m+1. The minimum is over all affine spaces. This gives a lower bound on the parity-certificate size at **every** all-distinct input and finds inputs attaining it. No assertion about attainment at every input is needed.

## Affine spaces of colliding lists

Let $M=\binom m2$, U=2ᵇ and let A=c+V be an affine subspace of codimension d in the full space of lists. For i<j let Kᵢⱼ be the intersection of V⊥ with the b-dimensional space of dual vectors supported on the pair i,j with the same value at both positions. Apart from zero these pair spaces are disjoint. Consequently
$$
\sum_{i<j}(2^{\dim K_{ij}}-1)\le 2^d-1.
$$
On a uniformly random list in A, the difference of records i,j is uniform on an affine space of dimension b−dim Kᵢⱼ. Thus the probability of that collision is at most 2^{dim Kᵢⱼ}/U. Summing yields
$$
\Pr_{x\in A}[\text{some collision}]\le (M+2^d-1)/U.
$$
When M≤U/2, all affine subspaces of codimension d<b therefore contain a distinct list. A single equality x₁=x₂ attains codimension b and has collisions everywhere. The parameters m=2ᵏ, b=2k satisfy M≤U/2.

## Validity on just one verdict suffices

Suppose every output bit of each q-entry binary table is an affine function of the source bits. Let e=⌈log₂q⌉ be the field width for the entries. If a table is invalid somewhere, one of its rows assumes a specific out-of-range value or two rows coincide. Either failure has a nonempty affine fiber of codimension at most e, obtained by fixing an e-bit affine output or difference. This argument also applies when all leading padding bits are fixed in advance. Variable extra high bits have to be counted separately or treated individually as nonzero padding failures.

* If tables are valid on all distinct lists and M≤U/2, the existence of a failure with e<b contradicts the colliding-list bound.
* If tables are valid on all colliding lists, the existence of a failure with e<D(m) contradicts the distinct-list bound.

For the hard parameters with k≥2 one has D(2ᵏ)>2k−1. The claimed one-sided validity result follows in either polarity. If q already requires at least b bits per entry, then q>2^{b−1}, above the q=O(mb) regime used to optimize output length. For q in that regime and large k, the full-table rank bound and the additive-period argument therefore still require q=Ω(mb). An arbitrary acceptance convention on malformed tables is compatible with this conclusion if at least one entire source verdict must map to well-formed tables. An encoder permitted to use arbitrary malformed tables on both verdicts has a different promise.

In the distinct-valid orientation, one nonempty failure fiber already contains a fraction at least $2^{-e}(1-(M+2^e-1)/U)$ of all lists that are both distinct and malformed, whenever the factor is positive. The inverse-width scale is attainable up to a constant. For q=2ᵉ, choose an e-bit linear projection z of the first pair's difference and output the table a↦za over the finite field of q elements. For each fixed input index a all output bits are affine. Exactly the codimension-e set z=0 produces an invalid table. At e=b the zero multiplier means the whole first pair is identical, so the width cutoff on the distinct-valid implication is attained.

## Scope and checks

The peeling bound also sharpens the gate-elimination lower bound in the companion note. If t two-input nonlinear Boolean gates together with arbitrary affine gates produce two always-valid q-entry tables from which list distinctness can be recovered, fixing one gate input per nonlinear gate and then fixing the two tables on the remaining affine flat costs at most t+2(q−s₂(q)) independent equations. Doing this through an all-distinct input gives
$$
t+2(q-s_2(q))\ge D(m).
$$
The same inequality holds if only the colliding inputs must have valid encodings. Write e=⌈log₂q⌉. If t+e<D(m), any failure fiber in the gate-restricted space is an affine subspace of global codimension at most t+e. It would have to contain a colliding list, so the whole gate-restricted family is valid. If t+e≥D(m), the bound follows from 2(q−s₂(q))≥e. To see this last inequality, q−s₂(q)≥⌊q/2⌋ and 2⌊q/2⌋≥⌈log₂q⌉. If only the distinct inputs must have valid encodings, the same reasoning proves the stated inequality under M≤U/2 and t+e<b. More generally, on that low-gate branch a nonempty failure would occupy at least $2^{-(t+e)}(1-(M+2^{t+e}-1)/U)$ of all lists that are distinct and malformed. Fixing a branch does not guarantee globally affine output when t>0.

## Witnesses and affine certificates

An exact verifier for distinct lists may use any number of private Boolean witnesses, any affine equations on the combined inputs, and s constraints of the form $\ell_i m_i=n_i$ with affine operands over the binary field. Fixing all s left operands produces at most 2ˢ affine solution spaces. Their projections to the public list are affine spaces. By soundness every such projection lies among the distinct lists, so each covers at most a $2^{-D(m)}$ fraction of all lists. Thus the accepted fraction of all lists is at most $2^{s-D(m)}$. For m=2ᵏ, b=2k the distinct lists have density greater than one half. Completeness therefore forces $s\ge D(m)=mk-m+1$. The statement permits unrestricted witnesses and acquires no arithmetic-circuit preprint dependency.

When the input consists of all Q values in some order, the minimum number of affine subspaces in any cover of this one verdict is exactly $Q!/2^{Q-s_2(Q)}$. Each affine space has size at most the denominator. For attainment use the full group of tree automorphisms on the maximal dyadic blocks of [0,Q), independently within each block. In the array-of-images representation this group is the affine family constructed above with m=Q. Each right coset just reorders its row coordinates, hence is affine. The cosets partition the entire permutation group.

These inequalities concern verification and preprocessing. The full unrestricted deterministic SAT clock remains open.

The [Lean file](../lean/PrivateRowsOfAffineInjections.lean) checks the disjointness of the single-row choices in any affine-closed injective family and the iteration of the deletion recurrence. Rank-nullity and the counting step that supplies its hypothesis are manuscript arguments. The finite [audit](../audits/affine_injection_capacity_audit.py) exhausts all 15 pairs 1≤m≤Q≤5, checks the marking construction on all 3,321 pairs through Q=81, and verifies the collision density bound on 177,665 affine subspaces of codimensions zero through two. Related work studies tight partitions of affine space and parity certificates of Boolean functions. The argument above uses neither as a black box. I did not locate the full injection formula or the one-sided-validity statement in the sources searched. Priority is unestablished. [Filmus et al., *Irreducible subcube partitions*, §4.2.1](https://arxiv.org/abs/2212.14685) · [Zhang and Shi, *On the parity complexity measures of Boolean functions*](https://doi.org/10.1016/j.tcs.2010.03.027)
