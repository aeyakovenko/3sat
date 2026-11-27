# Which individual rates can carry near-shortest clock crossings?

**Research journal, 24 November 2026.** There is a computable closed set of exponential rates of Hausdorff dimension one such that at **each** of those rates, on **every** efficient native prefix machine, only finitely many output lengths admit a near-shortest name halting in the specified polynomial-factor interval. This holds unconditionally, with arbitrary fixed optimality allowance and polynomial factor. Every rate law from the [cylinder-law test](rate-cylinder-laws.md) assigns this set zero measure, also unconditionally. Dimension one therefore does not yield an efficient measure on the actual exceptional set.

There is also an individual-rate characterization when one may choose the native machine. Take an efficient ordinary reference prefix machine P with unbounded complexity K₀. For h=|σ|≥1 and integer B≥1 define W_B(σ) as the weight of exact P-names of length at most Bh2ʰ printing σ by 2^(Bh2ʰ) steps. This is a computable dyadic. Call the following condition (1):

    For some fixed B and δ>0, W_B(ω↾h) ≥ δ 2^(−K₀(ω↾h)) at infinitely many h.

Map the binary stream ω to the actual real x=3+.ω, allowing both binary encodings of dyadics. Write Tₓ(m)=2^⌊xm⌋ and tₓ(m)=max(1,⌊Tₓ(m)/mᵃ⌋). Condition (1) is necessary for infinitely many near-shortest names of length at most m to publish in (tₓ,Tₓ] on any one efficient native prefix machine. Conversely, whenever (1) holds, for any specified positive saving d one can choose a single efficient native interpreter on which infinitely many words y have K(y)=K_Tₓ(y)=m−d<K_tₓ(y), for all sufficiently large fixed a. This converse is unconditional. Linear SAT would give bounded-offset crossings on every specified interpreter as described below.

## Extracting a timely header from a single actual name

Fix a native interpreter V and write K for its unbounded complexity. Let an exact name p of length at most 2m output y of length m at time τ∈(tₓ,Tₓ], with |p|≤K(y)+H. Put r=⌊log₂m⌋ and h=r−⌈log₂(r+1)⌉. At large m one has h2ʰ≤m≤8h2ʰ. Compute the index j₀ of the depth-h cell suggested by the integer lower estimate ⌊log₂τ⌋: take ⌊(⌊log₂τ⌋−3m)2ʰ/m⌋ clipped to [0,2ʰ−1]. The index of ω↾h is j₀+i for some signed integer |i|≤a+4 at all sufficiently large m. Indeed the logarithmic time uncertainty is at most a log₂m+2 and 2ʰ/m≤1/(r+1). The extra endpoint digit also fits this bound.

Use one prefix code E(i) for signed offsets with |E(i)|≤log₂(|i|+2)+2log₂log₂(|i|+3)+O(1). For a given σ of length h, form the finite class of pairs (i,p) producing cell σ by this rule, with |p|≤2m, the stated relation between m and h, and τ≤2^(4m). Its mass A(σ)=Σ2^(−|E(i)|−|p|) is computable by a finite enumeration of programs of length at most 16h2ʰ, simulating through 2^(32h2ʰ) native steps. A fixed ordinary prefix compiler taking E(i),p can output σ on each such input. Direct simulation of logarithmic-word random access on a multitape machine has polynomial overhead in the native time, even using a sequential scan per memory access. Hence for some fixed B independent of a,H, W_B(σ)≥c_V A(σ) at all sufficiently large h.

Normalize the finite pair weights by their sum A(σ)>0. Given σ, a uniform conditional prefix decoder describes any such pair with at most ⌈|p|+|E(i)|+log₂A(σ)⌉ bits using its normalized weight as a Shannon code-length bound. The normalized weights are computable rationals and the integer lengths meet Kraft's inequality. It can then recover y. Consequently the near-optimality inequality gives

    W_B(ω↾h) ≥ c'ᵥ 2^(−H−|E(i)|) 2^(−K₀(ω↾h)).                       (2)

Unbounded witness lengths yield unbounded h, proving necessity. This also applies when the near-shortest timely name does not improve on any earlier name. The factor for the candidate cell is at worst of order (a+1)(log(a+2))² in the reciprocal bound.

## Two sufficient constructions at this scale

For fixed B choose an integer s with 2^(s−1)>4B. Set m=2^(h+⌊log₂h⌋+s)+val(σ), where val allows leading zeroes. At fixed s, m determines h and σ. It is between 2^(s−1)h2ʰ and 2^(s+1)h2ʰ. The rate-cell width changes the deadline exponent by at most m2^(−h)≤2^(s+1)h. A polynomial denominator of sufficiently large fixed exponent absorbs this error.

For the unconditional construction put an existing native interpreter behind a fixed long generic prefix. On the separate 0 branch read any P-name p contributing to W_B(σ), with σ obtained by running p, and compute this m. Consume m−d−1−|p| raw suffix bits. Output d zeroes followed by the entire consumed name. Thus this branch is injective at each length. Delay publication to a fixed positive fraction below 2^⌊vm⌋, where v=3+.σ. On contributing names setup time is at most 2^(Bh2ʰ)poly(m), which fits well below the delay. Eventual publication is in (tₓ,Tₓ] for every x represented by the prefix and every sufficiently large fixed a. Use the [constant-factor native delay](programmable-clock-spectrum.md). The decoder checks the length/time cutoffs before publishing, and the fixed generic prefix provides an efficient literal compiler.

The exceptional cohort at m has actual total name weight W_B(σ)/2. The underlying generic interpreter's total program weight at m is ≤C2^(−K₀(σ)), since its length distribution is a semimeasure and m identifies σ. Make the generic prefix long enough that on each prefix from (1) its total mass at m is at most W_B(σ)/4. Then at least half the cohort has no other name of length at most m−d at any time. This gives the claimed shortest-name crossings. For given B,δ,d the construction works simultaneously for all rates meeting these parameters.

Under linear SAT the [missing-word decoder](rate-prefix-depth.md) works on a previously specified efficient native V. Hard-code a fixed D and assign disjoint rank blocks to all contributing headers for σ. The enumeration for their exact ranks costs at most 2^(2Bh2ʰ)poly(m). The available name length m−D pays each contributing header and the fixed decoder. The SAT-based earlier-table count fits at the center clock. Choose a large enough to absorb the cell-width error above. On the subsequence in (1) the allocated words have scaled mass ≥c_{V,D,B}δ2^(−K₀(σ)) and the words with K(y)≤m−D−H have scaled mass ≤C_B2^(−H−K₀(σ)). Some fixed H suffices, and a single exact saving in {D+1,…,D+H−1} recurs infinitely often. This statement permits its width to depend on D.

## The unfiltered increment sum on every interpreter

For computable x there is an unconditional three-way equivalence. Condition (1) holds if and only if the unfiltered increment sum

    Σ_y (2^(−K_Tₓ(y))−2^(−K_tₓ(y)))

is Martin-Löf random on some efficient native V for some fixed a, if and only if it is random on every fixed efficient native V for all sufficiently large a. In particular every computable stream in the full-dimensional class below gives a nonrandom unfiltered sum, and nonrandom sums in every exact-saving column, for each V and each fixed a. One concrete computable member is obtained by filling all its free positions with zeroes.

For necessity the summands are computable, by finite simulation for each word's clocks, and sum to at most one. The computable-series term criterion yields infinitely many positive terms at least a constant times 2^(−K(y)) when the sum is random. A shortest name by Tₓ for each such word must be within a constant of K(y) and must finish in (tₓ,Tₓ]. A fast literal decoder using the output bits and a self-delimiting length ensures K_tₓ(y)≤m+O(log m)≤2m at large lengths. Thus (2) applies. A fixed computable rate has computable integer deadline exponents: use rational arithmetic for rational x, and refine its approximation until the floor is determined in the irrational case. Zero summands can be handled by adding a computable geometrically decreasing positive sequence with negligible term ratios and rational total. [Bienvenu and Shen, Theorem 13](https://arxiv.org/pdf/1110.5028)

For sufficiency first convert W_B into fast individual prefix names. The sum of W_B over all strings is at most one since a program prints a single string. In length-lexicographic order put each positive W_B(σ) on a consecutive half-open subinterval of [0,1). Inside it choose a dyadic cell of depth at most ⌈−log₂W_B(σ)⌉+1. Such cells provide prefix-free names. Through level h one can compute every endpoint exactly in time 2^(C'h2ʰ) for fixed C' depending on B, by bounded simulations and dyadic arithmetic. A stream decoder compares earlier candidate codes bit by bit and stops at its assigned cell. On a valid name an incompatible candidate differs before the end of that name. Thus on the prefixes in (1) the decoder prints σ on a name of length at most K₀(σ)+O_δ(1) within 2^(C'h2ʰ).

At an arbitrary efficient native V choose the same injective output length m as above with s large enough for C'. From this prefix name compute σ, m and v=3+.σ. Put L=h+3⌈log₂(h+2)⌉. Simulate every V-name of length at most L through t'=⌊Tᵥ(m)/mᴬ⌋ and output the first missing m-bit word y. At most 2^(L+1)≤m·poly(log m) such names require simulation, so finding the first missing word fits by Tᵥ for a fixed large A. The first 2^(L+1)+1 candidate words suffice. For a large enough relative to A and 2ˢ, tₓ≤t' throughout the cell. We now have

    K_tₓ(y)>L,    K_Tₓ(y)≤K₀(σ)+O(1),    K(y)≥K₀(σ)−O(1).

The last inequality uses recovery of σ from |y|. The bound K₀(σ)≤h+log₂h+2log₂log₂(h+2)+O(1) ensures K_Tₓ(y)<L eventually. Consequently the unfiltered terms are tight infinitely often and the sum is random. The witnesses produced by this argument use very short names relative to m. The proof gives no corresponding conclusion in a fixed near-literal column on that V. Prior work establishes randomness results for the individual time-bounded weight sums; this equivalence concerns their difference. [Hölzl, Kräling and Merkle](https://hoelzl.fr/Hoelzl%2C%20Kraeling%2C%20Merkle%20-%20Time-bounded%20Kolmogorov%20complexity%20and%20Solovay%20functions%20%28Journal%20version%29.pdf)

## A finite test specific to the given native interpreter

There is a sharper characterization for a two-sided polynomial window on a *particular* V. Fix D and for each m-bit y find the first time τ of a name shorter than m−D, checking up to 2^(5m). Keep only the words with 2^(2m)<τ≤2^(5m). Give each kept word label s=(h,j), with h as in the extraction proof and j=⌊2ʰ⌊log₂τ⌋/m⌋. Every label has an effectively enumerable finite fiber, with a computable stopping bound. Define A_V(s)=Σ_{y→s}2^(D−m). Its entries are computable, and their total is at most one by the existence of a short name for each included word. For every nonempty fiber,

    min_{y→s} (m−D−K(y)) = −log₂ A_V(s) − K₀(s) + O_{D,V}(1).          (3)

Indeed the normalized weights 2^(D−m)/A_V(s) code y given s and give the lower bound on the minimum. For the upper bound, the forward map gives Σ_{y→s}2^(−K(y))≤C 2^(−K₀(s)). If all deficiencies in the fiber are at least e, the left side is at least 2ᵉA_V(s). These two calculations yield (3).

Consequently at this V there are unbounded near-shortest first arrivals at times between 2^(xm)/mᵃ and 2^(xm)mᵃ for **some fixed** a and optimality slack if and only if, for infinitely many h, some j within constant distance of 2ʰx has A_V(h,j) at least a fixed fraction of 2^(−K₀(h,j)). Here near-shortest means K(y)>m−D−H for a fixed H. The equivalence uses m/2ʰ=Θ(log m) and (3). For the original one-sided outer clock this label condition is necessary; it is sufficient if the occupied labels also satisfy j+2≤2ʰx, which ensures the first arrival is already below Tₓ. Thus an unconditional route to a SAT lower bound would be to find a thick rate allowed by (1) and a particular V with negligible actual first-arrival mass in the requisite neighboring labels, for all candidate slacks at an appropriate cutoff. The word masses A_V and the generic header masses W_B describe different computations.

## A full-dimensional set of genuine exceptions

For h≥1 let k=⌊√h⌋ and project an h-bit word to its bits in positions 1,4,…,k², numbering bits from one. For every integer 1≤B≤⌈log₂(h+2)⌉ compute the finite projected weights

    U_{B,h}(v)=Σ_{|σ|=h, projection(σ)=v} W_B(σ),    |v|=k.

Each sum over v is at most one. Forbid the k-bit words v with U_{B,h}(v)>2^(−⌊k/2⌋) for any of these B. Their union has fair-coin measure at most ⌈log₂(h+2)⌉ 2^(−⌈k/2⌉). These bounds are effectively summable in h: grouping the 2k+1 indices with ⌊√h⌋=k leaves a polynomial times 2^(−k/2). Start sufficiently late so the total is less than 1/4. The closed set avoiding these finitely testable conditions has positive computable measure, with a computable bound for the tails in every cylinder. Obtain a computable member β by successively selecting a child of positive measure, using the computable measures to certify positivity by approximation.

Let F consist of all streams whose square-position bits equal β. This is a decidable perfect tree of paths. Its Hausdorff dimension is one: the probability measure with free bits fair and the specified square bits fixed gives each allowed length-h cylinder mass 2^(−h+⌊√h⌋). For every u<1 this is at most a constant times 2^(−uh), and real intervals of each dyadic size meet at most a bounded number of comparable cylinders. The mass distribution bound gives dimension at least u. The ambient interval bounds it above by one.

For ω∈F, σ=ω↾h, and each fixed B, let Q be the total W_B mass of all h-bit strings with those prescribed square bits. Eventually Q≤2^(−⌊√h/2⌋), up to one fixed factor from integer rounding. Whenever W_B(σ)>0, describe σ given h,B by normalizing this finite computable distribution by Q. The prescribed bits can be computed from h by the fixed β algorithm with unlimited time. As above conditional prefix coding gives

    W_B(σ)/2^(−K₀(σ)) ≤ C_B 2^(K₀(h)) Q → 0,

uniformly on F, since K₀(h)=O(log h). Thus every member fails (1) for every B. By (2), on every fixed efficient native interpreter there are only finitely many near-optimal polynomial-window arrivals of the indicated kind at each such individual rate, without a SAT hypothesis. The binary image of F has the same dimension. Its dyadic endpoints, if needed, may simply be omitted from the dimension statement.

## Why no qualifying law charges these paths

In fact (1) itself holds almost surely under every law of the [cylinder-law theorem](rate-cylinder-laws.md), without assuming linear SAT, with common B and δ. Fix a positive-mass cylinder I and encode it and the law algorithm as z. Take a shortest q for z of length k and a conditional runtime-record p of length n on (z,k). Put h=2ʳ with r encoding the two names and runtimes. The usual record bound gives Σ_{|σ|=h}2^(−K₀(σ))≤C2^(−k−n). At depth h construct the rounded tickets for μ conditional on I by computing all 2^(h−depth(I)) child masses. This uses absolute precision h+O_{μ,I}(1). Under log₂(F(j)+2)=o(j2ʲ) for the law algorithm the entire bounded calculation takes 2^o(h2ʰ) steps, including all the child queries.

A fixed ordinary prefix decoder reads q,p and one fixed-length ticket, then prints its h-bit cell σ. The rounded ticket fraction rσ is ≤μ([σ]|I), with Σrσ≥29/32. Thus at B=1 and sufficiently late records W₁(σ)≥c2^(−k−n)rσ. The total ticket fraction of cells with W₁(σ)<δ2^(−K₀(σ)) is ≤δC/c by the record bound. Choose δ once to make this at most 1/8. The good cells therefore carry a fixed positive fraction of μ conditional on every I at arbitrarily late levels. The limsup and cylinder monotone-class argument gives μ-measure one for sequences meeting (1). This explains unconditionally why no qualifying law can assign positive measure to the actual exceptions in F. In particular the singular measure used in the dimension calculation cannot supply the SAT contradiction.
