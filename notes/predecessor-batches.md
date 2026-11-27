# Joint proofs for intervals preceding the first missing output

**Research journal, 2026-11-24.** Let w be the lexicographically first d-bit string omitted by the universal machine U on all descriptions shorter than d within B=2^(20n) steps, for d=n or d=2(n−1). Supply n as a separate input. Every predecessor of w has a short description within B. We ask whether one proof can certify a batch of these predecessors without individually replaying their computations. For the actual w, almost-complete batch coverage of even *one* unknown trailing interval would suffice to exclude cubic SAT. There is an unconditional obstruction when the batch proofs themselves have short, quickly decodable descriptions. [Source and replay bound](address-diagonal.md)

## Ranking the missing positions simultaneously at every scale

Put M=2ᵈ. For any subset S of the positions 0,…,M−1, enumerate the positions outside S as h₁<⋯<hᵣ and set h₀=−1. Score each omitted position by

    Dⱼ = max_{1≤i≤j} (hⱼ−hᵢ₋₁)/(j−i+1).

For every real t>0, at most M/t omitted positions score at least t. Take the rightmost such j, select a witnessing gap-index interval [i,j], then repeat at the rightmost qualifying index strictly before i. These intervals are disjoint, and they cover every qualifying index. On each selected interval the sum of its gaps hₖ−hₖ₋₁ is at least t times its number of indices. Their combined gap sum is at most M. The constant one is exact when t is an integer dividing M and the omissions lie at t−1,2t−1,…,M−1. This finite packing estimate is the discrete one-sided weak maximal inequality on the sequence of gap lengths. [Ephremidze, Fujii and Terasawa](https://doi.org/10.1155/2007/746031) · [Lean proof of the finite weak inequality](../lean/GapMaximal.lean)

Sort omitted positions by decreasing score, breaking ties by position. The one-based rank R of hⱼ is at most M/Dⱼ. A fixed decoder for S can print hⱼ from the binary representation of R−1 in ⌈log₂ R⌉ bits, taking zero bits for R=1. The raw rank goes at the end, so there is no scale parameter or rank-length header. Once the membership table of S is available, sequential scans compute all scores in O(M² poly(n)) tape time. Rational comparisons are exact by cross multiplication. Sorting or selecting the indicated rank fits the same bound.

Suppose a fixed decoder can tabulate S and do this postprocessing within B on U. At every such length where w lies outside S, its score is at most a constant C depending just on this decoder. Otherwise its rank payload and decoder prefix would together be shorter than d. Consequently, **simultaneously for every 0≤K≤w**, the preceding interval [w−K,w) contains at least

    (K+1)/C − 1

positions outside S. Indeed, if [w−K,w] contains u omitted positions, its earliest one has a preceding omission strictly before the interval, with h₀ used if necessary. Thus D at w is at least (K+1)/u. The estimate works for a scale chosen after seeing w, even when K varies arbitrarily slowly across lengths.

## Joint proofs that decompress from short seeds

Let a fixed deterministic batch checker receive a proof π and an individual position x. It accepts when π certifies x. For example π could certify the validity of a succinct family of histories, with x tested for membership in their output set. A single π can certify arbitrarily many x. Assume deterministic verification on the expanded proof and the chosen position takes 2ⁿ poly(n) multitape steps. At a tested length require only that no accepted proof cover w. Soundness for the long output image implies this condition.

Allow a fixed decompressor to produce π from n and any raw seed of length at most 6n in 2ⁿ poly(n) deterministic tape time. Take S to contain every x certified by at least one such expanded proof. Also include every d-bit string output and halted by a short description on U within F=2^(2n) steps. The combined set omits w. Exhaust over positions and seeds, decompressing and checking afresh each time. Its cost is at most 2^(d+6n+n+O(log n))≤2^(9n+O(log n)) native tape steps. Tabulate the F-fast outputs separately by simulation and sorting at the established 2^(4n+O(log n)) cost. Computing all scores adds O(2^(2d) poly(n)) steps. Even a quadratic universal simulation fits B eventually.

It follows **unconditionally** that every interval [w−K,w) contains at least (K+1)/C−1 genuine long-output strings that neither have an F-fast short description nor are certified by any of these jointly decompressed proofs. Different predecessors may use different descriptions or batches; repeated use of the same proof is permitted. There is no requirement to replay a long program inside the batch checker. Taking only F-fast outputs gives the same constant-fraction bound at all scales without any proof checker. The lower bound can be vacuous for small K.

## A sufficient condition on a nondeterministic verifier

Now allow arbitrary batch proofs checked nondeterministically within 2ⁿ poly(n) multitape steps, including their effective witness length. For each x the projected predicate says that some accepted batch contains x. The interval endpoints, a particular proof, and a membership witness can all be guessed inside the same clock. If cubic SAT holds on the unrestricted-workspace word RAM, tabulating this predicate independently for every x costs

    2^(d+6n+O(log n)) ≤ 2^(8n+O(log n))

native tape steps using the same quasilinear SAT construction and quadratic RAM-to-tape simulation as for the source. Add the F-fast outputs and rank the omissions as before. The resulting decoder fits B. Thus the constant-fraction obstruction holds even for the union of **all** nondeterministically accepted batches, at each sufficiently large length where their union excludes w.

Conversely, suppose a fixed such verifier has infinitely many lengths where it excludes w and, on some interval of K predecessors, the number missed by both its batches and the F-fast output enumeration is o(K), with K tending to infinity along those lengths. That would refute cubic SAT. A certificate for an entire unbounded trailing interval is the zero-exception case. Neither the interval nor the good lengths have to be found independently, and overlapping batches need no compatible witness assignments. What remains is to construct a fast verifier covering enough of these particular predecessors. The unconditional seed bound shows why uniformly compressing long witnesses into short fast programs does not by itself achieve this coverage.

## Rare flags and public-coin tests near the missing output

A test may instead flag occasional predecessors of w and make unrelated false positives. Let aₙ(x)≥0 be any weights on the M positions and μ their mean. Give endpoint s the score A(s) equal to the largest mean weight on [s−k,s) over 1≤k≤s, with A(0)=0. At most Mμ/t endpoints score at least t>0. Apply the packing argument above to the endpoints s−1 of the witnessing intervals. Selecting the rightmost qualifying endpoint and removing its interval covers all qualifying endpoints with disjoint intervals, each of mass at least t times its length. This gives constant one for arbitrary nonnegative weights. A single positive weight at position zero attains the bound for t equal to that weight. An exhaustive calculation on all 6,561 ternary weight vectors of length eight checked 25,086 distinct positive score thresholds counted across vectors, including 1,602 equalities.

If the weights and scores can be tabulated within the long decoder clock, order every s by decreasing A(s). For μ>0 the rank of w is at most Mμ/A(w) whenever A(w)>0. The rank description gives **A(w)≤Cμ** for a constant depending only on the decoder. For example, under cubic SAT take binary weights from any fixed nondeterministic 2ⁿpoly(n)-time flag predicate on d-bit words. An unbounded ratio of local to global flag density immediately before w would rule out cubic SAT, even if the local density tends to zero and w itself is never flagged. The radius attaining that ratio need not be recognizable.

The public coins of a test may change both the global density and the interval length. For a uniformly random string r, take aᵣ(x) to be one if a witness for (n,x,r) is accepted in 2ⁿpoly(n) time and zero otherwise. Let μᵣ be its global mean, and put Uᵣ(s)=Aᵣ(s)/μᵣ when μᵣ>0, zero otherwise. Write pₜ(s)=Prᵣ[Uᵣ(s)≥t]. Averaging the counting inequality over seeds gives meanₛ pₜ(s)≤1/t. For any fixed uniformly specified threshold t(n)≥1 of polynomial bit length computable in poly(n) time, rank positions by pₜ(s). This gives pₜ(w)≤C/t(n) when the table fits the decoder clock. In particular, the favorable interval may be chosen separately for each seed, after seeing its accepted set.

One fixed bound applies to thresholds selected without an algorithm. Use the rational score

    H(s) = Σ_{j=0}^d 2ʲ p_{2ʲ}(s) / ((j+1)(j+2)).

Its mean is at most one by telescoping. Hence ranking positions by H gives H(w)≤C for a single decoder constant. For every 1≤t≤M, take j=⌊log₂ t⌋. The corresponding summand shows pₜ(w)≤2C(j+1)(j+2)/t. Thus even a public-coin test that finds unbounded enrichment with probability bounded away from zero would exclude cubic SAT. Different witnesses can be used for every flagged position and seed.

For the clock calculation take a uniformly specified seed length e such that d+e≤(4−ε)n for some fixed ε>0. Tabulating all acceptance bits under cubic SAT costs 2^(d+e+6n+O(log n)) native tape steps. Sequential scans take O(2^(e+2d)poly(n)) steps to score all radii for all seeds. Sort the resulting records by position and sum their dyadic level counts there. The common denominator 2ᵉ·Π_{j=0}^d (j+1)(j+2) has polynomial bit length. Sorting and rational comparisons fit the same clocks, and quadratic universal simulation stays below 2^(20n). This permits any fixed seed rate strictly below 2n for the joint source or 3n for the one-mark source. The calculation gives an enrichment criterion for short-coin approximate-counting tests. We have no test meeting it for the actual late arrivals.

## A test may err everywhere after the first missing word

For the same short-coin witnesses, put p(s)=Prᵣ[s∈Aᵣ], and let k(s) be the expected number of accepted positions up to and including s, **conditional on s being accepted**. Fix any positive rational p₀≤1. For every K the set B of positions with p(s)≥p₀ and k(s)≤K has size at most 2K/p₀. Indeed, for each seed with Z accepted members of B, the sum of their accepted-list ranks is at least Z(Z+1)/2. Taking expectations gives

    K Σ_{s∈B} p(s) ≥ Σ_{s∈B} p(s)k(s) ≥ E[Z²]/2 ≥ (Σ_{s∈B} p(s))²/2.

Rank positions with p(s)≥p₀ by increasing k(s). Computing both rational quantities needs just one cumulative count per seed and a sort by position. Under cubic SAT and the stated seed bound, if p(w)≥p₀ then k(w)≥cM eventually, for a decoder-dependent c>0. Thus a verifier would suffice if it accepted w with positive constant probability and on its successful seeds accepted only o(M) preceding words in expectation. Earlier false positives on unsuccessful seeds and all later acceptances can be arbitrary. In the deterministic-coins case, the ordinary rank of w on the accepted list gives the result directly. The predecessors are all printed words by lexicographic minimality. No such selective error guarantee for the long computation has been obtained.

## Coarse counts of printed outputs can hide the first hole

In a finite oracle test, suppose the printed range contains all M positions except one unknown h. A query specifies any subset S and receives an estimate within a factor 1±ε of its number of printed positions, for 0<ε<1. Set K=⌈(1+ε)/(2ε)⌉. When |S|≥K the allowed real intervals for the counts |S| and |S|−1 overlap. Choose a fixed reply in their intersection. For smaller sets reply exactly. With this valid oracle, a randomized procedure making q adaptive queries and returning a list of size at most s hits a uniformly random h with probability at most

    min(1, (q(K−1)+s)/M).

Fix the coins and follow the replies on a hypothetical full range. Its small queried sets contain at most q(K−1) positions altogether. For each h outside their union the same transcript is valid and the fixed reported list contains at most s such holes. Averaging proves the bound. For s≥K−1 it is attained by querying disjoint blocks of size up to K−1, returning a block when it contains h, and using s of the remaining positions when no block does. Adjacent count intervals on these small blocks are disjoint even with arbitrary permitted replies. Counting *omitted* positions to relative error would distinguish zero from one and allow binary search. Also, a verifier given a candidate hole could query its singleton, which grants exactly the range-membership test. The bound concerns constructing a short list using coarse printed-range estimates. It does not lower-bound a verifier that is already given this exact test or a machine that exploits the code of U.
