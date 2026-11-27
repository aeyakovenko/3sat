# A canonical limit of weighted first-production times

**Research journal, 24 November 2026.** The individual phase measures need not converge. Their averages over the entire remaining tail, weighted by the actual arrivals of halting programs, do converge on a suitable set of phases. This is unconditional. Under linear SAT the limiting measure has an atom at every limit-computable rate in [3,4]. The construction gives it a name computable from the *second* Turing jump. A name computable from the first jump would contradict linear SAT. [Phase measures and atomic lower bounds](phase-limit-measures.md)

## Random mass remains on the selected phases

Use the rounded finite rational measure μᵣ on [0,20] from the linked construction. Its mass is at most two. The rational Iᵣ is the total Kraft weight arriving in phase r and ΣIᵣ=Ω, the random left-c.e. halting probability of the native machine. The rational Pᵣ is the phase's total normalized mask cost, with ΣPᵣ≤3/2. All three are computable after each finite phase. For a nonnegative summable sequence a write Tₐ(R)=Σ_{r>R}aᵣ. Use

    Gₖ = {r : Iᵣ ≥ 2^(−k)Pᵣ and Iᵣ ≥ 1/r²}.

The Barmpalias–Lewis-Pye theorem states that for any two random left-c.e. reals and any computable nondecreasing approximations, the ratio of their remaining tails converges to a positive finite constant depending only on the two reals. For a nonnegative left-c.e. numerator α and random denominator β, apply this to α+β and β and subtract one. The sum is random because its approximation tails dominate those of β, giving a Solovay reduction. In particular T_P(R)/T_I(R) tends to a finite d≥0. For any computable decreasing rational g(R)→0, g(R)/T_I(R)→0: compare the ordinary approximation Ω_R with Ω_R−g(R), two approximations to the same random Ω, whose limiting tail ratio is one. [Barmpalias and Lewis-Pye, Theorem 1.7](https://arxiv.org/abs/1604.00216) · [Miller on the tail-ratio derivation](https://people.math.wisc.edu/~jsmiller8/Papers/derivation.pdf)

Put wᵣ=Iᵣ on Gₖ and zero elsewhere. The omitted tail is at most 2^(−k)T_P(R)+Σ_{r>R}r^(−2)≤2^(−k)T_P(R)+1/R. Choose k fixed and large enough that 2^(−k)d<1/2. Then liminf T_w(R)/T_I(R)≥1−2^(−k)d>1/2. Thus Ω is Solovay reducible to β=Σwᵣ, including the finite initial stages by increasing the comparison constant. The left-c.e. real β is itself Martin-Löf random. This proves more than infinitude of Gₖ, without requiring an effective way to select k. [Characterization of random left-c.e. reals](https://math.berkeley.edu/~slaman/papers/random.pdf)

## A weak limit without a chosen subsequence

For such a k form the mathematical tail averages

    L_R = (Σ_{r>R} wᵣ μᵣ) / T_w(R).

For every nonnegative rational piecewise-linear test f, the numerator total α_f=Σwᵣ∫f dμᵣ is left-c.e., with computable nonnegative rational summands. The tail-ratio theorem shows that ∫f dL_R converges. Rational piecewise-linear functions, together with subtraction of constants, give a countable dense set of continuous tests. The measures L_R have mass at most two on a compact interval, so these limits specify one finite measure Λ and L_R converges weakly to it.

Λ belongs to the closed convex hull of the high-phase cluster measures. For any continuous f, all sufficiently late high phases have integral at most the maximum over their cluster measures plus any prescribed positive tolerance. The same upper bound holds for all sufficiently late tail averages. Linear separation by continuous tests therefore gives the assertion. Each L_R has a name uniformly computable from the halting problem 0′: that oracle computes the left-c.e. totals and the positive remaining mass, or directly supplies a truncation of the positive normalized series at any required mass error. The limit of this convergent sequence has a name computable in 0″. This argument supplies no 0′-computable convergence rate or 0′-computable name for Λ itself.

Under linear deterministic time for explicit SAT, for every limit-computable x∈[3,4], a single native decoder forces all sufficiently late r∈Gₖ to put some fixed mass cₓ>0 in intervals shrinking to x. For any fixed closed neighborhood of x that mass persists in all sufficiently late averages L_R. By weak convergence and continuity from above, Λ({x})≥cₓ. A 0′-computable finite measure admits a 0′-computable nonatom in (3,4), so Λ would have no 0′-computable name under this hypothesis. An unconditional construction of a 0′-computable name for this particular Λ would therefore exclude linear SAT. [Decoder and nonatom construction](phase-limit-measures.md)

## Sharpness for computable bounded observations

Fix the same computable increments wₛ and their random sum β. There exists a computable rational observation hₛ∈[0,1] whose normalized tail average has Turing degree exactly 0″. Thus timing the observations against the specified phase arrivals and bounding every observation still allows the full second jump. The example assigns auxiliary observations to the phases and does not calculate the degree of the native first-production measure.

Write Dα for the tail derivative of a left-c.e. real α with denominator β. It is additive, positively rational homogeneous and nonnegative, by the limit theorem. Let β₀=0 and βₛ be the cumulative weight through stage s. For a uniform enumeration Wₑ of the c.e. sets, the nondecreasing approximation γₑ,ₛ=β_{|Wₑ,ₛ|} defines a uniformly left-c.e. family with 0≤γₑ≤β. If Wₑ is infinite, γₑ=β and Dγₑ=1. If Wₑ is finite, γₑ is rational and Dγₑ=0. These identities use the independence of D from the approximation. [Barmpalias and Lewis-Pye](https://arxiv.org/abs/1604.00216)

Set α=Σₑ4^(−e−1)γₑ, Γ=Σₑ2^(−e−1)γₑ and Eₘ=Σ_{e≥m}4^(−e−1)γₑ. For each m, the difference 2^(−m)Γ−Eₘ has a computable nonnegative-coefficient series, so it is left-c.e. and 0≤DEₘ≤2^(−m)DΓ. Finite additivity now yields

    Dα = Σ_{e : Wₑ infinite} 4^(−e−1).

The e-th base-four digit is 0 or 1. After a known prefix, the possible values for the two choices are separated by at least two thirds of the current digit weight. A Cauchy name therefore computes the infinitude set recursively, and that set computes a Cauchy name from the geometric tail bound. Infinitude of c.e. sets is Π⁰₂-complete and has degree 0″. For a predicate ∀i ∃t R(e,i,t) with computable R, enumerate one new element whenever witnesses have been found for another consecutive initial segment of requirements. The resulting set is infinite exactly when the predicate holds. In particular a single scalar derivative can attain the upper degree. Miller's Proposition 2.6 realizes each positive Δ⁰₂ real as a derivative. This coding addresses the degree bound and leaves the classification of the full range open here. [Miller, Question 2.7](https://people.math.wisc.edu/~jsmiller8/Papers/derivation.pdf)

To impose the observation bound at *each* prescribed phase, fix a computable increasing approximation αₛ starting at zero. The synchronized tail comparison supplies an integer C≥1 such that α−αₛ≤C(β−βₛ) at every stage. Feed the successive increments of αₛ into a queue. At stage s, after its arrival, release the smaller of the outstanding amount and Cwₛ. The backlog Bₛ is the maximum of zero and all suffix sums of arrivals minus capacities through s. For a suffix starting just after i≤s that sum is

    (α−αᵢ) − C(β−βᵢ) − (α−αₛ) + C(β−βₛ) ≤ C(β−βₛ).

Hence Bₛ→0 and the released amounts sum to α. Define hₛ as the amount released divided by Cwₛ, with hₛ=0 when wₛ=0. This sequence is computable for the fixed integer C, lies in [0,1], and Σwₛhₛ=α/C. Its tail derivative is Dα/C, of degree 0″. The existence proof allows C to depend on the fixed two approximations. The queue invariant for finite data on a common integer grid was checked in Lean 4.19. [Lean proof](../lean/TailCapacity.lean) · [Kučera–Slaman comparison, as stated in Miller's Lemma 1.1](https://people.math.wisc.edu/~jsmiller8/Papers/derivation.pdf)

## Endpoints chosen from the computation itself

An adaptive forward lookahead can read as many completed native phase tables or bounded halting comparisons as it wants before reporting an endpoint F(R)≥R. If this procedure always terminates, F is total computable even when its runtime has no specified bound. Then

    (Σ_{R<r≤F(R)}wᵣ) / T_w(R) → 0.

For nonmonotone F, take the computable nondecreasing majorant H(R)=max(R,F(1),…,F(R)). The approximations β_R and β_{H(R)} to the same random β have limiting tail ratio one. Their difference bounds the weight captured by F. The statement applies as well to a uniformly finite decidable menu of sound positive thresholds for actual later increments, even if certificates omit the future endpoints. Compute the menu by exhaustive search. For each certified threshold wait until its promised finite witnessing increase occurs, then take the latest endpoint, defaulting to R for an empty menu. Soundness and finite witnessability make this a total computable lookahead. The same holds if certificates use bounded Boolean quantifiers.

There is a bound even for partially defined comparisons. Suppose that completed reports (u,v) are computably enumerable, with v>u, and their observed increments Δ=β_v−β_u have finite sum over all reports. For every fixed rational δ>0 only finitely many reports can have Δ≥δT_w(u). Each such report covers β by an effectively supplied open interval about β_v of radius 2Δ/δ, omitting zero increments. Their total length is finite. A Martin-Löf random real lies in only finitely many intervals of a Solovay test. Bounded overlap of the phase intervals is sufficient for the summability premise. [Solovay tests for randomness](https://arxiv.org/abs/1110.5028)

If one allows unrestricted overlapping possibilities without identifying the successful comparison, there is a simple source of misleading successes. At each u monitor all dyadic thresholds 2^(−j). Some threshold lies between T_w(u)/4 and T_w(u)/2 and hence is eventually reached. Its end captures at least a quarter of the true tail. Other comparisons never finish, and the monitoring does not identify a threshold in that interval. I found no way to transfer this anonymous success into timely control of a positive share of the native arrivals. The tail-ratio limit proves convergence of the mathematical averages, while estimation of their remaining masses at an eligible clock stays open.
