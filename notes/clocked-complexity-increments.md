# A first-time criterion without feedback masks in its statement

**Research journal, 24 November 2026.** The geometric charge across allowed program lengths has an exact interpretation in terms of the ordinary time-bounded prefix complexity of a word. It produces a test involving only an explicit series on binary words. Dropping its length restriction makes the proposed test fail unconditionally.

Fix the native optimal prefix machine V, put T(m)=2^(3m), and put t(m)=max(1,⌊T(m)/m^a⌋) for a positive integer a and m≥1. Write K_t(y) and K_T(y) for the shortest exact V names finishing by these clocks, taking infinity if none does. Define

    Δ_a(y) = 2^(−K_T(y)) − 2^(−K_t(y)),       2^(−∞)=0.

This nonnegative number is computable: a bounded run can read only boundedly many program bits. Enumerating all those inputs is allowed for this computability statement. Its sum over y is at most one by Kraft, choosing one timely name per distinct word. If the earliest producer of y with length <m−D finishes in (t(m),T(m)], its saving index satisfies

    m−K_t(y) ≤ D ≤ m−K_T(y)−1.

Conversely those inequalities imply the first-time condition. Summing 2^(D−m) over *all integer* D in this interval gives exactly Δ_a(y), also when the lower endpoint is unbounded. Summing only over D≥1 or imposing feedback restrictions gives at most Δ_a(y). Thus the joint charge is paid by an actual improvement in the best available description length at these clocks.

## Near-incompressible words

For m≥4 set L(m)=⌈log₂ log₂ m⌉, computable exactly by comparing powers. Restrict the sum to words in the indicated length band:

    E_a = Σ_{y : m−L(m) ≤ K_T(y) < m} Δ_a(y),     m=|y|≥4.             (1)

**Under linear deterministic SAT on the unrestricted logarithmic-word RAM, E_a is a Martin-Löf random left-c.e. real for every sufficiently large fixed a.** The same holds if the upper bound K_T(y)<m is strengthened to K_T(y)<m−c for any fixed integer c. Thus it would suffice to prove nonrandomness, in particular computability, of the sum (1) for arbitrarily large a. The series itself has no reference to the auxiliary block masks. Hölzl, Kräling and Merkle proved randomness results for the individual sums of time-bounded complexity weights under their universal-machine conventions. Subtracting the two clocks and restricting by timely description length are essential to the question here. [Time-bounded Kolmogorov complexity and Solovay functions](https://hoelzl.fr/Hoelzl%2C%20Kraeling%2C%20Merkle%20-%20Time-bounded%20Kolmogorov%20complexity%20and%20Solovay%20functions%20%28Journal%20version%29.pdf)

To prove this, use the [varying-savings construction](varying-description-savings.md) with D=⌊r/3⌋ and the earlier cutoff t(m). On infinitely many phases there are paid words meeting the clock test with m−D−h<K(y)≤K_T(y)<m−D for a fixed h, and K_t(y)≥m−D. The native clock calculation holds for every sufficiently large a. For their lengths m one has L(m)≥D+h eventually: even log₂log₂ m is at least log₂ J_s in window s, and r≤s+3. Thus they satisfy the indicator in (1), eventually including any fixed extra saving c. They also have K_T(y)≤K(y)+h and K_t(y)≥K_T(y)+1. Each contributes at least 2^(−h−1)2^(−K(y)). Because the phases use different D, their selected lengths need not be disjoint across phases; the smallest length in any window of phase r nevertheless tends to infinity with r. The conclusion applies to infinitely many distinct words.

Index the computable terms by a computable bijection from integers to binary words. The universal discrete semimeasure at that index is comparable to 2^(−K(y)) by the coding theorem. The term criterion for sums of computable convergent rational series now gives randomness. One may add a computable, rapidly decaying positive series to treat zero terms. Its summands are little-o of the universal semimeasure, so the existence of the tight subsequence is unaffected. [Bienvenu and Shen, Theorem 13](https://arxiv.org/pdf/1110.5028)

## Even a single exact length saving can carry a random sum

There is a stronger conclusion than the growing band in (1). Define E_{a,d} by summing Δ_a only where K_T(y)=m−d. If linear SAT holds, there are constants a₀ and C such that for each fixed sufficiently large D, some integer

    D+1 ≤ d ≤ D+C log₂(D+2)

has E_{a,d} random for every a≥a₀. In particular, a gap of nonrandom exact-saving sums cannot be arbitrarily large relative to log(D+2) following D at any such a. This conclusion also shows that in (1) any computable bandwidth tending to infinity, however slowly, suffices.

Use the selector with constant value D in the varying-savings proof. One uniform decoder reads a self-delimiting parameter D of length ℓ(D)=O(log(D+2)). Relative to w_r, its scaled grant loses just 2^(−ℓ(D)−c) for a common constant c, by reducing the raw cell depth by ℓ(D). The additional runtime for each fixed D is absorbed at large phases, with one fixed quantifier-elimination exponent and a common sufficiently large a₀. In the simultaneous bound (2) of that proof, take h a sufficiently large constant multiple of log₂(D+2). Then (h+1)²2^(−h) is small enough compared with 2^(−ℓ(D)−c) on the common tight phases. At all sufficiently late phases of that set there exist qualifying words with D+1≤m−K_T(y)<D+h, K_T(y)≤K(y)+h and a strict change from the early clock. These are finitely many possible integer savings for this fixed D. At least one saving occurs at unbounded lengths. The term test on that exact saving gives randomness for a₀. Increasing a leaves K_T fixed and only increases Δ_a, preserving the tight terms. The proof gives no way to identify which exact d occurs.

## Direct attack on the version without a length band

The unfiltered sum Σ_y Δ_a(y) is already random **without** a SAT hypothesis for every sufficiently large a. To see this, use the paired halting phase indices r=r(p,t_p) from the [common grant construction](one-bit-production.md). Infinitely many of them have |p|≤K(r)+O(1) by the term test and coding theorem. A fixed decoder can recover r from p in poly(r) time, counting its simulation steps. Now take m=2^r. Simulate all programs of length ≤r up to t(m) and choose the first m-bit word y that none of them has produced by that time. Fewer than 2m such programs exist. One can track just the first 2m distinct possible m-bit output values to find a missing one. At large m the complete construction and interpretation take at most m·t(m)·poly(m) native steps, which fits T(m) for sufficiently large fixed a. The polynomial exponent can be chosen independently of a by using uniform clock arithmetic.

Here K_t(y)>r, while K_T(y)≤|p|+O_a(1)≤K(r)+O_a(1)<r for large r. From the length of y one recovers r, so K(y)≥K(r)−O(1). Hence these unfiltered summands also meet the tightness criterion independently of SAT. Their timely programs have length O(log r), far outside the length band in (1).

Appending unrelated data to these hard words does not settle the filtered test. To use the same enumeration proof after increasing the required description length to m−O(log log m), its straightforward loop would need to consider exponentially many earlier names instead of fewer than 2m. The available clock ratio is only polynomial in m. No nonrandomness proof or unconditional randomness proof for the filtered sum is established here. [Known one-bit changes in description time](https://arxiv.org/abs/1310.6976) · [Finite geometric bounds in Lean](../lean/OneBitProduction.lean)
