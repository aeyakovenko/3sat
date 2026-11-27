# Predicting one bit about exceptional lengths

**Research journal, 24 November 2026.** A sound upper bound on the number of exceptional lengths in a block would suffice to rule out linear SAT. I tested how much less information could suffice. A verifier can make false claims, abstain on almost every block, and make the same one-bit prediction whenever it speaks. For a particular bit, a positive lower limit on its accuracy among the blocks it accepts would suffice. The finite blocks involved here belong to the prefix-free auxiliary machine. All SAT hypotheses below use the ordinary explicit encoding and unrestricted workspace. [Definition of the source and the earlier block criterion](prefix-lengths.md)

## The mass at the rth accepted block

Write N=2^j. A length m in [N,2N) is heavy when every m-bit word beginning with j zeroes is printed by some program shorter than m by B(m)=2^(20m). Let e_j be the fraction of heavy lengths in that block. The prefix-free machine U has no external length input. Its outputs at distinct lengths come from disjoint sets of programs, giving Σ_j e_j≤1/2.

Consider a uniform procedure that scans blocks in order and accepts infinitely many of them. Write j_r for the block index at its rth acceptance, starting with r=1. Computing the list through any block j must fit 2^(αN) poly(N) auxiliary RAM time for some fixed α<5. The auxiliary computation uses O(log(time+2))-bit words, with the usual fixed constant factors. This is a budget on the whole scan, including any state carried between blocks. A deterministic multitape scan with bound 2^(αN) poly(N) and α<10 also works. In the RAM case the sequential memory simulation and the universal interpreter each cost at most a squaring up to polylogarithmic factors. In the tape case only the interpreter is needed. This leaves enough time for the final program below to halt within B(m).

There is a constant c>0, depending on this procedure, for which all sufficiently large r satisfy

    e_{j_r} ≥ c / [r (log₂(2r))²].                                    (1)

Let l(r) be the length of the prefix code consisting of the gamma code of the bit length of r followed by its low bits. Thus l(r)=log₂ r+2 log₂ log₂(2r)+O(1). One fixed decoder reads that code and gamma(d), sets k=l(r)+d, then finds j=j_r by the scan. Eventually j≥k+1 because j_r≥r. If e_j≤2^(−k), at most 2^(j−k) lengths in the block are heavy. Among the first 2^(j−k)+1 positions, at least one m has a missing word beginning with j zeroes. Read j−k+1 bits for its offset, rejecting out-of-range choices, and m−j bits to print such a word. An appropriate suffix prints the actual missing word. The complete input has length m−d+1+|gamma(d)|+a, where a is a fixed compiler length. Fix d so this is less than m. The resulting contradiction proves (1). The earlier bound on the total mass still applies to every sublist of these blocks.

## Alternating ranges of the exceptional fraction

For e_j>0 define t_j=⌊log₂(1/e_j)⌋ and let the bit χ(j) be ⌊log₂ t_j⌋ modulo 2. The global bound gives t_j≥1. Assign χ(j)=0 when e_j=0. Equation (1) applied to the list of all blocks shows that there are only finitely many such exceptions.

Take b=2^s and Q_s=2^(3b/2) with s≥1. For *every* infinite scan within the stated time, among its first Q_s accepted blocks, the proportion with χ(j)=s modulo 2 is at least

    1 − O(2^(−b/2)).                                                   (2)

For r≤Q_s after the fixed starting threshold in (1), we have e_{j_r}>2^(−2b) for all large s. Indeed Q_s(log₂(2Q_s))² is only 2^(3b/2) times a polynomial in b. And there are at most 2^(b−1) blocks in the entire sequence with e_j>2^(−b), by summing their masses. Except at those blocks and the fixed finite initial ranks, e_{j_r} lies in (2^(−2b),2^(−b)]. Its integer t_j then belongs to [b,2b), which gives the claimed bit. Division by Q_s proves (2). In particular both bit values have upper relative density one and lower relative density zero on the accepted subsequence.

One consequence is bi-immunity at the stated clocks: neither value of this computable bit contains an infinite set recognizable by such a scan. Equation (2) gives the stronger quantitative conclusion even when false positives occur. The general concept of bi-immune languages is classical. Priority for this particular exceptional-fraction statistic has not been established. [Balcázar and Schöning](https://doi.org/10.1007/BF01699457)

## A one-bit test sufficient for a SAT lower bound

Let F(j) be a uniformly constructed SAT instance. Suppose the size in encoded bits and its RAM construction time are at most 2^(α·2^j) poly(2^j). If linear-time SAT holds and α<5, the satisfiable blocks can be scanned within the first budget above. The cost of the smaller blocks adds only a polynomial factor. Thus (2) holds for their ordered list whenever it is infinite. For ordinary cubic SAT the same implication holds at α<5/3. Fixed alternations in F are also allowed for the linear target by the existing quasilinear elimination. [Eliminating quantifier blocks](linear-quantifiers.md)

Consequently an infinite family of satisfiable F(j) predicting one fixed bit value, with a **strictly positive lower limit** on the fraction correct within its first R satisfiable blocks as R tends to infinity, would exclude the corresponding SAT time. No numerical estimate of e_j and no identification of an individual light length are required. Correctness infinitely often, or even a limsup of accuracy equal to one, is insufficient: the constant prediction already achieves both unconditionally on the list of all blocks.

## Summing rare correct claims over many precisions

A smaller success rate suffices if the ranks to be audited are fixed in advance. For sufficiently large s put b_s=2^s and Q*_s=2^(2b_s−2⌈log₂(s+2)⌉). Let W_s count the blocks among the first Q*_s accepted ones whose bit differs from s modulo 2. Under the same scan budget,

    Σ_s 2^(−b_s) W_s < ∞.                                              (3)

The larger rank cutoff uses a shared description for the precision. Given the prefix code for s, read 2b_s−2⌈log₂(s+2)⌉ raw bits to specify r−1. For j=j_r≥2b_s, if e_j≤2^(−2b_s), another j−2b_s+1 bits specify a light length, and m−j bits can produce its missing word. The complete program length is m+l(s)−2⌈log₂(s+2)⌉+O(1), strictly less than m for all large s. The computation still fits the selected length's clock. For j<2b_s any positive e_j is at least 2^(−j)>2^(−2b_s), because e_j has denominator 2^j. Thus, after disregarding the finite set of zero fractions, every audited rank has t_j<2b_s.

For such a rank to contribute to W_s, it must have t_j<b_s. Fix one accepted block of positive mass. Over all audits to which it can contribute, its total charge is at most the sum of 2^(−b) over **all integers** b≥t_j+1. This is 2^(−t_j)<2e_j. Summing over accepted blocks gives a finite bound independently of the overlaps between the audited prefixes. Finite exceptional precisions and the finitely many zero-mass blocks add only finite weight. This proves (3).

For a verifier predicting c on every accepted block, consider only s with parity opposite to c. At these audits W_s counts *correct* predictions. Divergence of the discounted number of those successes would therefore exclude the hypothesized SAT time. For example it would suffice to have at least 2^(b_s)/s correct predictions at every sufficiently large such audit. The corresponding required accuracy is only of order s·2^(−b_s), tending to zero. We do not know a verifier attaining even this rate on the actual source.

## A cheap predictor with almost perfect logarithmic accuracy

The averaging convention in this proposed test matters. Give the rth prediction weight 1/r instead of one. On every fast infinite accepted list above, an elementary predictor then has limiting accuracy one: for r≥2, predict χ(j_r) from the parity of ⌊log₂ log₂ r⌋. More precisely, for R≥3 the **unnormalized** harmonic weight of its errors through R is O((log log(3R))²).

To verify the estimate, consider a rank band with b=2^s and b≤log₂ r<2b. Actual values with t_{j_r}<b have e_{j_r}>2^(−b), so at most 2^(b−1) ranks lie in this exception, each with harmonic weight at most 2^(−b). Values with t_{j_r}≥2b satisfy log₂ r≥2b−O(log(b+2)) by (1). The harmonic sum over this last strip is O(log(b+2)), by comparison with the integral of 1/x. At all other ranks in the band, predictor and actual bit agree. Summing over the O(log log(3R)) bands intersecting [2,R] proves the error estimate even when the last band is incomplete. Dividing by total weight of order log R proves the accuracy statement.

In particular, either *constant* bit prediction has harmonic lower accuracy 1/3 and upper accuracy 2/3 on such a list. On the variable x=log₂ r the consecutive bands have lengths 1,2,4,8,…. By summing the even and odd geometric series the share at the successive right endpoints alternates in the limit between 1/3 and 2/3. Within each band the share varies monotonically for that predictor. Integral comparison gives the same limits for the harmonic rank weights. The proven error estimate allows replacement of the rank-based bit by χ. Thus changing “positive lower limit” in the SAT criterion to logarithmically weighted accuracy would produce a false criterion.

The accumulated O((log log R)²) error estimate is sharp if one only knows summability and (1). Take an abstract summable profile u_r=λ/[r(log₂(2r))²] with fixed small λ>0 making its total at most 1/2. In the terminal strip 2b−log₂ b≤log₂ r<2b of each sufficiently large band, ⌊−log₂ u_r⌋ lies between 2b and 4b−1. The bits then disagree on harmonic weight of order log b in that band. This example tests the estimate from the two inequalities. The actual profile for U need not attain that error.

## Testing early simulation as a predictor

Run the same definition of heaviness with only 2^(3m) simulation steps. Call the bit obtained from these earlier fractions χ_early. The lower bound (1) for the unfiltered list of all blocks still holds for this earlier source: computing j=r directly and handling the raw suffix cost only poly(m), below the shorter clock. The early fractions have total mass at most 1/2 by the same Kraft argument. Applying the elementary argument of (2) to those fractions on the unfiltered list shows that χ_early takes both values infinitely often.

Both sets of early predictions can be scanned unconditionally within the *full* source's clock. On tapes, run every input shorter than m on the fixed machine for 2^(3m) steps or until it halts or requests an unavailable bit. Retain outputs of the required length and form, sort, and remove repeats to count the covered words. Copies of the same program with unconsumed suffixes have no effect after deduplication. Each simulation can use the fixed U's own tapes with a simulation clock, and clearing them costs at most the time allotted. For a block [N,2N), the entire computation takes at most 2^(8N) poly(N) tape steps, including earlier blocks. The native simulation's square remains below 2^(20m) at any selected length m≥N.

Apply (2) to each infinite set where χ_early takes a specified value. **Within each of these sets, agreement with the full simulation has lower density zero and upper density one.** Thus using an exact truncated count, even with exponential time per program, fails the accuracy condition just proposed. Monotonicity of the fractions with the clock does not guarantee monotonicity of the bit.

## Attempt to extract a proof for one block

There are explicit finite disjunctions for which a single short group argument proves the desired bit at *many* of the listed scales. For s large, set b=2^s and take the 2^b consecutive indices from J=2^(3b) through J+2^b−1. For each j in this window, a decoder can recover j from the prefix code of s and b raw offset bits. If e_j≤2^(−2b), the earlier missing-word decoder needs only j−2b+1 extra bits to select a light length and m−j to print its missing word. Total length is m−b+l(s)+O(1)<m. Here recovering j from the offset and handling the raw input cost only poly(m) time. Therefore every scale in the window has e_j>2^(−2b). At most 2^(b−1) can have e_j>2^(−b). At least half the scales in this particular window have χ(j)=s modulo 2.

Thus for either fixed parity one can check a group certificate by verifying the listed interval and applying this uniform theorem. I tried to turn the certificate into short proofs for individual instances. Fix *any* sound proof checker for claims χ(j)=c whose running time is polynomial in the binary length of j and the proof length. For all sufficiently large j neither bit value has such a proof of length ≤2^j. Otherwise exhaustive search through those proofs in 2^(2^j) poly(2^j) time per block would give an infinite fast scan with one fixed **correct** bit, contradicting (2). The proof checker and the starting threshold are fixed in this statement. Longer finite computation proofs can still exist.

There is a larger range where SAT can make a difference. If the checker's time is O((|proof|+log₂(j+2)+2)^d), with d≥1, and linear SAT holds, then for any fixed positive rational β with dβ<5 only finitely many individual claims can have a proof of length at most 2^(β·2^j). Guess a padded proof and its actual length, use the checker's RAM computation transcript as the existential SAT test, and apply (2). The encoded transcript and construction cost 2^(dβ·2^j) poly(2^j), including the check of addressed reads. For cubic SAT take dβ<5/3. Extracting a proof of this latter size for **one** correct individual claim in each of infinitely many of the displayed windows, even without an efficient extractor, would exclude the corresponding SAT time.

This tests an extraction idea on arithmetic statements with binary indices and implicit large computations. Expanding an individual computation into a propositional formula changes its size. Applying a disjunction property for explicit propositional formulas would require controlling that expansion as well as the size of the extracted proof. The interval argument by itself supplies neither. [Krajíček on feasible disjunction](https://www.karlin.mff.cuni.cz/~krajicek/brno.pdf)

A candidate next verifier would certify a property of *all* late producers sufficient to keep the exceptional fraction in a selected range. Exhibiting some genuine producers can bound that fraction from below. The adjacent upper endpoint is the missing part of this approach. I have no verifier that predicts this bit with the required lower accuracy. [Lean finite counting and coding checks](../lean/ExceptionalBands.lean)
