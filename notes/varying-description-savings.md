# Testing first production times across a growing description-length saving

**Research journal, 24 November 2026.** On one fixed native prefix machine, count words first produced when their programs must be at least D+1 bits shorter than the output. The sum of the word masses, multiplied by 2^D, is finite even when summed over *all* D. Can the contribution at large D therefore be discarded? A common grant program gives a counterexample for broad time intervals. For narrow intervals the same conclusion follows under the linear-SAT hypothesis, giving a new target for an unconditional upper bound.

## A joint upper bound for the actual outputs

Fix the native universal stream machine V and K(y), its shortest program length without a clock. For each integer D≥1 use the wide windows, r=6 start and first h selected lengths of the [one-bit experiment](one-bit-production.md). Run the feedback for D on V using the stricter length condition |name|<m−D and the same deadline 2^(20m). An empty eligible name set causes no difficulty when D is large. Define a length to be heavy and a block to be good using these eligible names. In each run all phases terminate: the sum of the heavy-length fractions is at most 2^(−D−1), since each genuinely covered m-bit word costs at least 2^(D+1) times its normalized weight in Kraft capacity. Each failed mask charges its entire normalized size to this sum. The stage of a given phase can differ between D.

Write A(D,r) for the sum of 2^(−m) over distinct targets at the chosen lengths of **failed** windows in phase r of the D run having an eligible producer by the deadline. It is also permissible to restrict A(D,r) to specified intervals for the first such production times. In either case,

    Σ_r Σ_{D≥1} 2^D A(D,r) ≤ 1.                                      (1)

For a given word y of length m, each D counts it at most once over all r. If it counts at all, then D≤m−K(y)−1. Consequently its entire contribution, summed over D, is at most 2^(−K(y)) by the geometric sum. Sum over y and apply Kraft to shortest names. In particular the computable finite-deadline entries, summed in D, give a lower semicomputable row mass bounded by C a(r), for the universal discrete semimeasure a and a constant C. The schedules for different D need neither agree nor be independent.

A stronger estimate controls distance from the *shortest* program. Let B_h(r) be the same weighted sum over D on row r after restricting to words with K(y)≤m−D−h, h≥1. This row is lower semicomputable, since the phase tables can be computed and short names can be witnessed later. The geometric sum now gives Σ_r B_h(r)≤2^(1−h). Mixing these semimeasures for h with summable weights proportional to (h+1)^(−2) proves **simultaneously** for every r and h that

    B_h(r) ≤ C' (h+1)² 2^(−h) a(r).                                   (2)

## Targeting the saving without putting its value in the program name

Use the separate prefix machine U_0 and weights w_r from the one-bit experiment. Choose the injection r(p,t) with r≥6+3(t+|p|+1). The sequence w is computable, sums to Ω_0, and on the same infinite set R satisfies w_r≥δa(r). Crucially, w_r depends only on r. Fix a uniformly polynomial-time-in-r function g with 1≤g(r)≤r/3 at sufficiently large r, and put D=g(r). Concrete examples are ⌊r/3⌋ and ⌊√r⌋.

A single decoder on V reads a halting U_0 program p following a fixed header and a self-delimiting constant parameter c. It computes r(p,t), then D=g(r) and the appropriate feedback for that D. Allocate word cells in the selected lengths of this one phase until a normalized budget 2^(−D−c) w_r is exhausted. In the cell field of p, a word at length m receives depth m−D−|p|−c. All eligible lengths in the phase greatly exceed D+|p|+c. The name length is

    header + |gamma(c)| + |p| + (m−D−|p|−c) < m−D

for a fixed sufficiently large c. There is no code for D in the header or payload: the halting program already determines the phase, and g reads that phase. The eligibility of the output is therefore preserved even when D grows. For a fixed g, early phases at which its stated bound fails can be skipped.

First request words absent by 2^(3m) under this stricter length cutoff. For a selected length all earlier required names can be simulated, counted and unranked by 2^(4m)poly(m) native steps. Feedback from preceding windows is cheaper, and D=O(r) is negligible at the current length. By the end of the phase the quota must have been exhausted: otherwise every previously missing word of the eventual good block at its h selected lengths would now have an eligible producer by 2^(5m). Their first eligible production times lie in (2^(3m),2^(5m)]. The final successful window accounts for at most 2^(1−r) original word weight. In units scaled by 2^D, the deduction is o(w_r) on **all nonzero phases** as r→∞, because D≤r/3 and |p|≤r/3. Thus the broad-interval mass satisfies

    2^D A(D,r) ≥ 2^(−c−1) w_r,     D=g(r),                            (3)

on every sufficiently late phase with w_r>0, unconditionally. Programs from different phases or experiments do not have to be simultaneously representable by the same selected lengths. The single fixed decoder proves (3) for the selected experiment in each phase.

Under linear deterministic SAT on the unrestricted target RAM, (3) also holds for the first-time interval

    ( ⌊2^(3m)/m^b⌋, 2^(3m) ]

for a sufficiently large fixed b. Count words already produced by the earlier cutoff using a sorted witness list, a universally selected row and one bounded native transcript with the input length checked against m−D. Fixed-block elimination and prefix counts let the grant decoder select the required missing word by the upper deadline. The total overhead is polynomial in m, with fixed exponent, and is paid by choosing b sufficiently large. Any fixed larger b still works. [Native clock verification](near-clock-credits.md)

Combine (2) and (3) on R. For sufficiently large fixed h depending on g and the decoder, at least a constant multiple of w_r in the scaled row comes from words for which

    m−D−h < K(y) ≤ m−D−1.

Thus in the indicated time interval the machine actually produces a word with a description saving a **growing** number of bits and within a **constant** of the shortest possible description. No shorter eligible program finished before that interval. The program need not attain K(y).

## Where an upper bound would separate SAT

On R, divide the sequence D↦2^D A(D,r) by w_r. By (1) its total mass is bounded by a fixed constant. Yet (3) with g(r)=⌊r/3⌋ forces a fixed positive mass to move to arbitrarily large D along every infinite subsequence of R. This is already true for the broad time interval. For the polynomial-factor interval, an unconditional proof of uniform tightness on some infinite subsequence of R for arbitrarily large fixed b would exclude linear SAT. Here tightness means that for any ε>0 a single finite cutoff in D leaves less than ε mass beyond it throughout the subsequence. It would also suffice to show the scaled mass at g(r) can be arbitrarily small relative to w_r on nonzero phases with r arbitrarily large for such b.

Absolute summability in (1) gives no such tightness after division by w_r. For example, putting all of a row's unnormalized weight w_r at ⌊r/3⌋ keeps the global sum finite and moves all normalized weight to infinity. Even domination of many predictors fits a finite budget: take a prefix-coded, effectively clocked family of selectors and place 2^(−|code|)w_r at each timely prediction, adding the weights of coincidences. This numerical example only tests the counting argument. A successful upper bound has to exploit the *times at which* the fixed V produces these words. I found no such bound for its polynomial-factor intervals.

[Geometric allocation in Lean](../lean/OneBitProduction.lean)
