# Exactly one extra CRT parity from a public interval

**Research journal, 2026-11-24.** Suppose the unknown coefficients of a binary polynomial lie in a public interval of length m. Put s = ⌊m/b⌋, where b is the degree of each allowed irreducible modulus. With s fixed-length advice bits, the largest number of independent signed parity claims one can guarantee for **every** such polynomial is exactly s+1. Here s≥2, at least s+1 distinct moduli are available, and the unrestricted table has length N≥(s+1)b. This answers a question left by the cluster construction. [Advised parity claims](advised-claims.md)

## Full rank and rank on the interval

A query is a b-bit linear form applied to the coefficient vector of the remainder modulo one monic irreducible binary polynomial of degree b>1. Independence refers to the linear forms on all N coefficients. On any k distinct moduli of total degree d=kb, d consecutive powers of X realize every tuple of remainders. The Chinese remainder theorem identifies the quotient by the product with the product of the residue fields. Multiplication by the starting power of X is invertible in this quotient, since every modulus has nonzero constant coefficient.

Take h independent query rows. Let r be their binary rank on the interval. The relations on the restricted rows form a binary linear code of dimension h−r. Every nonzero word has weight at least s+1. Indeed, a relation on at most s rows uses at most s moduli, whose entire remainder tuple is attainable inside the interval. Such a relation would hold on the unrestricted table as well.

The Griesmer bound therefore gives

    r ≥ Σ_{j=0}^{h−r−1} ⌊s / 2ʲ⌋.

To see the underlying code argument, project off the support of a minimum-weight word of weight d. The kernel consists of zero and that word. In each other coset the two words disagree at exactly those d deleted coordinates. The lighter of their prefixes on these coordinates has weight at most ⌊d/2⌋. Its surviving part has weight at least ⌈d/2⌉. Iterating bounds the length of an [h,h−r] code below by the sum of the successive rounded-up distances. Subtracting its dimension gives the displayed bound. [Griesmer, 1960](https://doi.org/10.1147/rd.45.0532)

The case needed here has a shorter proof. Set h=s+2. If r≤s, choose two independent relations p,q. The words p, q and p+q each have weight at least s+1. At each coordinate their combined weights sum to at most two. This would imply 3(s+1)≤2(s+2), impossible for s≥2. Thus r≥s+1.

## Menus chosen after seeing the polynomial

For each of the at most 2ˢ advice messages, consider the entire fixed set of signed claims the verifier accepts with that message. This includes the union over all its nondeterministic witnesses. If its rank is at least s+2, keep any s+2 independent rows. At most 2^(m−s−1) choices of interval coefficients can satisfy their signed equations. Summing over every message covers at most half the 2ᵐ possible tables. This counting argument even tolerates an uncomputable decoder. It assumes the advice has exactly s binary positions, since a free variable length can itself transmit information.

For attainability, take s+1 distinct moduli and their b elementary coordinate masks each. The (s+1)b full rows are independent. There are more restricted rows than interval coordinates, so they have a nonzero relation. Combine its coefficients within each modulus to obtain one mask per modulus. Each of the s+1 masks is nonzero, since any s moduli retain their joint rank on the interval. The resulting s+1 full rows are independent, sum to zero on the interval, and have restricted rank exactly s. Supply their first s labels as advice and recover the last one by XOR. The construction uses only the moduli and the public interval to choose its rows. With b=2n and s polynomial in n, the moduli and masks can be found in 2ⁿ poly(n) time by the field enumeration in the companion note. [Uniform generation](advised-claims.md)

## What survives a promise of few nonzero coefficients?

The exact upper bound above covers all polynomials on the interval. The unadvised diagonal also limits the number of nonzero coefficients there. Write t for this weight bound.

* For a fixed family of rows of restricted rank r, the t-sparse inputs give at least Σ_{j=0}^{min(t,r)} binom(r,j) answer patterns. Choose r independent columns of the restriction matrix and allow all sums of at most t of them. In particular, for t≥s and h=s+2, there are at least 2^(s+1)−1 patterns. A fixed set of s+2 rows still cannot be labeled using s advice bits.
* For varying signed menus, let K be their count. If their affine solution sets leave a point uncovered in the full interval cube, they leave a point of weight at most K uncovered. Take any uncovered point. From each nonempty affine solution set choose a defining equation falsified by that point, and impose the complementary equation. This consistent system has at most K rows and hence a solution supported on at most K pivot columns. Every such solution avoids every menu. Empty solution sets can be discarded. The generic K bound is sharp for arbitrary flats, since avoiding the K coordinate hyperplanes given by xᵢ=0 requires weight at least K. With K=2ˢ this argument need not give weight as low as s.
* A stronger conclusion holds if each menu uses at most k distinct moduli, with kb≤m. Fix one public window of kb positions inside the interval. Each menu of h full-independent rows has restricted rank h already on this same window. At most 2^(h−1) messages can cover at most half its assignments. If kb is positive and even, more than half the assignments have weight at most kb/2. Consequently, guaranteeing h correct independent claims within such menus requires at least h advice bits whenever t≥kb/2. In particular, for b=2n and t=n, even letting the advice choose **which single modulus** to use cannot save a bit. Arbitrary width across moduli is essential to the remaining sparse-source question.

These tests leave a precise case unresolved. An advice-dependent choice of many moduli could still exploit weight at most s inside a much longer known interval. The exact one-bit gain does not obstruct certificates using additional properties of the particular diagonal table. The Lean file verifies the three-word weight inequality, its integer contradiction, and the capacity arithmetic. The script checks the constructive rank loss and exhausts the four-row bound at a small degree. [Lean](../lean/TailAdvice.lean) · [Experiment](../audits/tail_advice_experiment.py)
