# A narrow threshold for mixed checkpoint simulations

**Research journal, 24 November 2026.** On the packed logarithmic-word RAM specified in the reduction, a deterministic linear-time SAT solver cannot use $O(N/\log^{6.15484525}N)$ auxiliary bits. There is also a floor on this proof method. Even with arbitrary choices of a previously derived simulation at each separate level, the checkpoint profile rule below cannot give a negative work exponent at space exponent $6.15475$ or smaller. The interval has width $0.00009525$. The lower endpoint describes a limitation of the rule. The machine theorem uses the upper endpoint and a space hypothesis. [Packed reductions](materialized-input-census.md) · [Earlier finite checkpoint calculation](log-factor-trades.md)

## The resource rule

Use the virtual reduction with deterministic time $HL^A$ and snapshots of $H/L^B$ words, and the materialized reduction with time $RL^A+mL^p$ on $m$ public words. Here $H=\max(R,m,2)$, $L=\log(H+2)$, and constant factors and additive polylogarithms are suppressed. In the packed linear-time case $A=3$, $p=2$, $B=b-2$ for SAT space $N/\log^b N$. Write
$$
 c=(B-p)/A=(b-4)/3.
$$
A normalized profile $(d,f)$ gives complementary time $O(HL^{Ad}+mL^{p+Af})$. When $Ad\le p+Af$, it also gives the separated bound $O(RL^{Ad}+mL^{p+Af})$. The initial pair $(1,0)$ has this separated bound directly by materialization.

Choose $k$ such complementary simulations $(d_i,f_i)$ in order from the outer to the inner checkpoint level. Let $D_i=\sum_{h\le i}d_h$, $D_0=0$, $v_i=f_i+D_{i-1}$, and $F=\max_i v_i$. Use $P_i=\lceil L^{A u_i}\rceil$ segments at level $i$. Put $S=O(H/L^B)$ for the number of words in a snapshot. Each level guesses $O(P_i S)$ words, then selects a segment with universal polarity. Only its two endpoints and the original public input pass to the recursive segment checker. From a verifier costing $U$ steps on that smaller data, profile $i$ gives cost
$$
 O\big((U+S+\operatorname{polylog} H)L^{Ad_i}+
        (m+(P_i+O(1))S)L^{p+Af_i}+\operatorname{polylog} H\big).
$$
This bound also pays for guessing the list. It applies when the selected replay has a smaller clock than the list length, using the stated separated bound. The deterministic segment predicate can be tested in either polarity, by also applying the construction to its complement. Starting from a replay of time $O(HL^A/\prod_i P_i+S+\operatorname{polylog}H)$, expand this recurrence from the inside out. The list at level $i$ costs $HL^{A(u_i-c+v_i)}$; the base replay costs $HL^{A(1-\sum_i u_i+D_k)}$. The public input contributes $mL^{p+AF}$. Copying the selected endpoint pair contributes at most the larger of $HL^{A(F-c)}$ and $HL^{A(D_k-p/A-c)}$. The latter fits the former whenever the last profile has its usual input guard. All levels use fixed clocks and padded list dimensions; their input lengths and deadlines have logarithms comparable to $L$ as in the packed calculation. [Checkpoint construction and clocks](log-factor-trades.md) · [FLMV, Lemma 5.3](https://lance.fortnow.com/papers/files/tst.pdf)

Consequently the output profile is $(d',F)$ with
$$
 E=\frac{1+\sum_i(v_i-c)+D_k}{k+1},\qquad
 d'=\max\{E,F-c,D_k-p/A-c\}.
$$
Take $u_i=d'+c-v_i$. These powers are nonnegative and balance the displayed time bounds. Conversely their nonnegativity and the list and base inequalities force $d'\ge F-c,E$ for any split powers at this input floor. Other original-input floors can be obtained by weakening. This normalization is an affine translation of the bit-machine recurrence. The packed direct base reduction supplies the smaller starting input cost.

## Finite proof at the upper endpoint

Take the rational $c=0.71828175$. The first five nonempty inner sequences below list all earlier profiles in reverse order. The final two omit profile 2. This finite schedule, including all rounding, supplies the claimed upper endpoint directly.

At stage 0 start with $(1,0)$ and apply the one-level rule 300 times. At each later stage start with the preceding stage's work exponent. Raise its floor enough that all profiles in the indicated inner sequence fit after it at that starting work exponent. Apply the rule with this current outer profile and the indicated **fixed** suffix 300 times, retaining the raised floor. Earlier independently verified profiles continue to be available. Each work exponent is rounded **up** to a multiple of $10^{-20}$.

| Stage | Fixed inner sequence of stage indices | Final normalized work, rounded for display |
| ---: | --- | ---: |
| 0 | empty | 0.281718250 |
| 1 | 0 | 0.126873000 |
| 2 | 1, 0 | 0.070928500 |
| 3 | 2, 1, 0 | 0.044952000 |
| 4 | 3, 2, 1, 0 | 0.030950000 |
| 5 | 4, 3, 2, 1, 0 | 0.022840000 |
| 6 | 5, 4, 3, 1, 0 | 0.018023000 |
| 7 | 6, 5, 4, 3, 1, 0 | 0.004164000 |

Eleven copies of the resulting stage-7 profile give $d'<-1/200$. The exact replay checks every split width, the additional base endpoint charge, and every input guard after the initial direct simulation. All 2,401 transformations have fixed depths and constants independent of input length. Fixed rational logarithmic powers can also be implemented with integer bit-lengths and power-of-two rounding at constant-factor precision. At quadratic hierarchy clock on the original input, the public-input term is $o(H)$ and the negative work exponent makes the full simulation $o(H)$. This yields the contradiction at $b=4+3c$. Larger space exponents satisfy the same cap. [Exact rational replay](../audits/mixed-checkpoint-profiles.py) · [Complementary diagonal and RAM model](packed-band-transfer.md)

For any fixed $a\ge0$ the same packed reductions for SAT time $O(N\log^a N)$ give $A=a+3$, $p=a+2$ and $B=b-2$. Now $p/A\ge2/3$. The entire normalized calculation is unchanged apart from a possibly smaller endpoint exponent $D_k-p/A-c$ and a weaker eligibility condition $d_i\le p/A+f_i$. Thus the very same certified profiles give an exclusion whenever
$$
 b\ge (1+0.71828175)a+4+3(0.71828175)
   =1.71828175a+6.15484525 .
$$
At the displayed equality the final normalized exponent is already strictly negative. If $a$ is a fixed real exponent, the split powers can be approximated by fixed rational powers within sufficiently small error, since there are finitely many steps and the final saving has strict slack. Equivalently one may slightly increase the hypothesized time exponent and use the same schedule: exact operation maxima are continuous in the parameters, and the direct materialized base still supplies its separated bound. [Time and space costs of the packed reductions](materialized-input-census.md)

## A finite obstruction at the lower endpoint

At $c=2873/4000=0.71825$, give the rule five optimistic profiles. Their work coordinates in order are
$$
 (t_0,t_1,t_2,t_3,t_4)=(1127/4000,\ 127/1000,\ 143/2000,\ 6/125,\ 121/3000).
$$
Their shifted floors are $g_i=\sum_{h<i}t_h$. The first profile dominates the initial pair coordinatewise. Dropping the extra endpoint charge can only improve the optimizer's result.

Here is an exhaustive inductive check. Any pair with shifted floor at least $c$ has nonnegative output work if produced by the rule. That pair cannot participate in a subsequent output with floor below $c$, since every prefix time sum is nonnegative up to the first proposed negative result. For pairs below that floor, replacing a profile by a coordinatewise smaller one can only decrease $F$ and $E$. Thus it suffices to verify that every relevant tuple of the five proposed profiles produces an output dominated by at least one of them.

Only tuples in order of nondecreasing work need be checked. If an adjacent pair has larger work and smaller floor first, swapping it reduces the sum of the two list charges and preserves the outgoing prefix time. The larger of the two charges cannot increase. To see this, remove their common prefix and write the old ordering as $(d,f),(t,g)$ with $d\ge t$ and $f\le g$. The old largest charge is $d+g$ and bounds both new charges $g,t+f$. Repeated exchanges reduce any tuple to the order used in the enumeration.

Append each still-eligible index in that order, allowing repetition and skipping any next index whose list charge is at least $c$. Every prefix increases elapsed work by at least $121/3000$, so this tree is finite. The exact-rational check visits **718 nonempty tuples**. For each, one of the five pairs lies coordinatewise below $(\max(E,F-c),F)$. Therefore the optimistic profiles form an inductive lower bound on all finite applications of this mixed rule and componentwise weakening. Every achievable profile with floor below $c$ has work at least $121/3000$; any final floor at least $c$ also precludes a negative exponent. A smaller $c$ only worsens the numerical rule, since both $E$ and $F-c$ are nonincreasing in $c$. In SAT units the rule cannot give a negative exponent at $b\le1.71825a+6.15475$. This floor applies to fixed split powers and a previously derived complementary profile at each level, with the displayed time and input accounting. Other checkpoint encodings, input charges and new complementary simulations remain open. [Reproduce the enumeration](../audits/mixed-checkpoint-profiles.py) · [Finite envelope and ordered-list coverage in Lean](../lean/MixedCheckpointBarrier.lean)
