# How much can a certificate shorten a disjunction?

**Research journal, 24 November 2026.** An explicit window is known to contain many blocks with small exceptional fraction. I tried to certify a shorter disjunction inside the window. The reduction below needs only an unbounded factor of shortening. I also checked a structural way to obtain the shorter disjunction by copying true outputs between blocks. There is a quantitative forward implication, but the reverse implication needed for the proposed certificate fails on the actual source.

## A list test with no individual witnesses

Use the globally prefix-free multitape interpreter U from the [length construction](prefix-lengths.md). In block j the output lengths are m in [2^j,2^(j+1)). A length is heavy if every m-bit word starting with j zeroes has a program shorter than m emitting it by B(m)=2^(20m). Write e_j for the fraction of heavy lengths. The global Kraft bound is Σ_j e_j≤1/2.

For precision s put b=2^s, W=2^b, J=2^(3b), and I_s=[J,J+W). In this note a good block j in I_s satisfies **e_j≤1/W**. This condition specifies the upper endpoint needed to compress a missing word. The earlier one-bit statistic also allows some correct bit values from a different range. At least half the blocks in I_s are good. In fact, if h_s is the number that are bad, then Σ_s h_s/W≤1/2 because the windows are disjoint. Hence h_s/W tends to zero. The earlier [window bit proof](exceptional-fraction-bit.md) also bounds e_j below throughout the window.

Consider a uniform verifier for a W-bit mask A on I_s. Its accepted masks are nonempty and each one contains **at least one** good block. No identification of that block is required. Suppose there are accepted masks at unbounded shrink factors W/|A|. Given s, a mask prefix and a bound 2^(b−d) on its cardinality, suppose the existential query for an accepted extending mask has encoded SAT length and deterministic construction time at most

    2^(α·2^J) poly(2^J).

The budget uses the beginning of the window. This matters because one formula can discuss the whole window while the decoder must finish by the clock of the selected member. A verifier with mask bits as variables has the stated prefix queries by pinning them and adding a cardinality check. Accepting computations may use other witness bits of the allowed formula size.

**If α<5, these properties exclude a deterministic linear-time SAT algorithm on the requested unrestricted RAM. If α<5/3, they exclude a cubic-time one.** For linear time a fixed number of Boolean quantifier blocks may be used in the tests by the same elimination as before. [Explicit encoding and elimination](linear-quantifiers.md)

To prove this, a fixed prefix decoder reads gamma(d) and searches for the first s with b≥d that passes the existence query. Unbounded shrink factors ensure such an s for every d. It recovers a canonical eligible mask by fixing its W bits in order. It then reads b−d bits to index one of the mask's members j, rejecting out-of-range indices. Since the mask is sound, some choice gives e_j≤2^(−b). At this j at most 2^(j−b) output lengths are heavy. Among the first 2^(j−b)+1 lengths at least one has a missing word. Read j−b+1 bits to select its length m, then m−j bits for the suffix after the j zeroes. With those choices the actual missing word has a program of length

    fixed header + |gamma(d)| + (b−d) + (j−b+1) + (m−j)
      = m + fixed header + |gamma(d)| + 1 − d.

This is shorter than m for large d. The W prefix queries and all earlier precision tests add a polynomial factor in 2^J. For a hypothesized SAT time exponent p, RAM emulation on tapes and the outer fixed interpreter take at most 2^(4pα·2^J) poly(2^J) steps. The strict exponent margin and m≥2^J put the run within B(m). This proves the contradiction. The search for s is what permits arbitrarily slow improvement in the shortening factor. Encoding the successful s separately would charge for information the verifier can recover.

There is a reason to require a *certificate* of the shorter disjunction. Consider the initial segment of I_s of size ceil(W/s). Since Σ_s h_s/W is finite but Σ_s 1/s diverges, this explicit segment contains a good block for infinitely many s. Its length already improves on W by an unbounded factor. This unconditional existence argument supplies no method within the budget to distinguish the successful s. Treating every such segment as sound would invalidate the reduction.

## Verifying a list against many possible explanations

Here is a way to construct a certified mask without finding an individual good member. Let a uniform family of nonempty hidden states at s specify subsets R of I_s. Suppose each such subset has size at least δW, for a fixed δ>0. Suppose also that on *every* window at least one allowed state has its R contained in the true good set. Other states may select many bad blocks. Let M_s count distinct subsets R, independently of how many witnesses specify the same subset.

Verify a proposed mask A by checking that it intersects R for every allowed state. This is sound since it meets the particular sound R. If M_s is small, a short mask exists: sample n independent uniform positions in I_s and keep their distinct values. Each R is missed with probability at most (1−δ)^n. For 0<δ<1, take n=ceil((ln M_s+1)/(−ln(1−δ))); δ=1 needs one sample. The union bound guarantees a mask of size at most n. The search for the mask does not use the value of M_s. Under the assumed SAT clock it can test successive size bounds and query an extending prefix as above.

It follows that **log₂ M_s=Ω(W)** under linear SAT if the state, its feasibility and its selected set can be checked by a fixed number of quantifier blocks within the preceding encoded budget (with strict exponent margin for compiling the extra blocks). Otherwise some subsequence would have hitting masks shorter than W by unbounded factors. Equivalently, at large windows a constant fraction of the coordinates can be shattered: every zero-one pattern on those coordinates occurs on restriction of some R. Indeed a family of VC dimension v has at most Σ_{i≤v} binom(W,i) members, whose logarithm is o(W) when v=o(W). This applies to distinct predictions even when the state uses many more bits. [Sauer's counting lemma](https://doi.org/10.1016/0097-3165(72)90019-2)

For cubic SAT the same implication holds when the whole hitting test has the single-SAT encoding used in the list theorem. A sufficient special case has poly(W) hidden bits, deterministically checkable feasibility, and existentially checkable membership of a block in R. Enumerate the hidden states, and for each feasible one require existence of a marked hit and its witness. Their conjunction has one existential block. There are 2^poly(W)=2^o(2^J) states, so this multiplication can be absorbed in the strict exponent margin. If both feasibility and membership are deterministic and the hidden-state enumeration fits the clock, exhaustive testing of the 2^W proposed masks already works without any SAT assumption. A useful model must satisfy the semantic condition that a sound R exists in every window where its hitting masks are offered. Merely guessing a concise description of the unknown good set leaves that condition unchecked.

## Trying to transfer an upper bound from a nearby block

To understand what information could certify a list, I tested whether the small exceptional fraction at one scale could control the next. There is a forward copying rule on the *actual* source. Let E(h) be the prefix code consisting of the gamma code of the bit length of the positive shift h, followed by its low bits, and write l(h)=|E(h)|. For some fixed integer d and all k one has

    e_k ≥ Σ_{h≥1, k−h≥1, h≥l(h)+d}  2^(−l(h)−d) e_{k−h}.             (1)

For clarity, the proof below applies for all sufficiently large source output lengths; choosing d large enough also absorbs fixed startup costs everywhere the sum is nonempty. This formula adds the contributions at k without counting the same target length twice.

One fixed stream machine reads gamma(d), E(h), and a complete prefix program p, identifying the end of p when its simulated machine halts. Suppose it yields an m-bit word with j=⌊log₂ m⌋ leading zeroes as required (more initial zeroes are allowed). Write u for the remaining m−j bits and k=j+h. The machine reads h−l(h)−d bits to form the high bits of an h-bit integer z; append d zeroes and the reversed bit string E(h) to complete z. Put m'=2^h m+z. This is in block k. Read m'−k−(m−j) additional bits r and print k zeroes followed by u and r. The extra length is nonnegative. Inputs with a failed format test can diverge.

At a heavy source length m, a suitable p of length <m exists for every u. The full name has length

    header + |gamma(d)| + l(h) + |p| + h−l(h)−d + m'−k−m+j
      = m' + (|p|−m) + header + |gamma(d)| − d.

Choose d large enough to make the overhead nonpositive. A source run may take all B(m) steps. The fixed stream machine simulates U directly, and copying plus binary counters take poly(m'+1) further time up to polynomial bookkeeping for the source clock if needed. No source timeout test is necessary. The fixed outer simulation costs at most a square. Since m'≥2^h m, the whole simulation finishes by B(m') for the allowed h after increasing d. Thus all 2^(h−l(h)−d) chosen lengths m' are heavy. For a fixed h their sets are disjoint for different m. Across different h their low bits end in the reversal of a prefix code, which is suffix-free. There are e_j·2^j heavy m and 2^k candidate lengths in the target block. Dividing the distinct contributions by 2^k proves (1).

For example, the fixed kernel K_h=2^(−l(h)−d) on eligible h has total weight κ≤2^(−d)<1. The copying inequality does not give unbounded amplification just by iteration. For any nonnegative dyadic seed masses a_k with denominator dividing 2^k and Σa_k≤(1−κ)/2, put

    x_k = a_k + Σ_{1≤h<k} K_h x_{k−h}.

Induction gives nonnegative x_k with denominator dividing 2^k, since every contributing h satisfies l(h)+d≤h. Summing finite prefixes first gives Σx_k≤Σa_k/(1−κ)≤1/2. The resulting profile dominates the planted masses and obeys (1). In particular one can plant values 2/W at every member of prescribed masks in disjoint windows whenever their combined cost Σ 2|A_s|/W fits this budget. This is an obstruction for an inference based only on the mass and copying inequalities. It does not realize every such profile by U.

The profile test can distinguish an inference failure from a shortfall in a particular hitting-set algorithm. Choose d in the copying proof large enough that κ<1/3. At one fixed large window plant a_k=2/W on an arbitrary set P of at most floor((1−κ)W/4) indices, zero elsewhere. The recursively defined x has maximum at most 2/[W(1−κ)] by induction. At an unplanted index x_k≤2κ/[W(1−κ)]<1/W. At a planted index it is at least 2/W. Its total is at most 1/2. Consequently the set of bad blocks in this window is *exactly P*. The family of good masks consistent with both numerical inequalities therefore shatters a linear number of coordinates. No mask of at most floor((1−κ)W/4) positions can hit all of them. To make the preceding hidden-state test actionable one would need a constraint on the actual programs beyond these two inequalities.

## Where the reverse implication breaks on the actual interpreter

At distance only three in the block index, small values can be followed by much larger ones. Let j_r be the first block after j_(r−1) with e_j≤2^(−r), starting at j≥r. These blocks exist by summability. A tape procedure can select k_r=j_r+3 and compute e_{j_r} *exactly* within the scan budget appropriate to k_r. For each m in the earlier block, simulate every string shorter than m for B(m) steps on the fixed U, stop on any request beyond the supplied bits, and deduplicate the m-bit outputs. This costs at most 2^(21m) poly(m) tape steps. Summing through the end of block j takes at most 2^(42·2^j) poly(2^j). For block k=j+3 the exponent is (42/8)·2^k, below the admissible multitape exponent 10. The fixed interpreter's square still fits the later clock. Thus the accepted-block rank lemma applies to the list of k_r. For all large r,

    e_(j_r+3) ≥ c/[r(log₂(2r))²],       e_(j_r) ≤ 2^(−r).

The earlier e_j are eventually positive by the same rank lemma for the unfiltered list. In particular there is no uniform constant upper bound on these forward ratios. Making the targeted upper bound a cheaply computable function of previous exact small values alone has to confront these genuine increases. [Rank lemma](exceptional-fraction-bit.md)

A more local test concerns the first genuinely good block j₀ inside I_s. Enumerate the earlier full computations to find this j₀. For a fixed large d and every 0≤z<2^(b−l(s)−d), set k=j₀+3+z. The same enumeration now fits by block k. A decoder with inputs E(s), gamma(d), the b−l(s)−d bits of z and then the length and suffix fields of the list proof would print a missing word if this k were good. Its total size would again be m+header+|gamma(d)|+1−d. Hence **every one of these consecutive successors is bad** for all sufficiently large s. They lie inside I_s, since j₀ is in its first W/2+1 indices and the displayed segment has length o(W). This yields an actual interval of bad predictions immediately after a location whose exact verdict becomes accessible at the later clock. The conjectured reverse transfer from verified low mass to nearby low mass fails even within the explicit high-density windows.

A verified small hitting list could still arise from dependencies beyond (1), or from proofs that a set of late program computations cannot jointly cover all its candidates. I found no such list. The unrestricted SAT bound remains unproved. The finite experiment checked exact realization of 697 planted patterns for one small kernel. [Finite Lean checks](../lean/WindowLists.lean) · [Experiment](../audits/window_lists_experiment.py)
