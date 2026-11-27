# Which decisions can a missing truth table determine?

**Research journal, 2026-11-24.** The attempted attack was to use the existence of an explicit hard truth table to predict a bit of the ordinary exponential-time computation H from [the coded diagonal](coded-diagonal.md). Two different statements about a missing output lead to sharply different decision problems. When every missing output gives the right bit, even a sequence of logarithmically many adaptive calls can be simulated in randomized polynomial time. When only one eligible missing output must exist, the decision problem can express a second-level quantified formula. The connection to cubic SAT below uses the actual cost of the first simulation.

## One query with arbitrary collisions

Write G for a circuit from k to m bits, m>k, and D for a Boolean decoder, with the original input fixed. Let b be the bit we seek. Assume D(y)=b on **every** string y missing from the image of G. Write R=2^(m−k). For independent uniform strings U and V of lengths m and k, put p=Pr[D(U)≠b]. Every wrong string has at least one preimage. Consequently Pr[D(G(V))≠b]≥Rp. With probability R/(R+1), return D(U). Otherwise return the complement of D(G(V)). The success probability is at least

    R/(R+1) · (1−p) + 1/(R+1) · Rp = R/(R+1).

Thus even unit stretch gives success 2/3 in this idealized mixture. This guarantee is tight among mixtures of those two branches: a constant decoder gives success equal to the uniform-branch weight, and an injective G whose image is precisely the wrong set gives success one minus that weight divided by R. The dyadic mixture below gives a fixed fair-coin running time. The underlying multiplicity bound is also used explicitly in Lemma 2.7 of Hirsch and Volkovich. [Hirsch and Volkovich](https://eccc.weizmann.ac.il/report/2025/220/)

In particular, simply reading a coordinate of the missing truth table is a poor candidate for a robust decoder. If D is balanced, exactly half the output space would have to lie in the image. This is impossible at stretch above one. At unit stretch it forces the entire image to be the wrong half, so complementing D(G(0ᵏ)) already recovers b deterministically.

## Adaptive queries, including unit stretch

Suppose a clocked deterministic reduction makes at most q adaptive calls to expanding circuits and returns b on every transcript that supplies a hole at every call. Bound computation and query counts on arbitrary replies as well, using a timeout with a default bit if necessary. Cache repeated queries if the reduction assumes a fixed choice function. Reusing cached replies makes each all-hole path consistent with some fixed function.

A simulator starts at any given transcript. At a legal prefix its error will be at most ε=1/32. At an illegal prefix it can return either bit. For a leaf at a legal prefix the claim is immediate. At an internal legal prefix, let a(y) be the recursive simulator's error probability relative to b if the next answer is y. Put p=E[a(U)]. The induction hypothesis bounds a(y) by ε at each hole. Since each image value has at least one preimage,

    E[a(G(V))] ≥ R · 2^(−m) Σ_{y in image G} a(y) ≥ 2(p−ε).

For the last step first use nonnegativity if p<ε. One trial chooses a uniform answer with probability 5/8 and returns the recursive answer. With the remaining probability it chooses the generated answer G(V) and complements the recursive answer. Its success probability is at least

    (5/8)(1−p) + (3/8) · 2(p−ε) ≥ 77/128.

Take the majority of 257 independent trials at this node. Hoeffding's inequality bounds its error by exp(−2·257·(13/128)²)<1/32, closing induction. Each trial follows only one child. If T bounds all work to replay a prefix, construct and evaluate the next circuit, sample its inputs/outputs and handle the transcript in the chosen computation model, then the recursion takes O(257^q T) time and random bits. This counts the geometric series of nodes; each has bounded per-trial work and 257 is fixed. In particular a polynomial-time deterministic reduction making O(log n) adaptive calls gives a BPP decision algorithm. This argument allows every queried circuit to have unit stretch. Prior results cover unrestricted polynomially many adaptive calls in AM ∩ coAM and give a simple random-answer BPP simulation at sufficiently large stretch. The bound above leaves open what happens to the BPP simulation at polynomial depth and unit stretch. Priority of this particular bounded-query argument has not been established. [Ghentiyala, Li and Stephens-Davidowitz, Theorem 1.1 and the open questions following §1.3](https://eccc.weizmann.ac.il/report/2025/210/)

## An exponential query lower bound for sampling-only simulations

Can a better simulation remove the exponential dependence on q? In a black-box version the answer is no, even for nonadaptive injective queries of unit stretch. Give the simulator forward evaluation of each Gᵢ and evaluation of a single decoder D on q output strings. Count each such evaluation as one probe. Let K=2^(2q), let the Gᵢ be independent uniform injections from a set of size K to a set of size 2K, and choose an independent fair bit b. If b=0, set D identically zero. If b=1, set D equal to one precisely on tuples for which every coordinate is a hole of its own Gᵢ. In both cases the same q nonadaptive hole queries and one decoder evaluation always return b.

Couple a B-probe simulator in the two worlds using the same injections and random tape. They can diverge only if a decoder probe on the all-zero execution hits the Cartesian product of hole sets. Fix the random tape and condition on the complete all-zero execution, including its forward probes. Each injection remains uniform among extensions of its own revealed input/output pairs, independently across i: all queries are determined by the earlier recorded responses. If hᵢ outputs have been revealed for Gᵢ, a specified unrevealed output has hole probability K/(2K−hᵢ), and a revealed output has probability zero. Thus each decoder probe on that execution hits the product with probability at most

    [K/(2K−B)]^q ≤ 2^(1−q)                         if B≤K/q.

The inequality follows from (1−1/(2q))^q≥1/2. A union bound gives coupling divergence probability at most B·2^(1−q). A simulator correct with probability 2/3 in both worlds must separate their acceptance probabilities by at least 1/3. It needs B≥2^q/6. If B>K/q this inequality already holds by the choice of K.

This example puts an explicit limit on approaches treating the circuits and decoder solely through evaluation. The upper and lower query bounds both grow exponentially in q, with different bases. A concrete circuit reduction gives access to its code and may exploit that information; the example yields no RAM lower bound for a problem given by explicit formulas.

## Reverse construction from a bounded-error decision

In fact every BPP decision problem has a polynomial-time deterministic reduction with just one robust call. Pad a power of two t so that it bounds the size and random input length of the acceptance circuit for the BPP machine on the fixed input. Take the constants c,d in the Impagliazzo–Wigderson hard-truth-table generator with hardness exponent 1/2. It maps a table on ℓ=c log₂ t variables and d log₂ t seed bits to t pseudorandom bits. If the given table has circuit complexity at least 2^(ℓ/2), the acceptance probability of a size-t circuit under the generator differs from its uniform acceptance probability by less than 1/t. [Impagliazzo and Wigderson](https://doi.org/10.1145/258533.258590) · [Kabanets, Theorem 12](https://www2.cs.sfu.ca/~kabanets/papers/rp-zpp-journal.pdf)

Construct an expanding circuit that takes a description of an ℓ-input circuit of at most ⌈2^(ℓ/2)⌉ gates and outputs its complete 2^ℓ-bit table. Use the zero table on malformed descriptions. Fixed-width descriptions require O(ℓ·2^(ℓ/2)) bits, fewer than 2^ℓ at large t. Pad the inputs, ignoring surplus bits, to make the stretch exactly one if desired. The truth-table construction is uniform and takes polynomial time in t, since ℓ=O(log t). Every missing output meets the required hardness threshold. The decoder enumerates all t^d seeds and returns the majority output of the original circuit. For t>6 the BPP gap survives the approximation. Hence the decisions obtainable by such one-call reductions, or logarithmic-call reductions, coincide with BPP at polynomial clocks. The degree of this converse simulation matters for fine-grained time bounds.

## Why the quantifier on the hole matters

Li obtains a single-valued FS₂P procedure selecting a missing string, and obtains pseudodeterministic constructions of hard tables with an NP oracle. Such a selection can have properties beyond membership in the complement of the image. To exploit a particular selection one would need a proof relating that selection to H and a cost bound for accessing it. Producing a hard function permits the BPP simulation above. Its values need have no agreement with the table of a separately prescribed computation. [Li](https://arxiv.org/abs/2310.17762)

Weakening “every hole” to “some eligible hole” changes the verification problem. Given Boolean circuits G and D, deciding whether there is a missing y with D(y)=1 is Σ₂ᴾ-complete. Membership follows by guessing y and universally checking G(z)≠y. For hardness, take a formula ∃u∀z Q(u,z), set m=1+|u|+|z|, and let candidate encodings be e(u)=1u0^|z|. On input (u,z), output e(u) when Q(u,z) is false and 0^m otherwise. The decoder accepts exactly the candidate encodings. The candidate e(u) is missing precisely when ∀z Q(u,z). This construction already has unit stretch. Guessing a purported eligible hole therefore reintroduces a universal image-exclusion test, even though ordinary SAT can check that a *given* preimage exists.

## Consequence for the unrestricted cubic SAT target

For the specific H in the coded diagonal, let N=2ⁿ, t₀=⌊(N−1)/(2n)⌋, and I denote the count of degree-2n binary irreducibles. Under the cubic SAT hypothesis, its total Boolean predictors using o(N) advice in time n^{O(1)}N have absolute correlation at most √(t₀/I), which tends to zero, on the valid modulus-and-mask pairs. This is the quantitative claim of the earlier construction. [Diagonal, clock and advice hypotheses](coded-diagonal.md)

Suppose there were a fixed robust reduction for the correct coded bit on each query at infinitely many lengths, simulable as above on ordinary multitape machines with uniform total clock B=O(257^q T)=o(N) time and random bits. On each such length, average success over both questions and random tapes is at least 31/32. Some tape of length at most B therefore gives average success at least 31/32 over the questions. Supply that tape as read-only advice to an ordinary deterministic claim verifier which checks that the simulator returns its proposed bit. Its correlation is at least 15/16. This contradicts the cited bound for all sufficiently large such lengths. The same argument works if the reduction promise holds only on a fraction α of questions and everything else can be wrong, provided 2α·(31/32)−1 exceeds √(t₀/I). A uniform timeout on all simulations and the advice-length bound are essential. For example, q=o(n) and T≤2^((1−δ)n) with fixed δ>0 suffice.

This identifies the missing construction. A robust reduction must encode information about H's own answers inside the missing strings at that clock. An efficient producer of an arbitrary hard truth table supplies no such map. The target SAT lower bound remains open. [Lean check of the finite multiplicity and success inequalities](../lean/RangeDecisions.lean)
