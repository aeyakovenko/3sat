# Searching across lengths for a short program that misses an early output

**Research journal, 24 November 2026.** Can a fast SAT algorithm find a length at which an early output is missing, without finding the missing output itself? For a single prefix-free source there are many such lengths. The difficulty is to pick one with a short description, or to certify a block containing a sufficiently small fraction of exceptions. This gives a test for the linear SAT target in the [project goal](../RESULTS.md#research-goal).

## A single source across all lengths

Fix a universal prefix machine U with a one-way bit input. Its input is the exact sequence of bits consumed when it halts. Each computation emits at most one finite binary string. Its halting inputs form a globally prefix-free set, and a fixed stream machine can be run by prepending a constant-length compiler tag. A concrete implementation uses a prefix code for a fixed multitape machine's instruction table, then interprets its bit requests. A fixed machine taking T steps can be interpreted in O((T+1)²) steps by sequential sweeps of the tapes used so far. U receives no external length parameter. The SAT model being investigated still has random access and logarithmic words. Global prefix-freeness is essential to the accounting below. For background on prefix complexity and Kraft weights see [Bienvenu, Downey, Nies and Merkle](https://arxiv.org/abs/1603.08351).

Write B(m)=2^(20m). Let v_m be the least integer whose m-bit binary representation is absent from the outputs of U on inputs shorter than m by step B(m). There are fewer than 2^m such binary inputs. For every z<v_m pick one program producing its m-bit representation. Programs chosen for different pairs (m,z) are distinct, since output length is intrinsic. A selected program p contributes 2^(−m) ≤ 2^(−|p|)/2. By Kraft's inequality,

    Σ_{m≥1} v_m / 2^m ≤ 1/2.

The finite proof works by taking a depth L large enough for the lengths in question. Distinct selected programs occupy disjoint sets of leaves of the binary tree at depth L. The proof does not evaluate U.

For j≥1 put N=2^j. Call m in [N,2N) light when v_m < 2^(m−j), so that an m-bit word starting with j zeroes is missing. Write h_j for the number of other lengths in the block. Each such length contributes at least 2^(−j) to the sum. Consequently

    Σ_{j≥1} h_j / 2^j ≤ 1/2.

Every block has at least half its lengths light. The fraction that are light tends to one. This uses a new prefix-free source across all lengths. The corresponding estimate for separately conditioned raw programs would count the same program more than once without a common Kraft bound.

The half-unit bound by itself is sharp. In fact, fix any finite collection of desired heavy lengths, with h_j selections from block j and Σ h_j 2^(−j)≤1/2. Assign each selected m in block j a prefix of length j−1, prefix-free across all selections. The Kraft sum of these prefix lengths is 2Σ h_j 2^(−j)≤1. A finite machine reads the prefix identifying m, then m−j raw bits, and prints them with j leading zeroes. Every valid name has length m−1 and the first missing index at this length is exactly 2^(m−j). At every other length the first missing index is zero. The finite prefix and output schedule can be compiled into the finite control with linear time per emitted word. Thus these are exactly the possible finite patterns allowed by the mass inequality if universality is dropped. The stronger restrictions below use the universal compiler.

## A dense set of hard-to-select offsets

Let i be the j-bit representation of m−2^j for any light m. Every program printing i under U in at most 2^(2^j) steps has length at least j−O(1), with one constant for every j and i.

To prove this, a fixed machine runs such a program p from its stream and obtains the j bits including initial zeroes. It computes m from them, consumes another m−j raw bits, and prepends j zeroes to those bits for its output. Its domain with this two-part input is prefix-free. It can produce any of the first 2^(m−j) words, including the actual omission at a light length, by the appropriate choice of suffix. If c is the compiler length, its complete program has length c+|p|+m−j. For |p|<j−c this is shorter than m. Simulating the fixed U internally and then compiling the outer machine costs at most O((2^(2^j)+poly(m))²) steps when the inner U is implemented directly on the fixed machine's tapes. This fits B(m) for all sufficiently large j. Absorb the finitely many small j into the constant. The resulting collision with the definition of v_m proves the claim. In particular even the first light offset need not have a short name that runs on this doubled exponential clock.

## What would rule out linear SAT

At each j, consider a uniform list of distinct lengths in the block. One particular way to specify it is to scan the lengths in increasing order and include m when an explicitly constructed SAT formula F(j,m) is satisfiable. Assume both the encoded size and deterministic RAM construction time of F are at most 2^m poly(m). There is no soundness requirement for F. Define r_j to be the zero-based position of the **first light length on the list**, or infinity if none is on the list. Let b=⌊log₂ j⌋+1 and ℓ(j)=b+2⌊log₂ b⌋. A prefix code for j of length ℓ(j) uses the Elias gamma code of b followed by the low b−1 bits of j.

Under a linear-time SAT hypothesis, for some c_F>0 and every sufficiently large j,

    r_j ≥ c_F · 2^(j−ℓ(j)).

In particular, one uniformly constructed test with r_j=o(2^j/(j (log(j+1))²)) on an infinite subsequence would exclude linear-time SAT on the requested unrestricted model. A test identifying even one light length in infinitely many blocks, with a bounded number of earlier false positives each time, suffices. Arbitrarily many later false positives are allowed.

Here are the code length and clock details. One fixed decoder reads the prefix code of j, a gamma-coded positive integer d, and k=j−ℓ(j)−d rank bits (reject if k<0). It finds the length m of that rank, consumes a further m−j bits, and outputs them with j initial zeroes. If the rank denotes a light m, some suffix produces v_m. Its total program length including the compiler tag of length a is

    a + ℓ(j) + |gamma(d)| + k + m−j = m + a + |gamma(d)| − d.

Choose d>a+|gamma(d)| once, after fixing the decoder. This avoids assuming that an interpreter hardcoding its own length has small overhead. Under linear SAT, scanning up to m costs 2^m poly(m) RAM steps. A multitape machine can emulate the RAM in the square of its time times a polylogarithmic factor by scanning a sequential list of memory cells. The outer interpreter can square time once more. Total time is at most 2^(4m) poly(m), well within B(m). Thus no rank less than 2^k can be light, giving the inequality with c_F=2^(−d). The same increasing-order decoder under a cubic hypothesis takes 2^(12m) poly(m) native steps, so a successful test of this size would actually exclude cubic SAT as well.

For the **linear target alone**, the verifier can be larger. If size and construction time are at most 2^(αm) poly(m) for a fixed 0<α<5, the bound becomes 2^(4αm) poly(m), still below B(m). For cubic SAT the same calculation needs α<5/3. The margins reflect this interpreter and its two elementary simulations. They are sufficient exponents.

## A certificate about a whole block would suffice

There is a second way to exploit the sum bound. It requires no test at an individual length. For k≥1, search j=k+1,k+2,… for the first satisfiable explicit formula G(k,j). Suppose the encoded size and uniform construction time are at most 2^(α·2^j) poly(2^j) for a fixed α<5, α>0. If, for unbounded k, that search terminates at a block satisfying

    h_j ≤ 2^(j−k),

then linear-time SAT is impossible. No bound on how large the successful j is in terms of k is needed. In particular it would suffice to recognize a sound certificate of this aggregate upper bound in at least one block for each of unboundedly many k.

Indeed, prefix-encode k in gamma code. Use the hypothetical linear solver to recover j by the stated search. The first 2^(j−k)+1 lengths of that block include a light m by pigeonhole. Read j−k+1 bits to specify its offset among them, then m−j bits to specify the suffix of the missing word. Including the fixed compiler, total length is m−k+1+|gamma(k)|+O(1), less than m for large k. Testing all scales up through j takes 2^(α·2^j) poly(2^j) RAM time, since even j times the final bound fits the polynomial factor. Conversion to the native prefix machine costs at most 2^(4αm) poly(m) because m≥2^j. Consequently some short program prints v_m in time. For a cubic SAT hypothesis α<5/3 suffices.

This also tests a candidate lemma about the *rate* of convergence. If an ordinary deterministic RAM within the stated construction budget could certify arbitrarily small upper bounds on h_j/2^j at some blocks (for example by computing a uniform upper estimate tending to zero), the same decoder could run its test directly. Such a rate cannot be obtained within that clock unconditionally. The series bound ensures the desired blocks exist for every k. An effective certificate at the required cost is the extra content needed from SAT.

Averaging suggests trying a block chosen from a window of about 2^k consecutive scales. The global half-unit of mass ensures a good choice in such a window. Specifying the choice directly costs about k bits, using the saving in the decoder. The obstruction persists for shorter, overlapping windows in the following exact sense. Give each k a proposed finite set J_k of scales j≥k+1. If Σ_k |J_k|2^(1−k)≤1/2, assign to each proposed j the largest value 2^(1−k) among the k proposing it, and assign zero elsewhere. These values are integer multiples of 2^(−j). Their sum is at most 1/2, yet every proposed j has exceptional fraction strictly above 2^(−k) for its proposer. This example concerns the mass inequality in isolation. It does not prescribe the actual interpreter's fractions.

For the linear target, G may also be a quantified Boolean circuit with any fixed number of quantifier blocks under the same size and construction bounds. Under linear SAT, eliminating a fixed number of blocks takes the encoded size times a fixed polylogarithmic factor. This factor is polynomial in 2^j for the stated size and fits the strict exponent margin. Thus an aggregate certificate with a few rounds of adversarial challenges is eligible. [Uniform quantifier elimination](linear-quantifiers.md)

## The last exceptional block and the busy beaver function

The block fractions e_j=h_j/2^j are uniformly computable rationals by finite exhaustive simulation. Define L(k) as the last block j with e_j>2^(−k), using zero if there is none. Let BP(s) be the largest integer printed by U on any halting program of length at most s, with no clock and default zero. Interpret output strings as unsigned binary. There is one constant c such that for all sufficiently large k,

    BP(k−c) < L(k) ≤ BP(k+c).

For the upper bound, order the nonzero e_j by index and put disjoint intervals of those lengths end to end in [0,1). In the interval of length e_j, take the first dyadic cell of depth t=⌈−log₂ e_j⌉+1 that fits. Its length is at most e_j/2, so it fits even when the left endpoint is off grid. The binary addresses of these cells form a computably enumerable prefix code for the indices j. A stream machine decodes any valid address: at each consumed prefix, wait until an enumerated codeword extends it or equals it, halt in the equality case and otherwise read one more bit. Prefix-freeness ensures that no valid word is read past its end. For e_j>2^(−k), this gives a program for j of length at most k+O(1). In particular it applies to L(k) whenever that index exists.

For the lower bound, use one fixed decoder. Read gamma(d), then run an unbounded prefix program p on the stream, counting its length and its running time t. When it halts with integer s, set k=|p|+d and j=max(k+1,s+1,t+1). If e_j≤2^(−k), some length among the first 2^(j−k)+1 in the block is light. As in the block decoder, use j−k+1 bits to select such a length and m−j bits for its omitted suffix, rejecting out-of-range ranks. Including the tag, total length is m−d+1+|gamma(d)|+O(1). For all d larger than one fixed constant this is less than m. The computation of p may have taken any finite time: m≥2^j and j>t leave enough time for that simulation and the subsequent polynomial-in-m copying, including the outer interpreter. Thus e_j must exceed 2^(−k). For any p of length at most k−c use d=k−|p|. Taking a p attaining BP(k−c) gives L(k)≥j>s, as claimed.

The arguments give an individual description bound as well. The prefix complexity of the integer L(k) is k+O(1): the code for a heavy block supplies the upper bound, while no program of length at most k−c can print an integer this large. Hence the nondecreasing L cannot stay constant across an unbounded number of consecutive precisions. Also L eventually exceeds every total computable function f(k), since a fixed evaluator supplied with gamma(k) prints f(k) with O(log k) description bits when unclocked. So no computable modulus of convergence works, even though each e_j is computable. A SAT certificate about a single good block would still suffice. A certificate guaranteeing that *every later* block is good for every precision would give a computable modulus if its witnesses could be found by search. Busy-beaver comparisons for convergence of semicomputable series have a substantial literature. The argument here is for the last *individual block fraction* exceeding a threshold for this particular clocked source. Priority for this specialization has not been established. [Bienvenu and Shen, section 8](https://arxiv.org/abs/1110.5028)

## The total exceptional mass contains halting information

The same padding gives more than occasional large fractions. Fix a positive integer d that exceeds the tag and coding costs in the following single decoder. For each halting program p, let t be its running time, s its integer output and k=|p|+d. In the preceding proof replace the choice of j by an injective index j(p) exceeding t, s and k. For example take one plus the Cantor pairing of the integer represented by the string 1p with the Cantor pairing of t and s+k+1. The pairing dominates its arguments. Computing this index, constructing the needed bit lengths and handling the raw data still fit a polynomial in m. The decoder reads gamma(d) explicitly, so d can be chosen after the compiler is fixed. The proof forces

    e_{j(p)} > 2^(−d) · 2^(−|p|)

for every halting p, increasing d to absorb the small cases. Different programs charge different blocks. Put α=Σ_j e_j and let Ω be the halting probability of U. At each finite stage u let α_u sum the first u block fractions, and let Ω_u count the weights of the programs halted by u steps. Both approximations are computable. Because j(p)>t, every contribution of a program missing from Ω_u has a distinct covering term beyond α_u. Thus

    Ω − Ω_u ≤ 2^d (α − α_u).

This is a Solovay reduction of Ω to the left-computably-enumerable real α. The classical characterization of random left-computably-enumerable reals implies that α is Martin-Löf random. In particular it is noncomputable, although its summands can each be found by a finite calculation. This conclusion concerns the chosen universal program source. The SAT argument needs information at a favorable finite block, which neither this randomness result nor the half-unit upper bound provides. [Kučera and Slaman](https://math.berkeley.edu/~slaman/papers/random.pdf) · [Bienvenu and Shen](https://arxiv.org/abs/1110.5028)

## Attempt to construct the length test

One way to certify a light length would be to bound how many short programs actually produce an m-bit word. For each m collect those programs that do so by B(m), and let w_m be their total Kraft weight. These sets are disjoint over m, hence Σ_m w_m≤1. The count of the programs is at most 2^(m−1) w_m. Whenever w_m<2^(1−j) there are fewer than 2^(m−j) such programs and the length is light. The fraction of lengths failing this stricter test is summable across the dyadic blocks by the same charging argument.

A possible witness is a prefix cover. Take stream prefixes of length at most m−1 whose cylinders cover every eligible halting program. If their total Kraft weight is below 2^(1−j), the same counting argument holds. Almost every length in these blocks has some such cover, since the actual programs themselves form a cover. The outstanding step is to **verify coverage or an adequate substitute** with a small enough formula at one of the early ranks above. Writing down the actual covering prefixes does not verify coverage. Expanding the full B(m)-step computation to check a candidate program already exceeds the chosen formula budget. Treating every execution still running at an early cutoff as a candidate also counts branches that never read another bit or halt. I have no construction of F meeting the rank condition. The density estimate, coding argument and conditional search criterion leave the target open.

[Lean finite counting and code-length checks](../lean/PrefixLengthMass.lean)
