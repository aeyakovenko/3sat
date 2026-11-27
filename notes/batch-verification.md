# Can algebraic batching verify a RAM computation below its original clock?

## 2026-11-23 · Replace the sorting network by a multiset check

In [the block simulation](history.md) an accepting proof describes the chronological records of a RAM run and the intermediate layers of a sorting network. An alternative is to guess only the chronological list A and an address-ordered list B, verify transitions on A and adjacent reads on B, and reconcile the two lists. The desired saving is below T steps for a T-row hierarchy computation. Any use of a hypothetical O(mᵈ) SAT solver must charge its explicit input length m, for d=2 or 3.

Encode records injectively in a sufficiently large finite field. Put P_A(z)=∏ᵢ(z−Aᵢ) and define P_B similarly. Unique factorization gives equivalence between multiset equality and polynomial equality. For fixed distinct multisets of K records the difference has degree at most K−1. A uniform challenge thus detects inequality with probability at least 1−(K−1)/|F|. This is the algebra behind permutation arguments and interactive checks for products. [Gabizon, Williamson and Ciobotaru](https://eprint.iacr.org/2019/953) · [Thaler](https://arxiv.org/abs/1304.3812)

**Exact point-query count.** If a deterministic verifier can only ask for the two numerical product values at a challenge, K distinct field points suffice, and K are necessary for a deterministic worst-case guarantee when |F|≥K+1. Answer zero on both sides to the first K−1 distinct queries. Choose a common set of K−1 roots containing those points, then adjoin distinct last roots to the two lists. Identical lists can give the same answers as well. This works with adaptive challenges and lists without repeated entries. It applies to the point-only interface. Known row circuits provide more information. A nondeterministic hierarchy simulator accepting whenever *some* challenge agrees admits the same false positives even on one fixed unequal pair containing a common root.

**A possible repair.** Suppose a supplied representation of each list gives a small **exact** circuit evaluating its product at any field point, with consistency to the actual rows already certified. For field size at least K, one SAT query for a point of disagreement decides equality. The open step is to construct or certify those evaluators within the savings budget. Even at the point 2 in GF(3), the product for a binary list C(i) is (−1) to the number of zeros. For K=2ᵏ with k≥1 this gives the parity of the number of satisfying assignments of the row circuit C. A short circuit evaluating a single row supplies no known fast exact procedure for that product merely from an ordinary decision-SAT time bound. Interactive product verification instead requires a prover message before a fresh challenge. An accepting transcript with existentially guessed challenges does not inherit its soundness.

## What happens if the simulator distributes a proof of each product across SAT calls?

Consider an exact local-checking scheme. An input X has K independent bit positions as its domain of access, and the prover may guess a shared proof. Check family j receives hⱼ fixed proof bits, called its header. Different families can share any of those bits. Given its header, the family passes if **every** challenge in its index set accepts. Each challenge can adaptively read at most qⱼ input bits. Its remaining computation and the number of challenges are free. Acceptance means some single proof makes every family pass. Header positions are fixed within each family. A RAM lookup into an arbitrarily long free proof would be a different interface. Families with qⱼ=0 can be retained for proof-only conditions and omitted from the bounds below.

**Distributed parity bound.** For exact recognition of even parity, either some qⱼ≥K, or

    Σⱼ hⱼ qⱼ / (K−qⱼ) ≥ 1.

In particular Σⱼ(hⱼ+qⱼ)² ≥ (2√K−1)². The single-family width tradeoff follows already from the satisfiability coding lemma, as applied explicitly to parity encodings by Emdin and colleagues. The calculation below tracks separate, overlapping proof headers and different probe widths. Priority of this distributed formulation is undetermined. [Paturi, Pudlák and Zane](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/PaturiPudlakZane_1999_cjtcs.pdf) · [Emdin, Kulikov, Mihajlin and Slezkin](https://arxiv.org/abs/2203.01082)

Choose X uniformly among even strings and fix any valid proof as a function of X. Mark i for family j if changing only Xᵢ makes that family fail with its chosen header. Write dⱼ for the number marked. Every coordinate must be marked somewhere because the changed input has odd parity.

To bound E[dⱼ], order the K coordinates by a uniformly random permutation, independently of X. For each marked i choose one rejecting path on the altered string. That path must inspect i. Its queried variables define a forbidden partial assignment on at most qⱼ positions. If all its other positions precede i, then among strings passing family j with the fixed header and the previously decoded bits, only Xᵢ is possible. This forcing event has probability at least 1/qⱼ. Its probability with i outside the last position is at least 1/qⱼ−1/K.

For each fixed order, encode the header followed by the successive bits in the first K−1 positions, omitting a bit whenever only one value has a passing completion for the current header and prefix. The decoder can determine this condition by an unlimited search. Infer the last bit from parity. The resulting code is prefix-free because decoding knows when those K−1 positions are complete. Uniform even strings have entropy K−1. Averaging the code length over X and the order consequently gives

    hⱼ ≥ E[dⱼ] (1/qⱼ−1/K).

Summing the resulting bounds on E[dⱼ] proves the claim. For the quadratic estimate, use the following algebraic fact for any D≥1. If Σ hⱼqⱼ/(D−qⱼ)≥1 with 0<qⱼ<D, put L=2√D−1. If some hⱼ+qⱼ≥L we are done. Otherwise write m=hⱼ+qⱼ and θ=qⱼ/m. From (Lθ−√D)²≥0 we get L²θ(1−θ)+Lθ≤D. Since qⱼ≤Lθ, we have hⱼqⱼ/(D−qⱼ) ≤ m²/L². Sum to obtain Σm²≥L². A qⱼ≥D alone also costs at least L², since D≥2√D−1.

For K=a² the bound is attained with one family, q=a and h=a−1. Split into a blocks of a bits, guess the block parities except for the last (inferred from even target parity), and let each challenge check one whole block.

## A direct lower bound for equality of binary record multisets

The product example computes more than a yes/no multiset equality test. To attack equality itself, fix the target multiset to K/2 zeroes and K/2 ones, K even and positive. Write D=K/2+1. For a scheme in the same local model, either some qⱼ≥D, or

    Σⱼ hⱼ qⱼ / (D−qⱼ) ≥ 1.

Thus Σⱼ(hⱼ+qⱼ)² ≥ (2√(K/2+1)−1)². The bound uses exact equality on all input vectors. Treating the bits of a uniform fixed-weight string as independent would give an incorrect proof.

**Proof.** Choose X uniformly on the middle slice and fix its valid proof. Mark dⱼ coordinates using single-bit changes as above. Now pair the K/2 ones with the K/2 zeros by a uniform random bijection. Conditional on the resulting *unoriented* perfect matching, the orientations of its K/2 pairs are independent uniform bits: all 2^(K/2) compatible strings have the same joint probability with this matching.

For each marked i choose its rejecting path on the single-bit change before choosing the matching. Its mate is uniform among the K/2 coordinates with the opposite bit. The path reads i and at most qⱼ−1 others. With probability at least 1−(qⱼ−1)/(K/2), the mate is absent and changing both paired coordinates follows the same rejecting path. Thus a marked i yields a forced-orientation candidate with this probability. At most two marked coordinates count the same orientation. For a fixed matching the resulting rejection trace reads at most qⱼ orientation bits, regardless of which original data bits it asks about.

Encode the K/2 uniform orientations with the family header and the same random-order forcing rule. Here the full set of orientation bits is independent and no final parity bit is omitted. Conditional on a matching, if c orientations admit a rejecting single-orientation flip, their expected savings over the ordering are at least c/qⱼ. The average length cannot go below K/2, even though the header depends on X. Averaging over matchings gives

    hⱼ ≥ E[dⱼ] (1−2(qⱼ−1)/K) / (2qⱼ).

Again every coordinate is marked by at least one family, since changing its bit leaves the slice. Summation and the algebraic fact with D=K/2+1 prove the displayed inequalities.

The order Θ(K) of the quadratic budget is attainable. Use a balanced binary tree with leaves the input bits, padding to a power of two with fixed zeroes. Guess each node's exact subtree count. Verify leaves and one parent-child sum per family and pin the root to K/2. At height ℓ a check needs O(ℓ+1) header bits and there are O(K/2^ℓ) such checks. The sum of squared widths, including the proof-only checks, is O(K). The same construction works with any fixed power in place of two and has O(K) total proof length.

## Consequence for the proposed simulation

If query j in a SAT reduction explicitly embeds hⱼ header bits and separately unrolls qⱼ oracle probes so its charged length is Ω(hⱼ+qⱼ), the guarantee Σmⱼᵈ for d=2 or 3 cannot give o(K) for this generic ledger check. This is a lower bound on the *budget inferred from the assumed SAT clock in the stated reduction*. The actual SAT algorithm might run faster on special queries. Gate-level access to a succinct row generator or a proved restriction on its possible outputs also evades this black-box model.

**Retest on the real RAM record format.** Chronological rows have unique timestamp keys 0,…,T−1. A more specialized interface immediately escapes the middle-slice example. Given oracles for both tables, one universal test checks range and distinctness of the sorted table's timestamps by reading two rows. Another compares the record of sorted row j with the chronological row at its timestamp by two adaptive probes. Together these imply multiset equality of the timestamped records, without a computed product. The unresolved cost is evaluating the second probe inside a short SAT query when its target block depends on the first probe's contents. Flat explicit selection among B distinct s-gate block circuits can cost order Bs per selected row; separating by possible source and destination block pairs can require B² families. Neither charge is an intrinsic lower bound. This identifies a narrower target for a positive simulation: certify random access across independently compressed blocks with sublinear total SAT-query budget, or exhibit a verifier whose routing needs few such joins.

**Checks.** Lean 4.19 verifies adaptive path invariance and the rejecting-swap implication in `BatchProbe.lean`. The coding and averaging arguments are on paper. `python3 batch_probe_experiment.py` exhausts all header assignments of 0, 1, and 2 bits on four-bit even strings and on four-bit middle-slice strings for probe widths 1 and 2. For each header class it uses the strongest admissible local tests, rejecting a tuple exactly when some q-position restriction is absent among class members. This captures every adaptive depth-q rejecting path. For h=1 and q=2, some header map marks all four coordinates on average for either target. For the middle slice with h=2 and q=1 the maximum is 8/3.

## Timestamped transpose routing at the block level

The two-probe escape above treats the choice of a block as free. For a complementary experiment, make the routing entirely explicit in advance and charge which whole blocks a SAT instance mentions. Consider B² chronological records. At step iB+k the machine writes payload Xᵢₖ to address k, where 0≤i,k<B. Its address-ordered list places the same payload at position kB+i with timestamp iB+k. There is no data-dependent choice of address. In the reconciliation subproblem, one side presents source blocks (rows of X), the other presents destination blocks (columns of a separately claimed matrix Y). These are complete, uniquely timestamped candidate lists. Equality of the two lists as multisets is exactly X=Y. The claim concerns this reconciliation interface even when the accepted data values can be arbitrary nondeterministic bit choices of the normalized source machine.

**Fixed-scope bound.** For each family a fix source and destination block sets Rₐ,Cₐ and a set Hₐ of bits in a shared existential proof. Given those blocks and header bits, it may run any test, including a universal family of computations with adaptive accesses inside that scope. Require exactness on arbitrary matrix pairs. Put rₐ=|Rₐ|, cₐ=|Cₐ| and hₐ=|Hₐ|. Then

    B² ≤ Σₐ rₐ(cₐ+hₐ),       B² ≤ Σₐ cₐ(rₐ+hₐ),
    Σₐ(rₐ+cₐ+hₐ)² ≥ 4 B².

The square bound is exact. One global family can inspect all 2B blocks. Alternatively B² families can each see one row and one column. Both constructions charge 4B².

**Proof.** Fix i, set the entries outside row i on each side to zero, and let Alice hold source row x and Bob hold the claimed destination bits y₀,…,y_{B−1} from this row. Define Nᵢ=∪{Cₐ : i∈Rₐ} and Hᵢ=∪{Hₐ : i∈Rₐ}. A certificate supplies |Hᵢ| bits. Bob supplies y restricted to Nᵢ. Alice checks every family with i∈Rₐ, since its other source rows are zero and its destination inputs are now known. Bob checks that there exists a consistent extension of the header passing all remaining families. He can do this by unbounded local search. Acceptance on both sides is exactly x=y.

For a fixed header and fixed communicated substring of y, the pairs giving acceptance form a rectangle. Bob checks that the supplied substring equals the actual substring. A rectangle contained in equality contains at most one diagonal pair, by crossing the two inputs of any two distinct pairs. Thus 2^B diagonal pairs need at least 2^B choices of transcript, giving B≤|Nᵢ|+|Hᵢ|. Summing over i proves the first inequality. Exchanging source and destination gives the second. Finally 4rₐ(cₐ+hₐ)≤(rₐ+cₐ+hₐ)². This uses the elementary equality fooling-set argument; priority of the stated accounting for overlapping headers is undetermined.

More generally give each cell its own payload length wᵢₖ. Fix the payloads on Nᵢ to zero and vary the remaining row bits. The same argument gives

    Σ_{k outside Nᵢ} wᵢₖ ≤ |Hᵢ|.

In particular a proof-free checker has to cover *every* crossing (i,k) with some family mentioning both blocks. This last claim already holds under the promise that each input matrix has at most one nonzero bit. If a crossing is uncovered, the matched zero pair and the matched pair with a pulse at that cell force acceptance of the crossed unequal pair family by family. All of these individual blocks have O(log B)-gate offset circuits.

For nonzero proof length the unrestricted cardinality bound uses arbitrary row data. Under an s-gate promise, the same rectangle argument bounds |Hᵢ| below by the logarithm of the number of different allowed source rows vanishing on Nᵢ whose corresponding destination columns are also legal. For example, set at most t pulses among the B−|Nᵢ| missed columns, at cost O((t+1)log B) source gates by comparison to a hardwired list. Each destination column has at most one pulse. This yields a lower bound log₂ Σ_{l=0}^{min(t,B−|Nᵢ|)} binom(B−|Nᵢ|,l) for the total header accessible on that row. It does not restore the unrestricted B-bit entropy when s is small. The bound also assumes fixed scopes, with all proof data capable of influencing a family's decision included in its header. It leaves open adaptive construction of the SAT queries from descriptions of the block circuits. For the earlier parameters T≈n¹² and B≈n⁴, even B² alone is o(T). Any application at those parameters would need to account for the additional per-query cost of subcircuits and for the much longer individual blocks.
