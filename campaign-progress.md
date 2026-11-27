# Twelve-hour search for a native SAT time lower bound

This branch records measured progress on 27 November 2026. The first target is an unconditional exclusion of linear deterministic time for ordinary encoded SAT on a logarithmic-word RAM with unrestricted workspace. The quadratic and cubic targets remain in scope.

The mathematical rounds started at 2026-11-27 02:32:50 UTC. The scheduled minimum end is 2026-11-27 14:33:50 UTC. The independent finite census started at 2026-11-27 02:39:55 UTC, with its own minimum window through 2026-11-27 14:40:55 UTC.

The census examines all 65,536 inputs of a particular four-word selector encoding. It searches for a short accepting transcript on a specified base file. A refuted opcode sequence has a checked finite refutation. A separating path can decide that base quickly while other branches take longer. An individual shape, a single-base path, and a complete lower bound for ordinary SAT have different quantifiers. [Model and replay instructions](exhausting-a-seven-step-native-sat-transcript.md)

| Observed UTC | Completed math notes | Math round | Four-word base | Step deadline | Shapes refuted at that base/depth | Verified paths there | Services (math / census) |
|---|---:|---:|---|---:|---:|---:|---|
| 2026-11-27 02:45:38 UTC | 0 | 1 | 4488 | 7 | 121 / 154 | 0 | active / active |
| 2026-11-27 03:47:25 UTC | 2 | 2 | 1184 | 7 | 102 / 154 | 0 | active / active |
| 2026-11-27 04:48:47 UTC | 3 | 4 | 11C4 | 7 | 90 / 154 | 0 | active / active |

## Completed finite searches

- Base 1122, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 64 of 154.
- Base 1124, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 98 of 154.
- Base 1126, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 9 of 154.
- Base 1128, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 8 of 154.
- Base 112A, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 112 of 154.
- Base 112C, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 7 of 154.
- Base 112E, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 102 of 154.
- Base 1142, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 57 of 154.
- Base 1144, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 96 of 154.
- Base 1146, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 92 of 154.
- Base 1148, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 103 of 154.
- Base 114A, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 90 of 154.
- Base 114C, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 8 of 154.
- Base 114E, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 9 of 154.
- Base 1162, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 56 of 154.
- Base 1164, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 89 of 154.
- Base 1166, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 61 of 154.
- Base 1168, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 7 of 154.
- Base 116A, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 97 of 154.
- Base 116C, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 108 of 154.
- Base 116E, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 97 of 154.
- Base 1182, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 56 of 154.
- Base 1184, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 108 of 154.
- Base 1186, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 112 of 154.
- Base 1188, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 110 of 154.
- Base 118A, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 117 of 154.
- Base 118C, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 109 of 154.
- Base 118E, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 117 of 154.
- Base 11A2, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 56 of 154.
- Base 11A4, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 100 of 154.
- Base 11A6, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 117 of 154.
- Base 11A8, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 109 of 154.
- Base 11AA, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 94 of 154.
- Base 11AC, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 118 of 154.
- Base 11AE, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 118 of 154.
- Base 11C2, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 56 of 154.
- Base 1248, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 2 of 154.
- Base 4488, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 127 of 154.
- Base 8421, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 8 of 154.
- Base CC33, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 105 of 154.

## Independent checks of the eight-step question

At base 5488 the instruction-by-instruction verifier has refuted 154 of 154 seven-step shapes; it has found 0 separating paths. The separate finite case analysis and bit-sliced enumeration are recorded in the main journal. [Finite proof and executable tests](https://github.com/aeyakovenko/3sat/blob/main/eight-steps-on-one-four-word-sat-input.md)

The eight-step shared-program search (four initial direct loads) has 60 test files, 21 independently refuted parameter regions, and 27 still open. It has made 86 calls. Its most recent outcome is split-inconclusive.

The eight-step shared-program search (unrestricted prefix) has 33 test files, 0 independently refuted parameter regions, and 51 still open. It has made 59 calls. Its most recent outcome is split-inconclusive.

## Coupled finite accepting leaves

The independent layout census has completed 11,258 of 11,258 first-operation tables across 14 layouts. It tests eight-step, read-only native paths with four fresh loads, two arithmetic operations and two comparisons. It asks whether a single sound accepting path covers at least 19 of 64 specified satisfiable files. Its state is exhausted and its service is inactive.

## Residual one-comparison search

Four disjoint native partitions test support of at least 37 of the 64 complementary inputs at an eight-step deadline. The store case checks a necessary certificate obtained by erasing a write. The two read-only cases test actual accepting paths. The numbers below count covered pairs of first-operation tables and syntactic second-operation choices. A completed pair includes its terminal guards and, where applicable, third operations.

| Family | Refuted pairs | Assigned pairs |
|---|---:|---:|
| Erased store | 53,388,160 | 53,388,160 |
| Final fresh read | 71,627,266 | 71,627,266 |
| Final arithmetic operation | 77,680,300 | 77,680,300 |

## Reviewed mathematics from the run

On the positive four-word input `4488`, a computed address gives a seven-step accepting path. Flipping one bit produces the positive input `5488`, which requires eight steps on the same four-bit RAM by a case reduction and an exhaustive integer computation. This leaves a global eight-versus-nine question on sixteen-bit files. The common-prefix program search is running on two processor cores. [Finite proof](https://github.com/aeyakovenko/3sat/blob/main/eight-steps-on-one-four-word-sat-input.md) · [Common-tree encoding](https://github.com/aeyakovenko/3sat/blob/main/coupling-the-branches-of-the-small-ram-census.md)

For proper DIMACS, there is a short locally checkable certificate with exactly one passing string for each satisfying assignment to the occurring variable names. The corresponding clock argument now only needs a sufficiently short local compiler for uniquely accepting native histories. Constructing it remains open. A compiler with small local interfaces is available on restricted sources. [Canonical certificate](https://github.com/aeyakovenko/3sat/blob/main/a-canonical-short-witness-for-locally-indexed-sat.md) · [Block compiler](https://github.com/aeyakovenko/3sat/blob/main/compiling-native-blocks-from-short-boundaries.md)

The first mathematical round gave a lower bound on actual operations after the final physical SAT word is first read, on an aligned single-memory RAM. A near-linear prefix still leaves a charge of order log N / log log N on both files of a one-bit pair, even allowing pure pointer following at no charge. One correctly implemented SAT solver takes O(N) on this family. [Proof, model and upper bound](https://github.com/aeyakovenko/3sat/blob/main/processing-butterfly-queries-after-the-last-physical-word.md) · [One-address and one-payload counterexamples](https://github.com/aeyakovenko/3sat/blob/main/one-overwritten-address-after-the-last-sat-word.md)

At growing proper-DIMACS lengths there is a single one-bit opposite-verdict pair on which every member of a polynomial roster incurs Ω(N/log² N) marked non-load processing after data-only prefixes, with unrestricted prefix storage and time. Each file also needs every designated original private word read. On this family the underlying static equality queries have a matching O(N/log² N) upper bound after unbounded preprocessing. On a different parity family with many ordinary words still unread at the cut, the processing bound is Ω(N/log N) and a globally correct program takes O(N/log N) steps on all those files. [Common-roster proof](https://github.com/aeyakovenko/3sat/blob/main/a-common-sat-pair-for-a-growing-program-roster.md) · [Matching static ceiling](https://github.com/aeyakovenko/3sat/blob/main/the-static-ceiling-for-equality-encoded-as-sat.md) · [First-query processing](https://github.com/aeyakovenko/3sat/blob/main/unseen-ordinary-words-after-the-first-query-packet.md)

The four-word direct-addressing global optimum is nine. The native indirect census completed all 11,258 first tables in 708 disjoint intervals, eliminating overlarge two-comparison accepting leaves. One-comparison cases remain in the eight-versus-nine question with arbitrary addressing. Separate research on finite core identification produced the sharp entropy constant (log₂ 10)/12 and a globally correct scan-time counterexample to the proposed extrapolation. [Indirect census results](https://github.com/aeyakovenko/3sat/blob/main/exhausting-two-alu-indirect-accepting-leaves.md) · [Remaining finite shapes](https://github.com/aeyakovenko/3sat/blob/main/one-comparison-after-the-last-fresh-word.md) · [Core counting and clock](https://github.com/aeyakovenko/3sat/blob/main/the-cost-of-identifying-a-normalized-sat-core.md)

One mixed decimal identifier per database/query coordinate improves the roster charge from Ω(N/log² N) to Ω(N/log N), in addition to all original private reads. The same pair incurs graded costs at every prefix with sufficiently many query words still absent. Both extremes are explained by a sharp static trade-off in the number of boundaries between data-owner and query-owner bytes. At just one physical boundary even an arbitrarily long split variable name has a short rolling-hash summary. All actual inputs in the new scan-scale family admit a globally correct O(N/log N) native fast path. [Native pair and exact model](https://github.com/aeyakovenko/3sat/blob/main/a-common-sat-pair-with-a-name-across-each-word-boundary.md) · [All-prefix theorem](https://github.com/aeyakovenko/3sat/blob/main/graded-prefixes-of-a-packed-equality-file.md) · [Number of input boundaries](https://github.com/aeyakovenko/3sat/blob/main/equality-with-boundedly-many-switches-of-input-ownership.md)

The four-word native clock has now been settled at exactly nine. For each correct program, at least one of 64 fixed positive cases needs nine steps, with arbitrary program size and computed addresses and no deadline on negative cases. The upper program decides all 65,536 cases. The joint bound uses a marked rejecting path and the exhausted capacities of each accepting leaf. Two separate compiler builds, using different input orders, agreed on the two large kernels. Lean checks the upper program, store-erasure lemma, and tree arithmetic. [Mathematical proof, receipts and replay](https://github.com/aeyakovenko/3sat/blob/f77c51942f0f0a1884718f9e20187d4c55cb0133/exact-nine-step-clock-for-four-sat-words.md)

For a compact proposed positive clock history, a constant number of hashed layouts can serve all authenticated polylogarithmic adaptive challenges. A physically emitted defect formula of size O(D+M/log(2+M)+u+√s) follows under the stated sparse-presentation hypothesis. A uniformly short faithful presentation for arbitrary accepting RAM runs remains missing. [Formal parameters and finite tests](https://github.com/aeyakovenko/3sat/blob/24e5b8c8faa327f10691c1d0a8fc3323012f1d79/compact-verification-of-a-rare-accepting-presentation.md)

The latest four-word census strengthens the worst case to a cohort. Every one correct program takes at least nine instructions on at least 28 of the 64 selected positive files. A separate verification reconstructed all 215 CNFs covering the 154 native opcode shapes for the seven-instruction test on 5488. An external checker accepted all 6,189,437,324 LRAT proof bytes. The 91 regenerated proofs matched the recorded fingerprints. [Cohort theorem and recurrence](https://github.com/aeyakovenko/3sat/blob/ab527976a49e0f98b30e2fb172aa24c2e0275c2c/which-four-word-sat-targets-finish-in-seven-steps.md) · [Independent symbolic verification](https://github.com/aeyakovenko/3sat/blob/ab527976a49e0f98b30e2fb172aa24c2e0275c2c/eight-steps-on-one-four-word-sat-input.md)

A complete formula with one clause of width k on every k-set gives an algebraic successor that exists on ordinary clauses. On unsatisfiable extensions its polynomial-calculus degree is always k+1 over any field. The covered and uncovered signed hypergraphs on 5–8 variables include explicit answers to two cases left open in the 2021 GraphSAT table. A deterministic logarithmic-word RAM can enumerate every model of a complete Boolean k-CSP in O_k(v^k) native steps and scan order on the related proper packed DIMACS files. Balanced coordinate partitions extend this to a dense 3-SAT promise that permits missing supports. [Algebraic degree and finite certificates](https://github.com/aeyakovenko/3sat/blob/7cc756accac03748fab30cd56310f932c59ebc11/algebraic-degree-of-complete-sat-sign-patterns.md) · [Word-RAM upper bound](https://github.com/aeyakovenko/3sat/blob/80fcbe3aa1d90e51c08815e3ebf4bd08c65fc5a8/complete-csp-in-linear-dimacs-time.md) · [Missing-support theorem](https://github.com/aeyakovenko/3sat/blob/80fcbe3aa1d90e51c08815e3ebf4bd08c65fc5a8/balanced-splits-for-incomplete-clause-triples.md)

Research notes are saved as rounds finish. This ledger reports checkpoints and does not certify a superlinear RAM theorem.
