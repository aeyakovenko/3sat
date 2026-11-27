# Twelve-hour search for a native SAT time lower bound

This branch records measured progress on 27 November 2026. The first target is an unconditional exclusion of linear deterministic time for ordinary encoded SAT on a logarithmic-word RAM with unrestricted workspace. The quadratic and cubic targets remain in scope.

The mathematical rounds started at 2026-11-27 02:32:50 UTC. The scheduled minimum end is 2026-11-27 14:33:50 UTC. The independent finite census started at 2026-11-27 02:39:55 UTC, with its own minimum window through 2026-11-27 14:40:55 UTC.

The census examines all 65,536 inputs of a particular four-word selector encoding. It searches for a short accepting transcript on a specified base file. A refuted opcode sequence has a checked finite refutation. A separating path can decide that base quickly while other branches take longer. An individual shape, a single-base path, and a complete lower bound for ordinary SAT have different quantifiers. [Model and replay instructions](exhausting-a-seven-step-native-sat-transcript.md)

| Observed UTC | Completed math notes | Math round | Four-word base | Step deadline | Shapes refuted at that base/depth | Verified paths there | Services (math / census) |
|---|---:|---:|---|---:|---:|---:|---|
| 2026-11-27 02:45:38 UTC | 0 | 1 | 4488 | 7 | 121 / 154 | 0 | active / active |
| 2026-11-27 03:47:25 UTC | 2 | 2 | 1184 | 7 | 102 / 154 | 0 | active / active |

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
- Base 1248, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 2 of 154.
- Base 4488, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 127 of 154.
- Base 8421, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 8 of 154.
- Base CC33, depth 7. Worker verdict pointwise-certificate. Fully eliminated shapes 105 of 154.

## Independent checks of the eight-step question

At base 5488 the instruction-by-instruction verifier has refuted 150 of 154 seven-step shapes; it has found 0 separating paths. The separate finite case analysis and bit-sliced enumeration are recorded in the main journal. [Finite proof and executable tests](https://github.com/aeyakovenko/3sat/blob/main/eight-steps-on-one-four-word-sat-input.md)

The eight-step shared-program search (four initial direct loads) has 60 test files, 7 independently refuted parameter regions, and 8 still open. It has made 39 calls. Its most recent outcome is split-inconclusive.

The eight-step shared-program search (unrestricted prefix) has 33 test files, 0 independently refuted parameter regions, and 18 still open. It has made 26 calls. Its most recent outcome is split-inconclusive.

## Coupled finite accepting leaves

The independent layout census has completed 7,232 of 11,258 first-operation tables across 14 layouts. It tests eight-step, read-only native paths with four fresh loads, two arithmetic operations and two comparisons. It asks whether a single sound accepting path covers at least 19 of 64 specified satisfiable files. Its state is running and its service is active.

## Reviewed mathematics from the run

On the positive four-word input `4488`, a computed address gives a seven-step accepting path. Flipping one bit produces the positive input `5488`, which requires eight steps on the same four-bit RAM by a case reduction and an exhaustive integer computation. This leaves a global eight-versus-nine question on sixteen-bit files. The common-prefix program search is running on two processor cores. [Finite proof](https://github.com/aeyakovenko/3sat/blob/main/eight-steps-on-one-four-word-sat-input.md) · [Common-tree encoding](https://github.com/aeyakovenko/3sat/blob/main/coupling-the-branches-of-the-small-ram-census.md)

For proper DIMACS, there is a short locally checkable certificate with exactly one passing string for each satisfying assignment to the occurring variable names. The corresponding clock argument now only needs a sufficiently short local compiler for uniquely accepting native histories. Constructing it remains open. A compiler with small local interfaces is available on restricted sources. [Canonical certificate](https://github.com/aeyakovenko/3sat/blob/main/a-canonical-short-witness-for-locally-indexed-sat.md) · [Block compiler](https://github.com/aeyakovenko/3sat/blob/main/compiling-native-blocks-from-short-boundaries.md)

The first mathematical round gave a lower bound on actual operations after the final physical SAT word is first read, on an aligned single-memory RAM. A near-linear prefix still leaves a charge of order log N / log log N on both files of a one-bit pair, even allowing pure pointer following at no charge. One correctly implemented SAT solver takes O(N) on this family. [Proof, model and upper bound](https://github.com/aeyakovenko/3sat/blob/main/processing-butterfly-queries-after-the-last-physical-word.md) · [One-address and one-payload counterexamples](https://github.com/aeyakovenko/3sat/blob/main/one-overwritten-address-after-the-last-sat-word.md)

Research notes are saved as rounds finish. This ledger reports checkpoints and does not certify a superlinear RAM theorem.
