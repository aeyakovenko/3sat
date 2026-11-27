# Twelve-hour search for a native SAT time lower bound

This branch records measured progress on 27 November 2026. The first target is an unconditional exclusion of linear deterministic time for ordinary encoded SAT on a logarithmic-word RAM with unrestricted workspace. The quadratic and cubic targets remain in scope.

The mathematical rounds started at 2026-11-27 02:32:50 UTC. The scheduled minimum end is 2026-11-27 14:33:50 UTC. The independent finite census started at 2026-11-27 02:39:55 UTC, with its own minimum window through 2026-11-27 14:40:55 UTC.

The census examines all 65,536 inputs of a particular four-word selector encoding. It searches for a short accepting transcript on a specified base file. A refuted opcode sequence has a checked finite refutation. A separating path can decide that base quickly while other branches take longer. An individual shape, a single-base path, and a complete lower bound for ordinary SAT have different quantifiers. [Model and replay instructions](exhausting-a-seven-step-native-sat-transcript.md)

| Observed UTC | Completed math notes | Math round | Four-word base | Step deadline | Shapes refuted at that base/depth | Verified paths there | Services (math / census) |
|---|---:|---:|---|---:|---:|---:|---|
| 2026-11-27 02:45:38 UTC | 0 | 1 | 4488 | 7 | 121 / 154 | 0 | active / active |

Research notes are saved as rounds finish. This ledger reports checkpoints and does not certify a superlinear RAM theorem.
