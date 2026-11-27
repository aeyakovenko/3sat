# Exhausting two-ALU leaves with two comparisons and indirect loads

The subsequent full census establishes a global optimum of nine in this finite model with arbitrary addressing. [Complete theorem and replay](exact-nine-step-clock-for-four-sat-words.md)

At the eight-step deadline, a path on one of the 64 complementary four-word SAT files must read four distinct original data cells before any first overwrite. A two-comparison path with two ALUs therefore performs exactly four loads and no stores. Every path with fewer ALUs or with direct addressing already satisfies the needed 18-target support cap. The remaining two-comparison work is a finite set of 14 genuine indirect layouts. [Marked-leaf criterion and low-arithmetic cases](marked-leaves-and-high-word-lookups.md) · [Direct-addressed paths](nine-steps-for-direct-addressing-on-four-sat-words.md)

On every target all four original columns are high. A fresh load on that file cannot use a previous load's result as its address. Its operand must be a literal low cell or one of the two prior ALU results. One result cannot address two fresh loads on the same file. Remove unused moves and move direct loads to the beginning. Keep the order of the arithmetic operations and perform each load through an arithmetic result immediately after computing it. No write intervenes. The comparison outcomes may be collected at the end of the fixed path. These changes preserve the word values on **every** input, including low-word inputs. They only rename registers and move computations before actions independent of them.

With one indirect load, pick the omitted direct input column and which ALU addresses it. This gives eight layouts. With two indirect loads, choose the two direct columns. Both ALUs supply addresses of fresh reads. All six choices of the direct pair are included. On every covered target the two dynamic addresses must be distinct and absent from the direct set. Across different targets their order is allowed to change. A fixed assignment of the two addresses to physical columns across all targets would wrongly remove admissible paths.

For each layout enumerate the two native operations on all available raw words, earlier results and literals. For each terminal conjunction enumerate equality, unsigned and signed order in either direction, and both outcomes of each guard. If the second resulting load is fresh, that load's value must appear in a terminal comparison, since there are no further arithmetic operations. If the second ALU has no following load, a path using neither its value nor a comparison against it belongs to the already bounded one-ALU case. The worker applies this last pruning only for support thresholds greater than eight. The census tests support against 64 target bits and applies the pointwise freshness conditions. Any apparent separating conjunction is challenged with all 58,976 negative native inputs.

Each workload selects a half-open interval of first-ALU table indices in one layout. Shared first-stage tables agree on the 64 targets and all negative files. In one fixed first stage, a second result table that has no candidate on the fast examples can be skipped on subsequent occurrences of the same table there. A fast answer permitting a candidate triggers full-input checks of **each actual** second computation and both concrete comparison predicates. The 14 layouts contain 11,258 first-stage tables in total across their distinct register sets. The runner checkpoints every completed interval, preserves the binary fingerprint and independently replays any surviving path. [Native enumerator](two_alu_indirect_leaf_census.cpp) · [Resumption and independent path checking](indirect_leaf_campaign.py)

A control in the layout omitting column $P$, using $Q\mathbin{\&}N$ as the first computed address, found a universally sound path covering eight targets. Python independently checked all 65,536 input files. The same first-stage shard, challenged at support 19, exhausted 1,732 second tables. Of those, 67 had some predicate pair surviving the fast check. All 726 concrete full-input predicate tests failed. The production census subsequently exhausted **all 11,258 first tables** across the 14 layouts. A separate interval check verified that the 708 completed ranges are disjoint and cover every index of each layout. Of the first tables, 5,399 passed the immediate freshness filter. The worker examined 6,376,321 second-stage tables and tested 12,059 concrete comparison pairs that passed the quick screen. None covers 19 of the targets and rejects every negative input. Therefore every eight-step accepting path with two comparisons, including arbitrary native data addresses, has support at most 18 on the 64-target family. The remaining obstruction to the nine-step worst-case lower bound is at one comparison.

Compile the worker with `c++ -O3 -std=c++20 two_alu_indirect_leaf_census.cpp -o /tmp/sat-indirect-leaves`. Run the controls using `OPENBLAS_NUM_THREADS=1 python indirect_leaf_campaign.py --binary /tmp/sat-indirect-leaves --selftest`. Run or resume the 14-layout census using the same command with `--state /path/to/external-state --seconds 3600` in place of `--selftest`. The remaining one-comparison cases use two or three ALUs; this workload does not address them.

## Completed native census

Each row gives the direct-address mask and the positions of the arithmetic results used as addresses. The disjoint first-stage intervals cover the full range of each layout. The last column counts predicate pairs reaching the concrete negative-input check.

| Direct mask | Access mask | First tables | Intervals | Fresh first tables | Second tables | Full predicates |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 3 | 607 | 38 | 12 | 13363 | 0 |
| 5 | 3 | 607 | 38 | 143 | 156996 | 0 |
| 6 | 3 | 607 | 38 | 216 | 238411 | 0 |
| 7 | 1 | 952 | 60 | 1 | 1330 | 0 |
| 7 | 2 | 952 | 60 | 952 | 1100407 | 981 |
| 9 | 3 | 607 | 38 | 161 | 178505 | 0 |
| 10 | 3 | 607 | 38 | 226 | 250739 | 4 |
| 11 | 1 | 952 | 60 | 7 | 10476 | 20 |
| 11 | 2 | 952 | 60 | 952 | 1101062 | 283 |
| 12 | 3 | 607 | 38 | 291 | 323545 | 1788 |
| 13 | 1 | 952 | 60 | 199 | 296116 | 1733 |
| 13 | 2 | 952 | 60 | 952 | 1100313 | 2408 |
| 14 | 1 | 952 | 60 | 335 | 505327 | 2873 |
| 14 | 2 | 952 | 60 | 952 | 1099731 | 1969 |
| Total | | 11258 | 708 | 5399 | 6376321 | 12059 |
