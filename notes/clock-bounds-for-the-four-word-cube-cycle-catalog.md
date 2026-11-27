# Clock bounds for the 16-bit cube-cycle catalog on the four-bit native RAM: at most fourteen, at least eight, and at least nine with literal first reads

This is a finite result about one four-word instance, with no asymptotic content. On the 65,536 one-bank files of the 16-bit cube-cycle catalog, the worst-case native clock T of the four-bit RAM satisfies 8 ≤ T ≤ 14 in the full model and 9 ≤ T ≤ 14 for the programs that read every input cell for the first time through a literal address (class (F) below), which includes the explicit 14-step program. The optimum is not determined. The one-bank predicate has a constant-work-per-word scan at every length (Section 4), so these constants carry no information about superlinear time for SAT, and the linear, quadratic and cubic questions remain open.

## Result

The catalog is the set of 65,536 one-bank files of the shuffled-bank note: a 16-bit mask selects clause labels on the edges of a Hamiltonian cycle of the 4-cube, and the file is UNSAT exactly when `(mask | rotl16(mask,1)) == 0xffff`. There are 2,207 UNSAT masks ("covers"). Input word `i` (memory address `i`) holds mask bits `4i..4i+3`. [Cube-cycle banks](shuffled-four-cube-cycle-banks-in-ordinary-sat.md)

Let T be the worst-case native clock: the minimum over correct programs of the maximum number of executed instructions over the 65,536 inputs.

| Statement | Value | Scope |
|---|---|---|
| Upper bound | T ≤ 14 | explicit program: 4 literal loads, at most 10 comparisons of a word with a literal; no ALU instruction, no store. Verified on all 65,536 masks. |
| Lower bound | T ≥ 8 | **full model** (literal and register-addressed LOAD, STORE, the twenty ALU operations, immediates, both branch outcomes). No REJECT path of at most 7 instructions is sound and non-empty. |
| Lower bound | T ≥ 9 | **class (F)**: all programs of the full model in which, on every cover, each of the four input cells is read for the first time by a LOAD with a literal address. Stores, register-addressed loads of cells that were already read or of cells 4..15, all ALU operations and immediates are allowed. |
| Not covered | 8 steps | programs that on some cover fetch an input word for the first time through a register-addressed LOAD (address computed by an ALU instruction or read back from memory). |
| Pointwise clocks | 2 / 4 / 8 | 61,440 / 1,889 / 2,207 files; the value 8 for covers is exact in the full model. |

So 9 ≤ T ≤ 14 inside class (F) (which contains the 14-step program and every program that only uses literal-address loads) and 8 ≤ T ≤ 14 for the full model. The gap is open; the optimum is not known. The same runs were repeated for the other packing used by an earlier search (address `i` holds bits `12-4i..15-4i`); see Section 3.7.

Status of each claim:

* proved for the full model (exhaustive enumeration plus the manuscript normal-form argument of 3.2): T ≥ 8 and the pointwise values 2, 4, 8;
* proved for the named subclass (F) (same method, plus the erasure lemma of 3.5 and the Lean-checked recurrence): T ≥ 9;
* constructed and verified on all inputs: T ≤ 14;
* observed in search only (exhaustive inside the named families, no statement about other programs): 14 is optimal for the sequential single-word family and for the pair-block family of Section 2 with at most one ALU instruction per pair tree.

These are constants of one four-word instance; Section 4 explains why they carry no asymptotic information.

## 0. Conventions

Machine (from the paragraph "The input begins in data memory…" of the two-word clock note, the tuples `ALU`/`BRANCH` and `primitive` of [clocked_native_path.py](../audits/clocked_native_path.py), and [native_four_bit_planes.hpp](../audits/native_four_bit_planes.hpp)): 4-bit words; 16 memory words; `mem[i]` = input word `i` for `i < 4`, the other twelve words and all registers start at 0; unlimited registers and code; all sixteen literals are immediates. One step each: LOAD `reg <- mem[addr]` and STORE `mem[addr] <- value` with literal or register operands; one ALU operation on two register/literal operands from `and or xor add sub mul shl shr sar shlmod shrmod sarmod rol ror eq lt slt ne ge sge`; one branch on `eq`, unsigned `lt` or signed `slt` of two register/literal operands, either outcome to either label. ACCEPT (satisfiable) and REJECT (cover) are free terminals. A bounded-time program is unfolded into a tree. [Two-word clocks](exact-clocks-for-two-word-sat-inputs.md)

[cube_cycle_native_model.py](../audits/cube_cycle_native_model.py) is an independent scalar implementation of these semantics; it agrees with the journal's `primitive` on all 5,888 table entries (20×256 ALU, 3×256 branch), and the C++ programs compare their tables with a dump of the Python tables at start-up.

```
$ python3 cube_cycle_native_model.py
covers: 2207 SAFE words: (5, 6, 7, 10, 11, 13, 14, 15)
$ python3 cube_cycle_native_model.py --crosscheck clocked_native_path.py
cross-check with clocked_native_path.py: 5888 table entries agree
```

The first command also checks the rotation formula against the 16 assignments of the 4-cube on the reflected Gray cycle for all 65,536 masks.

Structure of the catalog used throughout. A word is SAFE when it has no two adjacent zero bits: SAFE = {5,6,7,10,11,13,14,15}. Write top(w) for bit 3 and low(w) for bit 0. A mask is a cover iff all four words are SAFE and, for every cyclically adjacent pair of words x → y (addresses i, i+1 mod 4), top(x) = 1 or low(y) = 1. Every word of a cover is at least 5, and replacing any word of a cover by 0 gives a satisfiable file (each word is pivotal).

## 1. Pointwise clocks (independent replication)

The pointwise clock of a file is the least number of instructions executed on it by any correct program.

```
$ python3 cube_cycle_pointwise_clocks.py
class A (a word outside SAFE, SAT): 61440
class B (all words SAFE, SAT):      1889
class C (cover, UNSAT):             2207
every word of every cover is pivotal (replacing it by 0 gives SAT)
class A paths: 32 (address, literal) tests, each leaf set is SAT only  -> 2 steps
class B paths: 256 two-word tests, each leaf set is SAT only; every class-B file has one  -> 4 steps
class C paths: four loads and four equality tests isolate one file  -> 8 steps
class B lower bound: 23328 three-step leaf sets (two literal loads + one comparison) tried, 0 are SAT-only and contain a class-B file
one-cell argument: (v at one address, 15 elsewhere) is a cover for every SAFE v
pointwise clocks: A = 2 (61,440 files), B = 4 (1,889 files), C <= 8 (2,207 files)
```

Upper bounds: prepend the displayed tests to any correct program (for instance the program of Section 2) and fall through to it when a test fails; the leaf reached when all tests succeed contains only files with the announced verdict.

Lower bounds, all for the full model.

* Every file needs 2 steps: a path of at most one instruction ends after a comparison of constants or after no comparison, so its leaf receives every input.
* Class B needs 4 steps. Let x be a class-B file and suppose an ACCEPT leaf is reached after at most 3 instructions. Any input that agrees with x on the original cells that x's run reads follows the same path. If the run reads at most one cell, the input equal to x on that cell and 15 elsewhere is a cover (last line of the output). Three cells would need three loads and leave no comparison. With two cells and the orders LOAD, BRANCH, LOAD or BRANCH first, the leaf set depends on at most one word (a branch before any load compares constants), so the one-cell argument applies again. The remaining order is LOAD, LOAD, BRANCH; the second load cannot be addressed by the first loaded word (it is ≥ 5 on x and reads a zero cell), so both addresses are fixed and the leaf set is `{y : cmp(P,Q) = outcome}` with P, Q among literals and the two loaded words. The script enumerates all 23,328 such leaf sets on the full catalog; none is SAT-only and contains a class-B file.
* Class C needs 8 steps: Section 3.3 (no sound non-empty REJECT path with at most 7 instructions).

## 2. Upper bound: an explicit 14-step program

Search class ("sequential family"). Call the words a, b, c, d (addresses 0..3). A word is *constrained* when its predecessor has top bit 0 (its low bit must then be 1). The program loads d and branches once on top(d); then it handles a, b, c in turn, each by a single-word decision tree that knows whether the word is constrained and ends in ACCEPT or reports the top bit of the word; finally it returns to d, knowing top(d) and top(c). Every single-word tree is the optimum of an exhaustive search ([cube_cycle_tree_search.cpp](../audits/cube_cycle_tree_search.cpp), mode `custom … single`) over all trees of comparisons of the word or of ALU results with literals or each other and at most one ALU instruction per path, minimising the worst value of (depth + cost of the continuation). A second variant has no probe and lets the tree for a report (top, low).

```
$ python3 cube_cycle_upper_program.py <pair_solver> <workdir> 1
probe variant: V4 {(0, 0): 2, (0, 1): 2, (1, 0): 1, (1, 1): 2} V3 {(0, 0): 4, (0, 1): 5, (1, 0): 4, (1, 1): 4} V2 {(0, 0): 7, (0, 1): 7, (1, 0): 6, (1, 1): 7} V1 {0: 9, 1: 9} -> worst non-load steps 10
probe: errors 0, worst case 14 steps, histogram {5: 18432, 6: 20480, 7: 640, 8: 384, 9: 14208, 11: 184, 12: 4276, 13: 2618, 14: 4314}
state variant: V4 {(0, 0): 2, (0, 1): 3, (1, 0): 2, (1, 1): 2} V3 {(0, 0): 5, (0, 1): 5, (1, 0): 4, (1, 1): 5} V2 {(0, 0): 7, (0, 1): 8, (1, 0): 7, (1, 1): 7} V1 11 -> worst non-load steps 11
state: errors 0, worst case 15 steps, histogram {4: 4096, 5: 28928, 6: 2560, 7: 512, 8: 11776, 9: 4320, 10: 368, 11: 549, 12: 6939, 13: 4, 14: 405, 15: 5079}
solver calls: 164; probe variant worst 14 (4 loads + 10); state variant worst 15 (4 loads + 11)
```

Here `<pair_solver>` is [cube_cycle_tree_search.cpp](../audits/cube_cycle_tree_search.cpp) compiled as in the rerun script. Allowing two ALU instructions per single-word tree (last argument 2) gives the same result (`solver calls: 164; probe variant worst 14 (4 loads + 10); state variant worst 15 (4 loads + 11)`). The state variant is the plain address-order scan; its histogram is identical to that of an independently built sequential comparison tree with worst case 15, checked with a separate interpreter. The probe-variant program is stored as `cube_cycle_program_14.json` in `audits/` (regenerated identically by the upper-program script). It is checked again by a separate script that uses only the interpreter of the model:

```
$ python3 cube_cycle_verify_program.py cube_cycle_program_14.json
instruction nodes by kind: {'ACCEPT': 97, 'REJECT': 49, 'branch': 145, 'load': 21} | longest path in the tree: 14
packing: word i = mask bits 4i..4i+3
wrong verdicts: 0
worst case: 14 instructions, e.g. masks ['055b', '055d', '055f', '056b', '056d', '056f']
histogram {steps: inputs}: {5: 18432, 6: 20480, 7: 640, 8: 384, 9: 14208, 11: 184, 12: 4276, 13: 2618, 14: 4314}
steps taken on covers: [12, 13, 14]
```

An independent interpreter, run on the same program exported to a separate list format, also gives worst case 14 and the identical histogram. [cube_cycle_verify_program.py](../audits/cube_cycle_verify_program.py)

Shape of the program. Each single-word tree has depth 2 to 4. For an unconstrained word two comparisons suffice for either outcome (`w > 9` then `w ≠ 12` gives top 1; otherwise signed `w > 4` gives top 0); for a constrained word the top-0 outcome {5,7} takes two comparisons (signed `w > 4`, `w ≠ 6`) and the top-1 outcome {11,13,15} three; the dynamic program picks, at each position, the tree whose leaf depths best fit the remaining costs (the table V above). The probe costs one comparison and saves at most one at the end. The optimal trees found use no ALU instruction, so the program consists of four loads and comparisons of a loaded word with a literal.

Why the search stopped at 14 (observed in search, not a proof of optimality). In the sequential family 10 non-load steps is the exact optimum of the dynamic program above. A coarser family that treats (a,b) and (c,d) as blocks, each by an exhaustive two-word tree, gives the same:

```
$ python3 cube_cycle_pair_blocks.py <pair_solver> <workdir> 0
P2 0 0 4
P2 0 1 5
P2 1 0 4
P2 1 1 4
P1 0 9 -> total non-load 10
P1 1 9 -> total non-load 10
```

With one ALU instruction allowed anywhere in each pair tree nothing changes. The second-phase costs stay 4, 5, 4, 4 (`cube_cycle_pair_blocks.py … 1 p2only`), and the first-phase problem for the probe outcome top(d) = 0 is infeasible at budgets 7 and 8:

```
$ pair_solver custom 8 1 <workdir>/problem_pp1_0.txt
mode custom budget 8 max_alu 1 labels: FAIL=222(cost 0) T0=13(cost 4) T1=21(cost 4)
no ALU: INFEASIBLE (4000640 nodes)
root comparison: INFEASIBLE
root ALU candidates (distinct new tables): 589
root ALU: INFEASIBLE (589 candidates exhausted)
```

(the three lines are the three exhaustive stages: comparisons only; a comparison at the root with the ALU instruction somewhere below; the ALU instruction first). The search with an ALU instruction was run only for the probe outcome top(d) = 0; that is enough, because this branch alone already forces a first phase of 9 and hence 1 + 9 = 10 non-load steps for the family.

Two exhaustive facts from the same solver explain the cost of about 2.5 steps per word: deciding "the pair (c,d) is locally fine" (both SAFE and top(c) or low(d)) needs 5 steps in every tree of comparisons and at most one ALU instruction (`pair_solver p2 3 4 1` is INFEASIBLE, `p2 3 5 0` is FEASIBLE; four steps with two ALU instructions are also INFEASIBLE, `p2 3 4 2`), and a strict two-phase program whose first phase is a comparison tree that classifies (a,b) into its four boundary states needs more than 14 steps (`p1 10 0 5 4 5 5` is INFEASIBLE). Faster REJECT paths exist for special covers (Section 3.4: one comparison after three ANDs certifies 225 covers in 8 steps), but no way was found to use them without lengthening other paths.

## 3. Lower bounds

### 3.1 Paths, leaf sets, capacity

A *path* is a sequence of executed instructions together with the outcome of each of its comparisons. Its *leaf set* R is the set of inputs whose run follows it. A REJECT leaf at the end of the path is correct iff the path is *sound*: R contains only covers. The *capacity* of a sound path is |R|. In a correct program the covers are partitioned among the REJECT leaves, so bounds on capacities bound the number of covers a tree of given depth can handle.

[cube_cycle_leaf_capacity.cpp](../audits/cube_cycle_leaf_capacity.cpp) (`leafcap` below) enumerates paths and computes, for each number d of comparisons, the exact maximum capacity of a sound path with at most N instructions. Instructions: LOADlit c, LOADreg p, STORE p q, ALU f p q (operands literal or register; registers in single-assignment form), then d comparison outcomes on pairs of distinct operands, at least one a register.

### 3.2 Why the enumeration is complete

Fix a leaf set R, a number d of comparisons and a step limit. Among all paths with this leaf set, d comparisons and at most that many steps take one with the fewest instructions and, among those, the lexicographically least sequence of data instructions under the key order LOADlit < ALU < LOADreg < STORE (then by fields). It has the following properties; the program enumerates exactly the sequences that have them. For the class (F) runs, where what is counted is not a function of the leaf set alone, the normal form is taken inside the exchange class of the path (Section 3.5).

* N1 (comparisons last). A comparison does not change registers or memory, and registers are never overwritten, so all comparisons can be evaluated after the last data instruction; R is the intersection of their outcome sets. A comparison of two literals or of an operand with itself has a constant outcome and can be dropped (the path gets shorter).
* N2 (liveness, "root rule"). A LOAD or ALU whose register is never used later, and a STORE after which no LOAD follows, can be deleted without changing R. Hence every register is an operand of a later instruction. An ALU instruction uses at most two registers and creates one, a STORE uses at most two, a LOADreg uses one and creates one, a LOADlit creates one, a comparison uses at most two. The search discards a prefix as soon as the unused registers cannot all be consumed by the instructions that still fit (`feasible`), and the d comparisons are generated so that they consume all unused registers.
* N3 (canonical order and exact redundancies). Swapping two adjacent data instructions that commute, with the register names exchanged, does not change R; if the swap puts a smaller key first, the sequence was not minimal. So: a LOADlit never directly follows an ALU or a LOADreg (no memory write in between); adjacent LOADlit addresses increase; a LOADlit never directly follows a STORE with a literal address (different address: they commute; same address: the load is a copy of the stored operand and can be deleted); an ALU never directly follows a STORE; an ALU directly after a LOADreg uses its register; an ALU directly after an ALU uses its register or has a larger descriptor; a LOADreg directly after a LOADreg uses its register or has a larger address operand. A LOADlit of a cell ≥ 4 before any STORE is the constant 0 and a LOADlit of a cell already read by a LOADlit since the last STORE is a copy; both can be deleted.
* N4 (fresh reads). If a cover x is in a sound leaf set, x's run reads every original cell before that cell is overwritten: otherwise changing the unread word to 0 gives a satisfiable input with the same run. So a useful path has at least four LOADs, and for each cover the program tracks which cells it has read; a cover is dropped when an unread cell is overwritten or when the remaining instructions cannot supply its missing first reads. A first read through a register needs a register that holds the missing cell number on that cover; such registers are not results of first reads (those are words of a cover, hence ≥ 5), so, when stores are excluded, each missing one costs a further instruction. When stores are allowed the program charges only one further instruction in total, because a single register-addressed STORE makes LOADlit possible again for all missing cells. In both cases the results of the remaining first reads must be consumed by the other remaining instructions (two each). A prefix on which no cover survives is discarded. In the runs of Section 3.5 (`--exact-steps`) a prefix is also discarded when, for every number d of comparisons it can still end with, the covers that can complete their first reads in time are not more numerous than the capacity already known for d; and with `--fresh-literal` a cover that would read an input cell for the first time through a register is not counted.

Evaluation. Register and memory tables are kept on a fixed sample of 1,024 satisfiable inputs (one-word changes of covers, inputs with all words ≥ 4, arbitrary ones; seed 20261127) and on all 2,207 covers. A candidate (data sequence + comparison set) is dropped if a sampled satisfiable input passes all its comparisons, or if its exact number of covers does not exceed the best capacity found so far for its d. Otherwise it is run by a scalar interpreter on all 63,329 satisfiable inputs and accepted only if none passes; the cover count is recomputed by the scalar interpreter and must agree. The sample is only a filter: it cannot make an unsound path count, and a sound path is never rejected by it.

### 3.3 Seven steps, full model

```
$ leafcap --tables tables.json --max-steps 7 --threads 2
max steps 7, stores on, register-addressed loads on, comparisons 1..3, sample 1024 (seed 20261127), split 5, part 0/1
exact-steps off, exotic-only off, first reads by literal address only off, last store reloaded off, reversed word order off, seeded capacities: 0 0 0 0
prefix pass done: 27704 tasks, 0.6 s
search nodes 46705804 (pruned by N4: 71177731), comparison sets tried 1109037230, passed sample 3659432, enough covers 354962, sound improvements checked 0
RESULT max_steps=7 comparisons=1  capacity(<=7 steps)=0  capacity(<=6 steps)=0
RESULT max_steps=7 comparisons=2  capacity(<=7 steps)=0  capacity(<=6 steps)=0
RESULT max_steps=7 comparisons=3  capacity(<=7 steps)=0  capacity(<=6 steps)=0
elapsed 252.5 s
```

354,962 candidates excluded the whole sample and contained a cover; each of them admits a satisfiable input. **No path of at most seven instructions is sound and non-empty, in the full model.** Consequently every correct program executes at least 8 instructions on every cover: the pointwise clock of each cover is exactly 8 and T ≥ 8. The quoted block is from a rerun on 2 threads; the original run on 12 threads printed the same lines except the thread-dependent elapsed time (42.5 s). An earlier build of the same program, before the pruning by exact cover histograms was added, gave the same result with the same 354,962 verified candidates in 164.6 s on 8 threads; the source of that build is not preserved.

### 3.4 Eight steps, literal loads only (direct class)

```
$ leafcap --tables tables.json --direct --max-steps 8 --threads 12
max steps 8, stores off, register-addressed loads off, comparisons 1..4, sample 1024 (seed 20261127), split 5, part 0/1
prefix pass done: 4980 tasks, 0.0 s
search nodes 116050096 (pruned by N4: 0), comparison sets tried 32056815587, passed sample 43114186, enough covers 2469185, sound improvements checked 9
RESULT max_steps=8 comparisons=1  capacity(<=8 steps)=225  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=2  capacity(<=8 steps)=147  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=3  capacity(<=8 steps)=81  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=4  capacity(<=8 steps)=81  capacity(<=7 steps)=0
elapsed 110.6 s
```

The counters `comparison sets tried`, `passed sample` and `enough covers` vary with thread timing in runs that find improvements, because the pruning threshold is shared between threads (the run quoted above: 32056815587 comparison sets; an independent rerun of the same command: 32054978561); `search nodes` and every RESULT line are reproducible.

Maximum capacity of a sound 8-step path with four literal loads, ALU instructions and comparisons, by number of comparisons:

| comparisons | ALU instructions available | capacity | a path that attains it |
|---:|---:|---:|---|
| 4 | 0 | 81 | `w0>12, w1>12, w2>12, w3>12` |
| 3 | ≤ 1 | 81 | `r=w0&w2; w1>12; w3>12; r==10` |
| 2 | ≤ 2 | 147 | `r=w0&w1; s=w2&r; w3>12; s==10` |
| 1 | ≤ 3 | 225 | `r=w0&w1; s=w2&w3; t=r&s; t==5` |

(`t==5` means every word contains the bit pattern 0101, so every word is SAFE and odd; 225 = 4⁴ − 2·2⁴ + 1.) The first build of the program (before the histogram pruning; 1,333.3 s on 12 threads, 34,693,005,204 comparison sets; source of that build not preserved) gave the same four capacities. The printed paths were replayed with the Python semantics (the tenth path is the hand-written one of 3.6, stored as `cube_cycle_witness_five_comparisons.txt` in `audits/`):

```
$ python3 cube_cycle_replay_paths.py <log of the run above> cube_cycle_witness_five_comparisons.txt
10 printed paths replayed: every leaf set is cover-only and has the printed size
```

### 3.5 Eight steps, class (F): register-addressed loads and stores

Class (F): on every cover, the first read of each input cell is done by a LOAD with a literal address. For a path, count only the covers of its leaf set that satisfy this along the path; for a program in class (F) these are all covers of the leaf.

*Normal form for counted covers.* The counted set is not determined by the leaf set, so the minimal path of 3.2 cannot be chosen among all paths with the same leaf set. Let π have eight instructions and a counted cover. Its leaf set is sound and non-empty, so by 3.3 no instruction of π can be deleted (the result would be a sound non-empty path with at most seven instructions); in particular π contains none of the exact redundancies of N1–N3. Normalise π only by the exchanges of N3, taking the lexicographically least sequence in its exchange class; it has all the properties listed in 3.2 and is therefore enumerated. This sequence is built greedily: always place the smallest instruction whose predecessors (the earlier instructions of π with which it cannot be exchanged, and their predecessors) are already placed. A LOADlit of c can be exchanged with every ALU, every LOADreg, every LOADlit of another cell and every STORE with a different literal address, and it uses no register; so its direct predecessors are STOREs that may write c (and an earlier LOADlit of c, which in an irredundant path is separated from it by such a STORE). Each of these STOREs also precedes, and cannot be exchanged with, every later LOADreg. So when a LOADreg that follows the LOADlit in π becomes available, the LOADlit is available or already placed, and it has the smaller key: a LOADlit that comes before a LOADreg in π still comes before it in the normal form. A STORE that may write c is never exchanged with a LOADlit of c, so their order is that of π. Exchanges do not change register values, so each LOADreg and STORE addresses the same cell on each input as before. Hence a cover whose first read of c in π is a LOADlit, with c not overwritten before it, keeps that first read in the normal form, and the counted covers of the normal form contain those of π. The same applies to the eight-instruction paths (π−S) + comparison of case (b) below.

Every path with a counted cover is replaced by this normal form, which has the same leaf set and at least the same counted covers; the three cases below (no STORE and no LOADreg: Section 3.4; case (a); case (b)) are exhaustive for normal forms.

(a) Paths with a register-addressed LOAD or a STORE, where the last STORE (if any) is followed by a LOAD that can return stored data on a counted cover, i.e. a LOADreg, a LOADlit of a cell ≥ 4, or a LOADlit of a cell that an earlier LOADlit already read. By Section 3.3 such a path with a counted cover has exactly eight instructions in normal form, so only those are enumerated; a LOADreg that reads an unread input cell on a cover removes that cover from the count; the search is started from the direct capacities and looks for anything larger.

```
$ leafcap --tables tables.json --max-steps 8 --exact-steps --exotic-only --fresh-literal --reload --seed-best 225,147,81,81 --threads 12
max steps 8, stores on, register-addressed loads on, comparisons 1..4, sample 1024 (seed 20261127), split 5, part 0/1
exact-steps on, exotic-only on, first reads by literal address only on, last store reloaded on, reversed word order off, seeded capacities: 225 147 81 81
prefix pass done: 26560 tasks, 0.2 s
search nodes 181360928 (pruned by N4: 20746958932), comparison sets tried 75648788, passed sample 14048, enough covers 0, sound improvements checked 0
RESULT max_steps=8 comparisons=1  capacity(<=8 steps)=225  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=2  capacity(<=8 steps)=147  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=3  capacity(<=8 steps)=81  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=4  capacity(<=8 steps)=81  capacity(<=7 steps)=0
elapsed 199.2 s
```

The RESULT lines repeat the seeds: no such path has more counted covers than the direct maxima (`enough covers 0`: no candidate with more covers than the seed of its class excluded the sample, so none reached the verification stage). The run without stores (`--no-store` in place of `--reload`) also ends with `enough covers 0` and the four seeded capacities.

(b) Paths in which every LOAD after the last STORE S = `mem[p] <- q` is a LOADlit of a cell c < 4 that no earlier LOADlit read (ALU instructions may also follow S; the run of case (a) does not contain these paths, because there a STORE must be followed by a LOAD that can return stored data). Let C be the set of these cells (C is non-empty, else S is dead). *Erasure lemma.* Let π−S be the path without S and M = {y : p(y) ∉ C}. (i) On M the runs of π and π−S coincide, because the only instructions that S can affect are later loads of the cell p(y), and all later loads read cells of C. (ii) A counted cover x of the leaf set of π lies in M: its first read of each c ∈ C is one of these later LOADlit instructions and must return the original word. Hence the counted covers of π lie in R(π−S) ∩ M = R(π) ∩ M, which is a set of covers. If p is a literal, M is everything or nothing and π−S would be a sound non-empty path with at most seven instructions, impossible by 3.3. If p is a register, M is the disjoint union of {p ≥ 4} and the sets {p = v}, v ∈ {0,1,2,3} − C, and each part is the leaf set of the sound path (π−S) + one comparison of p with a literal: at most eight instructions, one more comparison, one store fewer, same loads (these paths need not be in normal form; the bound for d+1 comparisons below applies to them through their normal forms). So

  counted covers of π ≤ (number of parts that contain a counted cover) × (bound for d+1 comparisons),

with at most 4 parts, and only the part {p ≥ 4} when p can only hold a word of a cover (p produced by a first literal read) — in particular when the path has no room for an ALU instruction or a further load.

Combining (a), (b) and 3.4 by induction on the number of stores gives, for class (F), the capacity bounds U₄ = 81, U₃ = max(81, 1·81) = 81 (a store plus three comparisons leaves no room for anything else), U₂ = max(147, 4·81) = 324, U₁ = max(225, 4·324) = 1296.

### 3.6 Tree recurrence

Assume a correct program halts within eight instructions on every input and unfold it into the binary tree of its executed comparisons. A REJECT leaf after d comparisons is the end of a sound path with at most eight instructions, so it holds at most w_d covers, with w = (225, 147, 81, 81) in the direct class and w = (1296, 324, 81, 81) in class (F); a leaf after 0 comparisons or after more than 4 comparisons holds none (four loads are needed); and some leaf is an ACCEPT leaf. The marked-tree recurrence of the nine-step note (a subtree holds at most F_d = max(w_d, 2F_{d+1}) covers, one containing an ACCEPT leaf at most E_d = F_{d+1} + E_{d+1}) gives at most F₁ + E₁ covers in total: [Exact nine](exact-nine-step-clock-for-four-sat-words.md) · [Journal recurrence](../lean/EightStepMarkedCapacity.lean)

| class | w₁..w₄ | F₁ + E₁ | covers |
|---|---|---:|---:|
| direct | 225, 147, 81, 81 | 648 + 567 = 1215 | 2207 |
| (F) | 1296, 324, 81, 81 | 1296 + 567 = 1863 | 2207 |

Both are below 2,207, a contradiction. Margins: with w₃ = w₄ = 81 the total stays below 2,207 whenever w₂ ≤ 324 and w₁ ≤ 1639, so the two capacities without a second implementation (147 and 225) are not decisive. What the conclusion really uses is the seven-step exclusion (3.3), w₄ = 81 and w₃ ≤ 162 (both cross-checked for direct paths in 3.7; uniformly, any weights with w₄ ≤ 147, w₃ ≤ 294, w₂ ≤ 588, w₁ ≤ 1176 would do), and, for class (F), that no path with a store or a register-addressed load exceeds these margins (3.5, single engine). [CubeCycleMarkedCapacity.lean](../lean/CubeCycleMarkedCapacity.lean) (Lean 4.19, the journal's proof of the recurrence with the new weights) checks the two instances and the two margin statements (weights 1639, 324, 81, 81 give 2206; weights 1176, 588, 294, 147 give 2205); changing 1215 to 1214, 1863 to 1862 or 2206 to 2205 makes Lean reject the file.

**Theorem (class (F)).** Every correct program in class (F) executes at least nine instructions on some input. In the direct class the bound uses only exact capacities.

This leaf counting cannot give 10: five raw comparisons already certify 135 covers (`w0 > 9, w0 ≠ 12`, the others > 12; the hand-written path in `cube_cycle_witness_five_comparisons.txt` passes the replay script), and 32 leaves of 135 covers exceed 2,207.

### 3.7 Cross-checks

* Independent second implementation for part of the direct class ([cube_cycle_capacity_crosscheck.cpp](../audits/cube_cycle_capacity_crosscheck.cpp): full tables on all 65,536 inputs, bitset intersections, no sampling, no root rule, no canonical order):

```
$ for cfg in "0 1" "0 2" "0 3" "0 4" "1 1" "1 2" "1 3" "2 1"; do crosscheck $cfg 12; done
CROSSCHECK alu=0 comparisons=1 max sound capacity=0 (leaf sets examined 337, 0.1 s)
CROSSCHECK alu=0 comparisons=2 max sound capacity=0 (leaf sets examined 54502, 0.1 s)
CROSSCHECK alu=0 comparisons=3 max sound capacity=0 (leaf sets examined 5630342, 0.2 s)
CROSSCHECK alu=0 comparisons=4 max sound capacity=81 (leaf sets examined 400356837, 12.6 s)
CROSSCHECK alu=1 comparisons=1 max sound capacity=0 (leaf sets examined 58888, 2.2 s)
CROSSCHECK alu=1 comparisons=2 max sound capacity=0 (leaf sets examined 20813408, 2.4 s)
CROSSCHECK alu=1 comparisons=3 max sound capacity=81 (leaf sets examined 3005435977, 70.2 s)
CROSSCHECK alu=2 comparisons=1 max sound capacity=0 (leaf sets examined 2685312000, 435.5 s)
```

  These agree with `leafcap` (0 for everything that fits in seven steps, 81 for four raw comparisons, 81 for three comparisons and one ALU instruction). The classes with two ALU instructions and two comparisons (147) and three ALU instructions and one comparison (225), and all paths with stores or register-addressed loads, have **no** second implementation; for them the evidence is the single engine, the replay of its witnesses, and the agreement of two builds of the engine (before and after the histogram pruning) on all reported numbers.
* Other packing. An earlier CEGIS search stored mask bits 12..15 at address 0. For programs with literal addresses the two packings are exchanged by renaming addresses i ↔ 3−i; for register-addressed memory access they are not obviously equivalent, so the runs were repeated with `--reverse-words`:

```
$ leafcap --tables tables.json --max-steps 7 --reverse-words --threads 12
search nodes 46703614 (pruned by N4: 71176862), comparison sets tried 1108935770, passed sample 3615077, enough covers 314883, sound improvements checked 0
RESULT max_steps=7 comparisons=1  capacity(<=7 steps)=0  capacity(<=6 steps)=0
RESULT max_steps=7 comparisons=2  capacity(<=7 steps)=0  capacity(<=6 steps)=0
RESULT max_steps=7 comparisons=3  capacity(<=7 steps)=0  capacity(<=6 steps)=0
$ leafcap --tables tables.json --direct --max-steps 8 --reverse-words --threads 12
search nodes 116050096 (pruned by N4: 0), comparison sets tried 32060847169, passed sample 39151809, enough covers 2118954, sound improvements checked 9
RESULT max_steps=8 comparisons=1  capacity(<=8 steps)=225  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=2  capacity(<=8 steps)=147  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=3  capacity(<=8 steps)=81  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=4  capacity(<=8 steps)=81  capacity(<=7 steps)=0
$ leafcap --tables tables.json --max-steps 8 --exact-steps --exotic-only --fresh-literal --reload --reverse-words --seed-best 225,147,81,81 --threads 12
search nodes 181360928 (pruned by N4: 20746958932), comparison sets tried 75648498, passed sample 9345, enough covers 0, sound improvements checked 0
RESULT max_steps=8 comparisons=1  capacity(<=8 steps)=225  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=2  capacity(<=8 steps)=147  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=3  capacity(<=8 steps)=81  capacity(<=7 steps)=0
RESULT max_steps=8 comparisons=4  capacity(<=8 steps)=81  capacity(<=7 steps)=0
```

  Same conclusions for that packing: nothing in seven steps (full model), the same direct capacities, no larger class-(F) path (the last four lines repeat the seeds). These three runs are the evidence for that packing. The 14-step program carries over by the address renaming: `cube_cycle_verify_program.py cube_cycle_program_14.json --reverse-words` mirrors both the load addresses and the memory layout, so it reproduces the same runs by construction and is an illustration, not an independent check.

* Independent evidence for part of 3.3 comes from an earlier campaign's depth-7 pointwise censuses of four covers in the other packing (SAT encodings of all 154 opcode shapes over LOAD, STORE, ALU, BRANCH with LRAT proofs). Each ended with `"result":"all-shapes-refuted","checked":154,"total":154`: these four covers have no seven-step recognition path, in agreement with the `--reverse-words` run above, which covers all 2,207 covers. Those runs are not part of the journal and were not replayed.
* An earlier depth-8 shared-program CEGIS search had found no 8-step program (inconclusive splits after 295 and 209 solver calls). Its "direct" prefix class (four literal loads first, then anything) lies inside class (F), so by 3.6 it cannot succeed.

## 4. What this catalog says about growing lengths

Nothing asymptotic. The one-bank predicate is a local cyclic condition: at any length L and word width w, a word x of the mask is fine iff `x | (x << 1) | (top bit of the previous word)` is all ones, so a scan with a constant number of word operations per word (here: load, shift, or, shift of the previous word, or, compare) decides it in O(L/w) steps, and conversely every cover forces all L/w words to be read. The numbers above (between 8 or 9 and 14 instructions for four words, about 2 to 3.5 per word) are constants of this instruction set and of the four-word size; they do not grow faster than the input and carry no information about superlinear time for SAT. The hardness results of the shuffled-bank note concern many banks with unknown positions, not this fixed-position catalog. [Cube-cycle banks](shuffled-four-cube-cycle-banks-in-ordinary-sat.md)

## 5. What is not proved

* The optimum T is not determined: 9 ≤ T ≤ 14 in class (F), 8 ≤ T ≤ 14 in the full model. The upper bound is the optimum of restricted families only (sequential single-word trees with up to two ALU instructions per tree; pair blocks, comparison-only and with one ALU instruction per pair tree), and there is no evidence either way about 10–13.
* Eight steps in the full model: paths in which a cover reads an input cell for the first time through a register-addressed LOAD are not covered. A direct enumeration of that class with the present engine was estimated at tens of CPU-hours and was not run. For such a path, split the covers of the leaf by the cell c < 4 that each such LOAD reads first. On each piece the LOAD can be replaced by LOADlit c plus the comparison `r == c` on its address register, without changing the run. The missing piece is a bound on such leaves (up to three extra equalities, stores allowed) times the number of pieces (up to four per such LOAD). This has not been done.
* The completeness argument of Section 3.2 (normal form, root rule, fresh-read pruning) and the erasure lemma of 3.5 are manuscript arguments. Only the tree recurrence is checked in Lean. An error in a pruning rule would invalidate the lower bounds silently; the partial independent enumeration of 3.7 does not exercise stores, register-addressed loads, or more than one ALU instruction (except the scalar two-ALU check).
* The capacities 147 and 225 and every result of Sections 3.3 and 3.5 rest on one program ([cube_cycle_leaf_capacity.cpp](../audits/cube_cycle_leaf_capacity.cpp)). Neither theorem needs 147 or 225 exactly. The direct-class contradiction holds whenever w₁ ≤ 1639 and w₂ ≤ 324, and the class (F) one whenever the direct and case-(a) capacities for one and two comparisons are at most 1639 and 324 (the marked total is max(w₁, 648) + 567). The values that carry the result are 3.3 and the two 81s, which are cross-checked in the direct class by `crosscheck 0 4` and `crosscheck 1 3`.
* The lower bound 9 cannot be pushed to 10 by leaf counting (Section 3.6); a proof of 10 would need a different argument.
* The numbers in the "(leaf sets examined …)" and "comparison sets tried / enough covers" columns vary slightly between runs with different thread timing (the pruning threshold is shared between threads); the capacities do not.

## Reproducing the checks

From `audits/`, `sh cube_cycle_clock_rerun.sh BUILD_DIR [THREADS]` compiles the three C++ programs into BUILD_DIR and reruns the computations quoted here: Sections 0 (including the comparison with the journal's tables), 1 and 2 (including the two-ALU variant, the pair-block runs and the tree-search feasibility claims), 3.3–3.5 (including the no-store class (F) run), the replay, the reversed-packing runs, the first bullet of 3.7, and finally `lean CubeCycleMarkedCapacity.lean` in `../lean/` (set `LEAN` if `lean` is not on PATH). `ONLY_UPPER=1` stops after Section 2. An earlier version of the script, without `custom 8 1`, `p2 3 4 2` and the two-ALU variant of Section 2, ran end to end in about 21 minutes of wall time on 12 threads (about 237 CPU-minutes), dominated by the eight-step enumerations and `crosscheck 2 1`; the Section 3 blocks are from that run. One pruning test was then added to the tree search (an ALU instruction is not tried when some label present could not afford the two further steps), and Sections 0–2 of the final script were rerun alone (`ONLY_UPPER=1`, about 13 minutes, most of it `pair_solver p2 3 4 2`); the Section 1 and 2 blocks are from that rerun. The final script, and this version adapted to `audits/`, have not been run in one piece. The 14-step program is stored as `cube_cycle_program_14.json` and the hand-written path as `cube_cycle_witness_five_comparisons.txt`, both in `audits/`.

```
python3 cube_cycle_native_model.py
python3 cube_cycle_native_model.py --crosscheck clocked_native_path.py
python3 cube_cycle_pointwise_clocks.py
python3 cube_cycle_verify_program.py cube_cycle_program_14.json
sh cube_cycle_clock_rerun.sh /tmp/cube-cycle-build 12
lean CubeCycleMarkedCapacity.lean
```

The upper-program, pair-block and replay scripts take the compiled tree search, a work directory or a `leafcap` log as arguments; the rerun script supplies them. [cube_cycle_native_model.py](../audits/cube_cycle_native_model.py) · [cube_cycle_native.hpp](../audits/cube_cycle_native.hpp) · [cube_cycle_pointwise_clocks.py](../audits/cube_cycle_pointwise_clocks.py) · [cube_cycle_tree_search.cpp](../audits/cube_cycle_tree_search.cpp) · [cube_cycle_upper_program.py](../audits/cube_cycle_upper_program.py) · [cube_cycle_pair_blocks.py](../audits/cube_cycle_pair_blocks.py) · [cube_cycle_verify_program.py](../audits/cube_cycle_verify_program.py) · [cube_cycle_leaf_capacity.cpp](../audits/cube_cycle_leaf_capacity.cpp) · [cube_cycle_replay_paths.py](../audits/cube_cycle_replay_paths.py) · [cube_cycle_capacity_crosscheck.cpp](../audits/cube_cycle_capacity_crosscheck.cpp) · [cube_cycle_clock_rerun.sh](../audits/cube_cycle_clock_rerun.sh) · [CubeCycleMarkedCapacity.lean](../lean/CubeCycleMarkedCapacity.lean)
