# A 50-instruction program decides the five-slot proof's padded table-index family in linear time, one program per literal order

A fixed program of 50 stored five-slot instructions decides, in linear time, the padded, translated table-index family F5 that the five-slot proof uses (the private-probe theorem's family, in read-only step 3 and the writable row W5), when the tree clauses list their literals in the theorem's displayed order; the other order needs a second program of the same size, with two operands swapped. It takes at most 16.62 steps per file word on the timed files and is correct for every t by a manuscript argument; the finite checks cover t = 5 to 12, with CaDiCaL agreeing on every file it was run on. A 107-instruction dispatcher decides six of the fooling families built so far in linear time, one of them (the periodic sign-edit family) only in its restricted form. The program's stores escape the bound K ≤ 2^{|B|} of W5's lemma, not the private-probe count itself, so there is no contradiction with the five-slot theorem. This is not a time bound for SAT; like the round-five note on [linear-time programs for the fooling families](linear-time-programs-decide-several-five-slot-fooling-families.md), it marks where the fooling-family method stops, and the linear, quadratic and cubic questions remain open. [Private-probe contexts](private-probe-contexts-in-read-only-sat.md) · [Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md)

## Setting

The machine is the journal's separate-operation RAM as run by `five_slot_ram_interpreter.py` and cross-checked by `five_slot_independent_interpreter.py`. Every register starts at zero, and there is no public n or w. The family is that of the [private-probe theorem](private-probe-contexts-in-read-only-sat.md): its encoding, its small-alphabet paragraph and "Moving the pins". The round-five note lists it as not built ("the proof's padded, translated, bounded-alphabet F5"); its program for F5′, the dense-name, unpadded sample of the audit `table_probe_context_audit.py`, is not a decider for it (Section 3).

## 1. The family as built

`table_index_family_generator.py` builds the family as the theorem specifies:
- **Tree.** Variables form a full binary tree of height t, and level j has selector u_j. For each internal node v with children l and r there are the four clauses (u_j ∨ ¬v ∨ l), (u_j ∨ v ∨ ¬l), (¬u_j ∨ ¬v ∨ r), (¬u_j ∨ v ∨ ¬r).
- **Gadget.** a, b and z get short names. Seven clauses forbid every assignment to them except (0,0,0).
- **Pins.** Each pin has the form (±x ∨ a ∨ b). Leaves are pinned to T, selectors to u, and the root to true, so SAT ⇔ T(u) = 1.
- **Names.** Names are aligned. After a leading 1, each of the K index bits is a full word of W−1 zeros followed by the bit. A literal starts on a word boundary with W−2 spaces, the sign byte and the first digit, and a clause ends with the block ' 0\n' padded with spaces. The header declares the all-ones name, which DIMACS permits since it allows unused identifiers.
- **Length and width.** n = 8·⌈C(D+1)2^t t²/8⌉ bits, with C = 96 and D = 1, and w = 16⌈log₂(n+2)/16⌉, which gives w = 32 at t = 5 to 12.
- **Translation.** The selector-pin section is moved by z all-space words, taken from the trailing whitespace, for any 0 ≤ z < L = Θ(n/w); L/(n/w) runs from 0.26 to 0.71.

The theorem leaves some choices open; they are fixed here, and each is a parameter of `build`:
- **Short names.** a, b, z are named 1, 2, 3; a short literal has the same block shape as a long literal's lead block.
- **Literal order.** Literals appear in the order the theorem displays them. The audit writes tree clauses as (u_j, child, v) instead. Within one clause the parent and the child cannot be told apart by sign, since they always have opposite signs, so a decider must assume one order.
- **Numbering.** Heap names, as in the audit (u_j gets index j and heap node i gets index t+i), or a random injective map into K+1 bits.
- **Section order.** Canonical (gadget, tree, leaf pins, root pin, then the z all-space words, the selector pins and the padding); shuffled (all other clauses permuted, with the permuted selector section at a random clause boundary); or scattered, which also scatters the selector pins and is not the proof's family, only a robustness test.
- **Padding.** Optional extra bytes give a partial final word, and an optional final newline. Forced widths 48 and 64 are labelled as forced and use a larger C.

`check_properties` asserts on generated files that the width follows the rule; that no header word has low 16 bits 0x2020 or 0x3020; that length and selector-word addresses are the same across T and u at each z; that two files differing only in u differ exactly in the selector words where the bits differ; that the selector words move by exactly z, and translation changes whitespace only; that the palette is the same for all T, u and z checked; that the journal's validator accepts the file as proper DIMACS 3-CNF; and that CaDiCaL on the parsed bytes equals T(u). `python3 table_index_family_generator.py 5 6 7` and `python3 table_index_family_generator.py 8 9 10` print one such line for each t, among them:

```
{'t': 5, 'w': 32, 'W': 4, 'n': 153600, 'bytes': 19200, 'K': 7, 'L': 1244, 'words': 4800, 'nclauses': 169, 'palette_sizes': [16], 'union_palette': 16, 'cadical_runs': 8, 'sat': 5}
{'t': 7, 'w': 32, 'W': 4, 'n': 1204224, 'bytes': 150528, 'K': 9, 'L': 20076, 'words': 37632, 'nclauses': 651, 'palette_sizes': [16], 'union_palette': 16, 'cadical_runs': 8, 'sat': 2}
{'t': 8, 'w': 32, 'W': 4, 'n': 3145728, 'bytes': 393216, 'K': 10, 'L': 59872, 'words': 98304, 'nclauses': 1292, 'palette_sizes': [17], 'union_palette': 17, 'cadical_runs': 8, 'sat': 4}
{'t': 10, 'w': 32, 'W': 4, 'n': 19660800, 'bytes': 2457600, 'K': 12, 'L': 434116, 'words': 614400, 'nclauses': 5134, 'palette_sizes': [17], 'union_palette': 17, 'cadical_runs': 8, 'sat': 4}
```

The palette, zero included, has 16 words at t = 5 to 7 and 17 at t = 8 to 10, the same for every T, u and z checked. The extra word is in the header: at t ≥ 8 the clause count has four digits, so its newline falls into a word of its own, '\n   '. CaDiCaL agreed with T(u) on all 48 files of these checks.

## 2. The decider `table_index_tree_walk.asm` (50 instructions)

The program parses every clause, keeps name-indexed tables in memory above the file, and evaluates the pinned multiplexer tree.

**Word classes, by the low 16 bits.** 0x2020 is a literal's lead block or an all-space word; the all-space word is recognised as x = (x shl 16) or 0x2020 and skipped. 0x3020 is a clause terminator, 0 the end of the file, and anything else, the header, is skipped. Digit blocks are consumed inside the literal loop; they are the only words with low byte '0'.

**Names.** j starts at 1 and becomes 2j + bit at each digit block, and a short name keeps j = 1. The bit is read as `ltu lead block`: the block 0…00 is below the lead word, which is below the block 0…01, comparing the top two bytes, so no constant depends on W. A three-literal shift register holds (lead word, j) for the clause's literals. At a terminator the clause is classified: a gadget clause has j₁ = 1, a pin has j₂ = 1, and otherwise it is a tree clause.

**Tables.**

| table | contents | cells |
|---|---|---|
| M[H2 + j] ← the pin's lead word | the pin sign of j; H2 is the lead word of the pin's third literal, b | one per pinned name |
| M[F + v] ← the name of u | the selector of internal node v; F = H+ + H− is the sum of the two lead words with first digit 1 | one per internal node |
| M[((F − s) shl 8) + v] ← the child | s is u's lead word in the clause, so the child is filed under the pin word that selects it | two per internal node |

The bases have top bytes 0x32, 0x62, 0x20 and 0x2d at every width, so they are at least 5·2^{w−8} apart. Names satisfy j < 2^{t+4}, and the formula alone forces 2^w ≥ n ≥ 1280(2^t − 1), so the regions are disjoint for every t ≥ 2 and lie above the file, since n/w ≤ 2^w/32 < 2^w/8 − 32.

**Two passes.** Pass 1 fills the tables. In pass 2, at every pin clause (±j a b), the program walks from j: v ← M[((M[H2 + M[F + v]]) shl 8) + v] until v has no selector, and answers NO if the pin word reached differs from j's pin word. Of the pinned variables only the root has children, so the walk from the root ends at leaf u and checks that T(u) equals the root's pin, which is true; from a leaf or a selector the walk stops at once.

Instruction count: word classes 9, literal loop 14, clause class 2, tree clause 7, pin 3, walk 12, end and restart 3; total 50. In each pass the cursor only increases and each word costs at most about 9 steps; each clause adds at most 7 steps, and the walk adds 8 per level at the root only. So the running time is about 2·17·n/w + 8t + O(#pins), which is linear.

**Correctness for every t ≥ 2 with W ≥ 4** is a manuscript argument, re-derived step by step during review: the all-space test holds only for the all-space word; the bit test compares the top two bytes as above; in a tree clause {a2, a3} = {H+, H−}, so F − a1 = flip(s) and the child is filed under the pin word that selects it; the table bases and the bound on names keep the tables disjoint and above the file, so the end-of-file zero word is never overwritten; pass 2 sees the complete tables, with F still holding its pass-1 value and a3 = H2 during a walk. Clause order, translation, numbering and t are never used.

## 3. Runs against T(u) and CaDiCaL

`table_index_tree_walk_test.py` runs a program on generated files against T(u), with both interpreters, which agree on the verdict and the exact step count for every file. The step cap is 40 times the word count. The configurations vary the three section orders and the two numberings; z ∈ {0, 1, random, L−1}; the table (random, the indicator of u, its complement, or random with T(u) forced to 1); extra bytes from 0 to W−1; a final newline or none; and the rule width or forced widths 48 and 64.

```
t=5 files=12 cadical=4  max steps per file word: forced48 10.33, forced64 16.57, rule 16.57  (1s)
t=6 files=12 cadical=4  max steps per file word: forced48 16.62, forced64 10.18, rule 15.75  (3s)
files=24 correct=24 wrong=0
```

With CaDiCaL on every file, `python3 table_index_tree_walk_test.py table_index_tree_walk.asm 7,8 24 1 24` and `… 9,10 12 1 12` give:

```
t=7 files=24 cadical=24  max steps per file word: forced48 15.90, forced64 15.27, rule 15.27  (14s)
t=8 files=24 cadical=24  max steps per file word: forced48 15.45, forced64 15.93, rule 14.96  (33s)
files=48 correct=48 wrong=0
t=9 files=12 cadical=12  max steps per file word: forced48 15.14, forced64 11.56, rule 14.76  (51s)
t=10 files=12 cadical=12  max steps per file word: forced48 14.92, forced64 12.22, rule 14.61  (101s)
files=24 correct=24 wrong=0
```

So at t = 7 to 10 CaDiCaL agrees with T(u), and with the program, on all 72 files, which include shuffled and scattered orders, random names and forced widths. Steps per file word at the rule width are 15.27, 14.96, 14.76 and 14.61, flat in t; the largest over the 96 configuration files is 16.62 (t = 6, forced width 48).

**Every u at small t.** Three tables (a random one, its complement and the parity of u), two order and naming settings (canonical with heap names, shuffled with random names) and z = L−1 or 0, alternating with u, at t = 5 and 6, with both interpreters agreeing on every file; these 576 files were not timed:

```
table_index_tree_walk.asm: every u at t = 5, 6, three tables, two order/naming settings: files=576 correct=576 wrong=0
```

**Literal order.** On tree clauses written in the audit's order (u_j, child, v) the program answers NO on every file, so it is wrong exactly on the satisfiable ones:

```
files=24 correct=8 wrong=16
```

Read in the wrong order, the tree clauses file each node under its child, so the walk from a pinned leaf climbs instead of descending; from any leaf that its parent's selector does not select, the walk reaches the empty cell, v = 0, where M[H2] = 0 differs from the leaf's pin word, and every file has such leaves. The variant `table_index_tree_walk_audit_order.asm`, which differs only in the tree-clause block where two operands are swapped, is correct on 24 of 24 audit-order files and fails the same way on theorem-order files, answering NO on every one. One program for both orders is not built.

**The round-five F5′ program on this family.** The round-five note expected `table_index_lookup.asm` to fail on these files "by the same mechanism but unchecked". `table_index_lookup_on_padded_family.py` checks it: its verdict follows the translation, not T(u), answering YES at z < L−1 and NO at z = L−1 with the same step count on every file of a given t, and it ends

```
table_index_lookup.asm on F5: files=16 correct=4 wrong=12
```

## 4. Where W5's context bound fails for this program

W5's lemma for writable machines covers the schedule x ≠ p, LOAD x ← M[p], a numerical instruction writing p, and STORE M[x] ← x or M[x] ← c, and it needs every STORE destination to lie in a bounded set B, a destination fixed by an original word. This program stores each private reply, a selector pin's lead word, at H2 + j, where j is computed from the pinned name's digit blocks, which follow the sign word; the STORE is made at the clause terminator, and the walk reads the reply back. That store violates the lemma's hypothesis that every STORE destination lies in B. The private-probe count is not contradicted: every STORE lands above the file, so private words keep their original signs, and the contraction applies with written memory counted in the context. What fails is the lemma's upper bound K ≤ 2^{|B|}: in pass 2 every selector probe happens with all t pin words already filed in memory, so a private site can have up to 2^t contexts, which the Ω(2^t/t²) bound permits. There is no contradiction with the five-slot theorem: the program has 50 instructions, and W5 concerns only the five-slot schedule above. This describes the mechanism; it is not a new barrier.

## 5. The dispatcher `fooling_family_dispatcher.asm` (107 instructions)

`fooling_family_dispatcher_build.py` concatenates five deciders, renaming the registers of each (so every component again starts from zero registers) and prefixing their labels: the round-five programs `four_file_four_instructions.asm` (F3), `two_low_bit_count.asm` (F2), `sign_edit_periodic_scan.asm` (restricted F1) and `k_region_pin_table.asm` (F4 and the k-region family), and the walk above. They sit behind an 8-instruction test of word 0: exactly 0x2070 ("p ", at w = 16) sends the file to F3; low three bytes "p␣␣" to F2; byte 6 equal to '2', read by two shifts of 24 so that both shift conventions agree at every w ≥ 32, to F1, whose header is "p cnf 20" at W ≥ 28 (F3, the only family at w = 16, leaves at the first test, before any shift); and anything else to the F5 walk. Two components were changed. The walk gains two instructions: one sets a flag at every pass-1 pin clause, and the other, if the first pass saw no pin, hands over to the pin table. The pin table keeps its name table at Z0 + j instead of P + j, where Z0 is the all-'0' word, so that the first pass's stores on F4 and k-region files, with top bytes 0x13, 0x20, 0x2d, 0x3a and 0x62, cannot meet it (derived, not run); this costs no instruction. Head 8, F3 4, F2 7, F1 8, F5 52 and k-region 28 give 107 instructions.

Each family's harness was run on the dispatcher; the F1/F2, F3 and F5′ harnesses are the round-five ones patched only to take the program name (`sign_edit_and_low_bit_tests_any_program.py`, `four_file_test_any_program.py`, `table_index_lookup_test_any_program.py`):

```
F3 four files: truth [True, False, False, True] verdicts ['YES', 'NO', 'NO', 'YES'] steps [6, 6, 6, 6] correct 4 of 4
prog=fooling_family_dispatcher.asm files=64 correct=64 wrong=0
max steps/N = 0.3646   (N in bits)
prog=fooling_family_dispatcher.asm order=chain files=54 correct=54 wrong=0
prog=fooling_family_dispatcher.asm order=shuffled files=54 correct=54 wrong=0
files=36 correct=36 wrong=0
files=12 correct=12 wrong=0
```

With 60 F1 files and 30 F2 files, all correct, the total is 4 + 60 + 30 + 64 + 108 + 36 + 12 = 314 files, all correct. CaDiCaL gave the truth on the files of every harness; on F5 it was run on 10 of the 48 files and T(u) gave the truth on the rest. On F4 and k-region files the dispatcher first makes the F5 parser's pass and then runs the pin table, so the steps per bit are at most 0.365 and 0.287, at most 23.4 and 18.4 steps per word at w ≤ 64. F5′, the audit's unpadded sample and not a family the proof uses, is not covered: its header "p cnf 266 …" sends it down the F5 path, whose parse does not fit dense names, and the dispatcher is wrong on 14 of its 24 files.

## 6. Independent checks during review

- **Interpreter.** `five_slot_block_interpreter_independent.py` was written during review from the machine definition of the five-instruction note and the 43-instruction note's conventions. It compiles each program into Python basic blocks, computes both shift conventions and reports any disagreement, and it agrees with the journal's interpreter on verdict and steps on 54 of 54 files (three programs, both literal orders). A rerun with the staged scripts, nine files at t = 5 for each program and order through `run_harness_with_independent_interpreter.py` and the test harness, which compares two interpreters file by file, again agrees on all 54 files. It also counts 50, 50 and 107 stored instructions and finds the three programs legal: at most two operands per numerical site, register STORE payloads, register or literal addresses, branches comparing two words, free fixed successors, and terminals not counted.
- **Generator.** `table_index_family_generator_independent.py`, written during review from the theorem's text, produces bytes identical to the generator above on every canonical, heap-named file compared (24 of 24 at t = 5 to 10, and 2 of 2 at t = 11 and 12).
- **Runs.** `table_index_tree_walk_independent_check.py` runs a program with the independent interpreter on the independent generator's files. On 96 files at t = 5 to 10, half satisfiable, it is correct on all 96 with CaDiCaL agreeing on all of them, and at t = 11 and 12 on 8 of 8:

```
table_index_tree_walk.asm lit=theorem variant=plain: files=96 correct=96 wrong=0; generator byte-identical 24/24
```

  Varying choices the family fixes, short names 7, 8, 9, the gadget order (z, b, a), and C = 400, each gives 16 of 16 (at C = 40 the formula does not fit the length). `run_harness_with_independent_interpreter.py` reruns any harness with the independent interpreter in place of the journal's; every dispatcher harness gave the same results, 314 of 314, with the same steps per bit.

## 7. The three standard tests

No lower bound is claimed.
- **(a) A fast, globally correct solver for the family?** Yes: this note is one, at 50 instructions and about 15 steps per word. Unit propagation also decides the family once the three gadget variables are set (the gadget forces a = b = z = 0); from the empty assignment it derives nothing, since every clause has three literals.
- **(b) The same argument for 2-SAT?** Not applicable, since there is no lower-bound argument. The decider is a pinned-circuit evaluator, and deciders of the same kind, name-indexed pin tables, should also decide 2-CNF encodings of pinned-value consistency, as the round-five note remarks; that was not run.
- **(c) The relativized-clock oracle?** Not applicable to an upper bound; with the packed oracle a constant-size program decides SAT anyway. [Relativized clock](relativized-clock.md)

## 8. Exact obstruction and next step

The falsifiable statement "the proof's table-index family keeps fooling" is false at the sizes checked: the proof's F5 falls to 50 instructions in linear time. With it, six of the seven families the journal has built are decided by one 107-instruction linear-time program; the seventh is F5′, the audit's sample, which the proof does not use. So for those six families the linear-time size frontier lies in [4, 107]: 4 is the generic bound, and 107 is checked at finite size. The five-slot theorem's 6 holds only for the full union of the proof's families, several of which are not built.

**Next step.** Build the families of the five-slot proof that are still missing: the parity-pin expander family F6, the arbitrary-stride sign-erasure files F7, the homogeneous base F8, the unary reverse-link base, the placed-site F3 and the re-paired equality files. Each needs a generator, a decider, and then a word-0 test or a hand-over flag in the dispatcher, whose size then bounds the instruction count at which the whole proof's families stop fooling. What a family past that count must defeat is unchanged: a name-indexed memory table plus a constant-depth parse plus a walk of pinned values. Among the built families, F5 was the one whose decision needed adaptive reads of t private bits, and it stops fooling once each bit is filed in memory under its name, which lifts W5's bound on contexts (Section 4).

## 9. What is not proved

- **Correctness for every t.** It is a manuscript argument (Section 2), re-derived during review, with no Lean proof; the finite checks cover t = 5 to 10 here and t = 11 and 12 during review.
- **A promise decider.** The program relies on these choices, all fixed in Section 1:
  - tree clauses list (u_j, v, child), the theorem's displayed order (the variant handles (u_j, child, v));
  - every pin lists its pinned literal first, then two one-word (short) literals;
  - every gadget clause starts with a short literal;
  - terminators are blocks starting ' 0';
  - aligned names in this block format, and W ≥ 4.

  The digits of the short names are not used: short names 7, 8, 9 and the gadget order (z, b, a) each gave 16 of 16 during review. One further condition was added after the review and not checked during it: the third literal of every pin must be the same word, because its lead word is the base H2 of the pin table. The program files each pin sign at a3 + j, where a3 is the lead word of that pin's third literal, and walks with the same base. Writing every selector pin as (±x ∨ b ∨ a), or only the pin of the leaf that u selects, leaves the formula unchanged, and either change makes the program answer NO on every satisfiable file of the check; with the leaf pin swapped, the root's walk reads the leaf's sign under the other base and finds an empty cell (`table_index_tree_walk_third_literal_check.py`):

```
selector pins (x, b, a)      files=12 correct=7 wrong=5, 5 of them satisfiable
selected leaf pin (x, b, a)  files=12 correct=7 wrong=5, 5 of them satisfiable
satisfiable files: 5 of 12
```

  The theorem's pins are all (±x ∨ a ∨ b), so the family satisfies the condition; it narrows the promise, not the family. The program does not rely on clause order, translation, numbering or t.
- **The dispatcher's checks.** On the F1, F2, F4 and k-region harnesses only the journal's interpreter and the independent one written during review were run, not the round-five independent interpreter; that one was run on F3 and F5.
- **Minimality.** For F5 alone the least size lies between 4 (the generic bound) and 50; for the union of the six families, between 4 and 107. The five-slot theorem's lower bound of 6 needs families that are not built here.
- **Lower bounds and targets.** No lower bound on SAT is given, and the linear, quadratic and cubic targets are untouched.

## Reproducing the checks

Run from `audits/`, under an 8 GB memory cap, with TMPDIR set to a temporary directory, since CaDiCaL's wrapper writes temporary files there. With no argument each script runs a short default; the commands below give every run quoted here and the review's reruns, about 9 minutes in all. The last one is the interpreter comparison for one program and order; the other five runs change the program and the last argument.

```
python3 table_index_family_generator.py 5 6 7
python3 table_index_family_generator.py 8 9 10
python3 table_index_tree_walk_test.py table_index_tree_walk.asm 5,6 12 1 4
python3 table_index_tree_walk_test.py table_index_tree_walk.asm 7,8 24 1 24
python3 table_index_tree_walk_test.py table_index_tree_walk.asm 9,10 12 1 12
python3 table_index_tree_walk_test.py table_index_tree_walk.asm 7,8 12 1 4 96 audit
python3 table_index_tree_walk_test.py table_index_tree_walk_audit_order.asm 7,8 12 1 4 96 audit
python3 table_index_tree_walk_test.py table_index_tree_walk_audit_order.asm 7,8 12 1 4 96 theorem
python3 table_index_tree_walk_every_u.py
python3 table_index_lookup_on_padded_family.py
python3 table_index_tree_walk_third_literal_check.py
python3 fooling_family_dispatcher_build.py
python3 four_file_test_any_program.py fooling_family_dispatcher.asm
python3 sign_edit_and_low_bit_tests_any_program.py fooling_family_dispatcher.asm
python3 equality_program_test.py fooling_family_dispatcher.asm 7 64
python3 k_region_family_test.py fooling_family_dispatcher.asm chain 3 54
python3 k_region_family_test.py fooling_family_dispatcher.asm shuffled 4 54
python3 table_index_tree_walk_test.py fooling_family_dispatcher.asm 6,7,8 12 1 2
python3 table_index_tree_walk_test.py fooling_family_dispatcher.asm 9,10 6 1 2
python3 table_index_lookup_test_any_program.py fooling_family_dispatcher.asm
python3 five_slot_block_interpreter_independent.py
python3 table_index_family_generator_independent.py
python3 table_index_tree_walk_independent_check.py table_index_tree_walk.asm 5,6,7,8,9,10 16 16 theorem
python3 table_index_tree_walk_independent_check.py table_index_tree_walk.asm 11,12 4 1 theorem
python3 table_index_tree_walk_independent_check.py table_index_tree_walk.asm 6,8 8 4 theorem short789
python3 table_index_tree_walk_independent_check.py table_index_tree_walk.asm 6,8 8 4 theorem gadget_zba
python3 table_index_tree_walk_independent_check.py table_index_tree_walk.asm 6,8 8 4 theorem C400
python3 run_harness_with_independent_interpreter.py k_region_family_test.py fooling_family_dispatcher.asm chain 3 54
python3 run_harness_with_independent_interpreter.py table_index_tree_walk_test.py table_index_tree_walk.asm 5 9 1 0 96 theorem
```

The programs `table_index_tree_walk.asm`, `table_index_tree_walk_audit_order.asm` and `fooling_family_dispatcher.asm` are in `audits/`; the build script checks that the dispatcher it builds is identical to the stored one, and writes it only with `--out DIR`. [Family generator](../audits/table_index_family_generator.py) · [Test harness](../audits/table_index_tree_walk_test.py) · [Every u](../audits/table_index_tree_walk_every_u.py) · [F5′ program on the family](../audits/table_index_lookup_on_padded_family.py) · [Third-literal check](../audits/table_index_tree_walk_third_literal_check.py) · [Dispatcher build](../audits/fooling_family_dispatcher_build.py) · [Independent interpreter](../audits/five_slot_block_interpreter_independent.py) · [Independent generator](../audits/table_index_family_generator_independent.py) · [Independent check](../audits/table_index_tree_walk_independent_check.py) · [Run with the independent interpreter](../audits/run_harness_with_independent_interpreter.py)
