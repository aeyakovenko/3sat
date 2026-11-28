# Fixed linear-time programs decide several five-slot fooling families, and more regions do not force more instructions

Explicit linear-time programs in the five-slot machine decide several fooling families that the small-program exclusions use: 7 stored instructions for the two-low-bit family, 17 for the equality files, and exactly 4, the only proved minimum, for the four 87-byte files. Two other families are decided only in restricted forms. Eight instructions decide the periodic sign-edit family only for edits beyond the first eight tail words. Twenty-six decide only the unpadded sample of the table-index files: that program fails once the sample is padded or translated with all-space words, as the proof's table-index family is. One fixed 28-instruction program decides a k-region family for every k and both region orders, by keeping a table indexed by variable name, so forcing more regions does not force more instructions. A proof that the needed instruction count grows without bound would be the target itself. The journal's [address-production note](address-production-and-a-program-size-lift.md) proves growth with program size, on its own suites, only under deadlines of at most two steps per word, while these deciders take up to about 5–6 steps per word (the pin table up to 2.70), so there is no conflict. The deciders were checked against CaDiCaL at finite size, and during review by an independent interpreter. The note answers a question raised in the project, whether the needed instruction count must grow. No lower bound on SAT is claimed; the linear, quadratic and cubic questions remain open. [Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md) · [The five-slot case split](the-five-slot-case-split-is-exhaustive.md) · [A 43-instruction SAT program](a-43-instruction-sat-program-in-the-five-slot-machine.md)

## Setting

The machine is the journal's separate-operation RAM, as run by the audit `five_slot_ram_interpreter.py`, with the conventions of the 43-instruction note: every register starts at zero, there is no public n or w, STORE payloads are registers, and every data instruction has a free fixed successor. For each fooling family F used in the five- and six-instruction exclusions, the question is the least s such that some s-instruction program is correct on every file of F, (a) with any running time, and (b) with running time O(N) on F, where N is the length in bits. The labels R1, W5 and W7d are those of the [case-split note](the-five-slot-case-split-is-exhaustive.md): R1 is its cited [one-arithmetic-site note](read-only-ram-with-one-arithmetic-site.md), and W5 and W7d are rules of its coverage script (the raw-word case and the translation-stable three-period case).

The generic lower bound is 4. Each family has unboundedly many sensitive words and a bounded word palette, so a correct program needs a cycle containing a LOAD and a numerical site, and a cycle that can reach both verdicts needs two branches (step 1 of the five-instruction theorem).

## 1. The deciders

| family (where the journal uses it) | program | stored instructions | files correct / run | max steps per file word | lower bound |
|---|---|---|---|---|---|
| F1, the even periodic sign-edit base, **restricted to edits at tail words ≥ first + 8** (property 1 of the five-instruction-loops note; R1 non-cursor rows; parity rows) | `sign_edit_periodic_scan.asm` | **8** | 60/60 | 5.99 | 4 |
| F2, the two-zero-low-bit base (read-only cases 3 and 4) | `two_low_bit_count.asm` | **7** | 30/30 | 5.00 | 4 |
| F3, the four 87-byte equality files (the Lean sample of the two-query obstruction) | `four_file_four_instructions.asm` | **4** (exact) | 4/4 | constant | 4 |
| F4, the constant-palette equality files (the [communication note](communication-bound-for-public-crossed-scans.md); R1 cursor row, W7d), not the one-accumulator scan's re-paired variant | `equality_two_cursor_17.asm` | **17** | 64/64 | 4.83 | 4 |
| F5′, the dense-name, unpadded, untranslated table-index files of the audit `table_probe_context_audit.py` (the audit's sample), not the proof's family | `table_index_lookup.asm` | **26** | 24/24 | 5.33 | 4 |
| k-region equality, any k, either order | `k_region_pin_table.asm` | **28** | 108/108, plus 48/48 on F4 | 2.70 | 4 |
| every family at once, any speed | the journal's `five_slot_sat_program_43.asm` | 43 | 4/4 on F3 only | exponential | 6 |

Every loop either advances a cursor by at least one word or is bounded by t = O(log N). The steps per file word are steps × w / N, maximized over the files run; for the pin table the maximum, 2.70, is on the tight-padding k-region files of the independent check below, and on the generator's k-region files, which end in long padding, it is at most 1.33 ([steps per word](../audits/fooling_family_deciders_steps_per_word.py)):
```
equality_two_cursor_17.asm, equality files             files  64  widths 32,48,64     max steps per file word 4.83
equality_two_cursor_18.asm, equality files             files  48  widths 32,48,64     max steps per file word 4.83
k_region_pin_table.asm, equality files                 files  48  widths 32,48,64     max steps per file word 2.55
k_region_pin_table.asm, k-region files, chain          files  54  widths 32,48,64     max steps per file word 1.33
k_region_pin_table.asm, k-region files, shuffled       files  54  widths 32,48,64     max steps per file word 1.28
k_region_pin_table.asm, tight-padding k-region files   files 150  widths 32,48,64     max steps per file word 2.70
sign_edit_periodic_scan.asm, F1                        files  60  widths 224,256,512  max steps per file word 5.99
two_low_bit_count.asm, F2                              files  30  widths 32           max steps per file word 5.00
table_index_lookup.asm, the audit sample               files  24  widths 32           max steps per file word 5.33
```

**Not built.** A linear-time decider for all the families built here at once (a dispatcher on the header in front of the programs above), and deciders for several families: the parity-pin expander family F6, the arbitrary-stride sign-erasure files F7, the homogeneous base F8, the unary reverse-link base, the placed-site version of F3 used at large lengths, the one-accumulator scan's re-paired equality files, and the proof's padded, translated, bounded-alphabet F5. The F5′ program fails on padded or translated copies of the audit's sample, because an all-space padding or translation word passes its slot test; on the proof's bounded-alphabet files it was not run, and failure there is expected by the same mechanism but unchecked. At t = 7 and 8 and w = 32, with CaDiCaL truth, it answers YES on a file with T(u) = 0 padded by 64 all-space words, and NO on a file with T(u) = 1 translated by one word ([padding failure check](../audits/table_index_lookup_padding_failure_check.py)):
```
t=7 w=32 T(u)=0 trailing pad 64 words          truth=False verdict=YES steps=14920
t=7 w=32 T(u)=1 translated by 1 word, no pad   truth=True verdict=NO steps=13597
```

### F4: the equality files

`equality_two_cursor_17.asm` has three phases:
1. Find S, the first word whose low 16 bits are two spaces: the first literal word of the first half, since no header word qualifies.
2. Build the all-space word P = (x shl 16) or 0x2020 from that sign word x, then run a hare q = S + 2j until M[q] = P. At that point j = H, half the body.
3. Compare M[r] with M[r + H] for r = S, S + 1, …. At the first mismatch, M[r + H] = P means r has reached the second half, so answer YES; otherwise answer NO.

The half-length offset is not a literal: with no public n, and with header and padding of variable length, the program must find S and H itself. The files come from the journal's generator `equality_file_generator.build`, at lengths 2^14 to 2^19 bits, w = 32 and forced w = 48 and 64, with a third each of equal strings, strings differing in one bit, and independent strings; CaDiCaL's verdict on the parsed clauses is asserted to equal (a = b). An 18-instruction predecessor, `equality_two_cursor_18.asm`, gives 48/48.
```
prog=equality_two_cursor_17.asm files=64 correct=64 wrong=0
max steps/N = 0.1511   (N in bits)
```

### The k-region family

`k_region_family_test.py` builds k regions in the journal's word-aligned equality layout. Each region pins the same m variables, with four clauses (pin, ±u, ±v) per pin, and region r lists its pins in its own order, the identity (`chain`) or random (`shuffled`). The formula is satisfiable iff all k regions pin every variable the same way; k = 2..10, m ∈ {3, 5, 8, 13, 21}, w ∈ {32, 48, 64}. With shuffled orders there is no fixed offset between the copies of a pin, so a two-cursor scan does not apply, and a naive streaming design would need about k cursors.

`k_region_pin_table.asm` never locates regions. It turns each pin's aligned binary-digit name into the cell P + 2^K + i, which lies above the file; stores the first sign word seen at that cell; answers NO when a later pin with the same name has the other sign; and jumps to the next clause by the arithmetic q + 2(q − p) + 1.
```
prog=k_region_pin_table.asm order=chain files=54 correct=54 wrong=0
max steps/N by number of regions k: {2: 0.0274, 3: 0.0216, 4: 0.0141, 5: 0.0335, 6: 0.0272, 7: 0.0071, 8: 0.0221, 9: 0.0211, 10: 0.0031}
prog=k_region_pin_table.asm order=shuffled files=54 correct=54 wrong=0
max steps/N by number of regions k: {2: 0.0344, 3: 0.02, 4: 0.0095, 5: 0.0335, 6: 0.0228, 7: 0.0055, 8: 0.0342, 9: 0.0162, 10: 0.0031}
prog=k_region_pin_table.asm files=48 correct=48 wrong=0
```
The last line is the same program on F4. The steps per bit do not grow with k, and the size is fixed by construction: the state that a k-cursor design would keep in registers lives in memory, one cell per variable name. During review 150 more files were regenerated, with k up to 30 and m up to 40 in both orders, all decided correctly.

### F1, F2 and F5′

```
F1 j=4 forced w=512 record=14B sensitive words used=2176 files=15 correct=15 wrong=0 max steps/N=0.0117
F2 j=3 w=32 files=15 correct=15 wrong=0 max steps/N=0.1563
t=10 w=32 bytes=83972 max steps/N=0.1641
files=24 correct=24 wrong=0
```
- **F1, eight instructions.** Word widths are multiples of 16, so the 14-byte tail record repeats every 7 words, and the program compares M[p] with M[p + 7], with a flag marking that the periodic tail has been reached. An edit raises a byte (space to minus), so it shows as M[p + 7] > M[p]; the end of the tail, a partial or zero word, shows as M[p + 7] < M[p]. The program answers YES on an edit at any of the first eight full tail words, first … first + 7, which include the words first … first + 6 that the journal's layout audit `dimacs_five_slot_layout.py` checks, so the family decided is F1 restricted to edits at tail words ≥ first + 8. During review the wrong positions were exactly offsets 0–7 at four forced widths; on the journal's layout at the rule width (j from 128 to 1200, simulated on virtual memory), the edits tested at offsets 0, 3 and 7 are not caught and those at 8, 9 and 20 are. That each row using F1 needs only Θ(N/w) consecutive sensitive words, which the restricted family still has, is claimed without being checked: all four residues mod 4 and all seven tail phases survive the restriction, but no row was re-read against it. Widths are forced to 224–512 bits, since the journal's layout needs W ≥ 28 bytes, which the width rule gives only at astronomical N.
- **F2, seven instructions.** It counts words whose low three bytes are " -1". The base has exactly three of them, all in the forcing clauses, and an edit adds a fourth.
- **F5′, 26 instructions.** It stores every sign slot (a word whose low 16 bits are spaces) at cell P + n, solves t + 2^t = n for t, reads the selector bits u most significant first, and answers by slot t + u. It was tested at t = 7..10 (w = 32) with random tables and addresses, in the layout of the audit's sample. The proof (read-only step 3, the [private-probe theorem](private-probe-contexts-in-read-only-sat.md), W5) pads the file, translates the selector section with all-space words and uses bounded-alphabet aligned names. On padded or translated copies of the audit's sample the program fails, as shown above; the bounded-alphabet files were not built.

### F3: an exact minimum

The four 87-byte files are decided by `x = load 34; y = load 39; z = mul x y; br ltu z 35779 NO YES`:
```
4-instruction program four_file_four_instructions.asm: ['YES', 'NO', 'NO', 'YES']
3-instruction programs x=load 34; y=load 39; br cmp x y deciding the files: []  words(34,39): ['0x200a/0x3120', '0x200a/0x312d', '0x2d0a/0x3120', '0x2d0a/0x312d']
```
No 3-instruction program decides them. Only the case LOAD, LOAD, branch is enumerated; the rest rests on an argument checked by hand during review, including signed branch orders (all four sign words are below 0x8000) and optional public registers n = 696 and w = 16, which give only fixed addresses. A program needs a branch to reach both verdicts and must read both sign words, which leaves three cases. With LOAD, LOAD, branch, one comparison of the two words never separates the files (word 34 < word 39 in all four), and a test of one word against a literal ignores the other. With one LOAD and two branches, no register but the loaded one ever changes, so the loads read at most address 0 and words chased from it, and M[0] = 0x2070 lies beyond the 44-word file. With one branch only, no cycle can reach both verdicts, so there is one straight-line read. This is the four-file suite at its single length (w = 16), so linear time is trivially constant time.

## 2. Where the method stops

- **At any speed.** The size method can climb at most from 6 to 43, because the journal's 43-instruction program decides every comment-free proper 3-CNF with canonical names, and all these families are of that kind. A single family stops fooling much earlier: F3 at 4, F2 by 7, restricted F1 by 8, F4 by 17 and F5′ by 26; the proof's F5 is not decided here. The five-slot exclusion survives only because it needs all the families at once. The least program correct on their union lies between 6 and 43 at any speed. In linear time no upper bound is shown: a dispatcher in front of the deciders above, which is not built, would cover only the families built here.
- **What a family must defeat to carry C to C + 1 in linear time past that point.** Every C-instruction program built from a constant number of cursors at computed offsets (the equality files), direct-address tables in memory indexed by variable names (pin consistency, any number of regions, any order), and constant-size structural parses (sign edits, table lookup). None of the families built here needs search on more than three variables: F2 and F3 have three variables, and in the others unit propagation settles the verdict once at most three public variables are set. If one linear-time program combining a name-to-address map, unit propagation and those few branchings were built, with C\* instructions, then a family that fools every C-instruction linear-time program for some C ≥ C\* would have to defeat it, for example by needing branching on unboundedly many variables. That alone is not SAT hardness, since 2-CNF families also need such branching.
- **The growth statement is the target.** If for every C some family had no C-instruction program deciding it in linear time, then, every program having a fixed size, no program would decide SAT in linear time. Conversely, if SAT has no linear-time program, then SAT itself is such a family for every C. So, for O(N) time, "the needed count grows without bound" is equivalent to the target theorem, not a step toward it. The address-production note proves growth with C under the deadline K⌈n/w⌉ for 0 < K < 2 and at the endpoint K = 2, on its own suites of formulas, which are not the families here. In addition, the deciders here exceed that deadline on some of their files: they take up to about 5–6 steps per word, the pin table up to 2.70 on tightly padded files (1.33 on the generator's k-region files, where it stops at the first word of their long padding). So there is no conflict. The case-split note (§8(a)) already says that larger programs decide the families trivially; what this note adds is the explicit sizes and the k-region test. A direct-address dictionary, the pin table's device, already gives the journal's scan-time SAT program on a circuit-hard list family, with one load and one store per source key ([one wrong initializer](one-wrong-initializer-in-a-sat-run.md)); here the keys are variable names and the program has 28 five-slot instructions.

## 3. The three standard tests

No lower bound on SAT is claimed; the only lower bounds stated are the generic 4 and the exact 4 for the four files.
- **(a) A fast, globally correct solver for the hard families?** Yes; that is the content of this note, with F1 decided only in a restricted form and F5 only in the audit's unpadded sample.
- **(b) The same argument for 2-SAT?** Yes. The families' verdicts are consistency checks of pinned values (F1, F4, F5, k-region) or concern three variables (F2, F3), and the same exclusions and deciders of the same kind apply to 2-CNF encodings of these conditions. The fooling-family method cannot tell SAT from a linear-time language.
- **(c) The relativized clock oracle?** Not applicable, since no time bound is claimed.

## 4. Exact obstruction and next step

The statement that fails is "some k-region fooling family has a minimal linear-time decider whose size grows with k": a fixed program keeps the per-variable state in a memory table indexed by names, so register-held cursors are never needed. The next step is to bound C\*: build one linear-time program in this instruction set that decides all the families at once, combining a name-to-address map (a trie in memory for arbitrary decimal names; the 28-instruction pin table suffices for aligned binary-digit names), unit propagation and brute force over the few variables of Section 2. Its size bounds where families of the journal's kind stop fooling; below it the gap [6, C\*] is a finite enumeration problem. Narrower open items: deciders for F6, F7, F8, the reverse-link base, the placed-site F3, the proof's F5 and the re-paired equality files; and exact minima for F1, F2, F4 and F5′, which need an exhaustive search over programs of 4 to 8 instructions on small family members.

## 5. What is not proved

- **Correctness.** The deciders are correct on the files tested, at finite size, and by the manuscript reasoning in the programs' comments; none has a Lean proof.
- **Layout assumptions.** Every program relies on its family's layout, so each is a promise-problem decider. F1: edits at tail words from first + 8 on, at forced widths. F4, F5′ and the pin table: W ≥ 4. F4: padding of at least 2W + 1 bytes. The pin table: aligned binary-digit names and at least W + 1 bytes of padding after the body, so that one word is all spaces; on a satisfiable 3-region file it answers NO with 1, 2 or 4 padding bytes at w = 32 (1, 2 or 8 at w = 64), as checked during review ([padding check](../audits/pin_table_padding_check.py)), while the generators always leave enough padding. F5′: only the audit's unpadded, untranslated, dense-name sample, tested only at t ≥ 7.
- **Minimality.** None of the sizes 7, 8, 17, 26 and 28 is shown minimal. A one-site lower bound of 5 for F4 was only sketched and is not claimed; the generic two-query lemma does not apply directly to F4, because each private bit is repeated in four sign words.
- **The 43-instruction program** was run only on the four 87-byte files; that it decides the other families rests on the journal's claim for its input class.
- **Families not built**, listed above. So "every family built" means restricted F1, F2, the four-file F3, F4, F5′ and the k-region family.

## Reproducing the checks

Run from the audits directory, where the programs (`.asm`) sit beside the journal's interpreter and generators; CaDiCaL is found through the generator's `find_cadical`. Each command takes about a second, except the last two, which take about 16 and 11 seconds.
```
python3 -B equality_program_test.py equality_two_cursor_17.asm 7 64
python3 -B equality_program_test.py equality_two_cursor_18.asm 1 48
python3 -B equality_program_test.py k_region_pin_table.asm 2 48
python3 -B k_region_family_test.py k_region_pin_table.asm chain 3 54
python3 -B k_region_family_test.py k_region_pin_table.asm shuffled 4 54
python3 -B sign_edit_and_low_bit_tests.py
python3 -B table_index_lookup_test.py
python3 -B four_file_program_search.py
python3 -B four_files_on_the_43_instruction_program.py
python3 -B table_index_lookup_padding_failure_check.py
python3 -B pin_table_padding_check.py
python3 -B fooling_family_deciders_independent_check.py
python3 -B fooling_family_deciders_steps_per_word.py
```
The independent interpreter, written during review from the machine's definition, agrees with the journal's on verdict and exact step count in every run of the check script, which takes section names (counts, f3, f4, kregion, f2, f1, f1virtual, f5, f5translated) and runs all of them with no argument. Its f5 section also runs the sample at t = 5 and 6 with w = 16, where the F5′ program is wrong on 4 and 7 of 8 files; there W = 2, outside the program's assumption W ≥ 4. [Equality test](../audits/equality_program_test.py) · [k-region test](../audits/k_region_family_test.py) · [F1 and F2 tests](../audits/sign_edit_and_low_bit_tests.py) · [F5′ test](../audits/table_index_lookup_test.py) · [F3 search](../audits/four_file_program_search.py) · [43-instruction run](../audits/four_files_on_the_43_instruction_program.py) · [Independent interpreter](../audits/five_slot_independent_interpreter.py) · [Independent check](../audits/fooling_family_deciders_independent_check.py) · [Steps per word](../audits/fooling_family_deciders_steps_per_word.py)
