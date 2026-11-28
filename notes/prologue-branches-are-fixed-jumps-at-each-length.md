# A prologue of branches is one fixed jump at each length, which excludes the last three prologue-branch classes of the six-instruction map

Lemma P says that a branch before the cycle reads no memory, and that every comparison of public words, literals included, has an outcome that depends on the length alone, so at each fixed length the program is one five-slot program. It excludes the last three prologue-branch classes of the six-instruction map, L1S0A2B3 `C:AAL`, L1S1A1B3 `C:ALS` and L1S1A1B3 `C:ASL`, given that each cited five-slot argument fails the program at every large member of its family. That was checked during review at source, including the journal's layout audit at every j from 3 to 1199, whose assertions hold from j = 61 on. The map moves from 929/76/14 to 932/73/14. The exclusions still rest on the unformalized five-slot proofs they cite, and nothing here is a time bound; the linear, quadratic and cubic questions remain open. [Six-instruction map](six-instruction-control-classes-in-the-five-slot-machine.md) · [Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md)

## Setting

The model is the five-slot machine of [five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md): standard width w = 16⌈log₂(n + 2)/16⌉ and Q = 2^w; registers zero apart from optional public n and w; literals fixed integers reduced mod Q; input in words [0, n/w) and zero elsewhere.

The three classes are those of the [six-instruction map](six-instruction-control-classes-in-the-five-slot-machine.md) whose rule-4 marking failed only because of the length-regime gap. They have six stored instructions, three data instructions all on one simple cycle with no off-cycle data, and three branches, and in some of their labeled graphs a prologue branch comes before a cycle that reaches both verdicts. There are 3,528 + 1,764 + 1,764 such graphs, inside 13,392 + 6,696 + 6,696 labeled graphs. The round-four note on [length-dependent markers](length-dependent-markers-and-the-prologue-branch-classes.md) closed the four `C:AL` classes of the gap through length regimes; that route needs every five-slot row to fail the program at lengths below Q/2. Lemma P needs no regime lemma.

**The claim.** For every program P in one of these graphs, P errs or never halts on some proper ASCII DIMACS 3-CNF. Equivalently, for every way σ of resolving the branches P executes before its first cycle instruction, the five-slot program P_σ fails at a length at which those branches actually resolve as σ. Here P_σ is P with each such branch replaced by a jump to the side σ selects, contracted to five stored instructions. Its cycle, operands and exit branches are those of P, and only its entry differs. If σ leads to a verdict without entering the cycle, P_σ is constant. The branches resolved by σ are the prologue branches, which reach the cycle, and any branch reached from a prologue side whose own sides lead only to verdicts; such a branch may be the same vertex that serves as an exit test after the cycle.

## 1. Lemma P

**Lemma P (pointwise entry).** Let P be a program in which no data instruction precedes the recurrent cycle, so the instructions before the cycle are branches only. Let Λ be a set of lengths at each of which both verdicts occur among valid inputs. Suppose there is n₀ such that for every σ and every n ∈ Λ with n ≥ n₀, the program P_σ errs or diverges on some valid input of length n; the witnessing input may come from a family built for P_σ. Then P errs or diverges on some valid input.

*Proof.*
1. Fix n ∈ Λ with n ≥ n₀.
2. Every branch executed before the first cycle instruction runs at most once, before any data instruction. This covers a prologue branch, and a branch reached from one whose sides lead only to verdicts. Let σ resolve all of them.
3. At that point every register holds its initial value: 0, or the public n or w. Branch operands are registers or literals. The width w, the modulus Q and every literal's value mod Q are functions of n. So each of these tests has the same outcome on every input of length n, whatever the comparison type. Call the resulting resolution σ(n).
4. On length-n inputs P executes exactly the data operations, exits and verdicts of P_{σ(n)}; only the executed jumps differ, and there is no clock.
5. If σ(n) leads to a verdict without entering the cycle, possibly through such branches, then P is constant on length-n inputs and errs on one of the two answers present at length n.
6. Otherwise P_{σ(n)} errs or diverges on some valid length-n input by hypothesis, and so does P. ∎

There are finitely many σ, so a common n₀ exists as soon as each P_σ has one. The closest precedent in the journal is the "Side arms" paragraph of [the case-split note](the-five-slot-case-split-is-exhaustive.md), which already observes that a prologue side arm's decision is the same on every input of that length.

**Applying it to the three classes.** All P_σ of one P share the cycle, the operand roles and opcodes, the literals and the cyclic order. The journal's case-split coverage audit keys its operand classes by exactly these (`coinc, AL, num, AS, VS, order` for the writable cycle W-cyc and `da, db, regs, AL, na, nb` for the read-only cycle R2-cyc), never by the entry. So one rule R serves every P_σ of P, with one length set Λ_R that does not depend on σ. Lemma P then applies as soon as R's contradiction has three properties:
- (a) it is derived on inputs of one common length;
- (b) it holds at every sufficiently large length of Λ_R, not along a subsequence the proof chooses;
- (c) it holds for every entry instruction and every public first partial turn.

Some points of the application:
- **Lengths are fixed before σ is known**, which is all Lemma P needs; they may depend on data shared by all P_σ, but not on the entry. Two families leave the exact length to a free constant, and both constants are fixed here as functions of the family parameter alone: the one-accumulator family's record length of ⌈log₂(K + 2)⌉² bytes, and the table family's C and byte-aligned length n_t. Only the file contents then depend on P_σ (the pairing, the frozen records, the translation, the markers).
- **One length per parameter is harmless.** The property-1 base, the read-only decimal family, the table family and the one-accumulator family each have one length per parameter (n_j, N_j, n_t, N(K)). Lemma P fixes n ∈ Λ_R first and only then reads off σ(n), so the prologue never selects the lengths.
- **(c) is part of the five-slot theorem's statement.** P_σ is a five-slot program whose fixed initial instruction is its entry, and the theorem holds for every such program.
- **Both verdicts occur at every sufficiently large byte-aligned length**, by padding a fixed satisfiable file and the 8-clause unsatisfiable file with whitespace. Step 5 needs only this.

During review it was checked, by counting, that a cycle reaching both verdicts uses two of the three branches, so exactly one branch reaches the cycle from outside and P_σ is a genuine five-slot program.

## 2. Which rules serve which class

The cyclic data orders map to the coverage audit's orders as follows: `C:ALS` is L,S,A, order LSN; `C:ASL` is L,A,S, order LNS; and `C:AAL` is the read-only family R2-cyc with both numerical sites on the cycle. [The split script](../audits/prologue_branch_rule_split.py) imports the journal's coverage audit, enumerates its operand classes for these three schedules, lists the rules that fire, and checks that every class is covered by a rule judged to pass (a)–(c):
```
## C:ALS (order LSN): family W-cyc, operand classes 179475, covered by a PASSING rule: 179475, uncovered: 0
## C:ASL (order LNS): family W-cyc, operand classes 179475, covered by a PASSING rule: 179475, uncovered: 0
## C:AAL: family R2-cyc, operand classes 358208, covered by a PASSING rule: 358208, uncovered: 0
all operand classes of the three schedules covered by PASSING rules: True
```
21 rules fire for `C:ALS`, 18 for `C:ASL` and 14 for `C:AAL`, 41 distinct rules in all (27 writable, 14 read-only). Since the passing set is the full rule set, the run shows only that the list of 41 is complete for these schedules; whether each rule passes (a)–(c) is the reading of Section 3. As a control, leaving one rule out uncovers the classes only it covers:
```
## C:ASL (order LNS): family W-cyc, operand classes 179475, covered by a PASSING rule: 179472, uncovered: 3
```

## 3. The 41 rules against (a), (b), (c)

Every rule passes all three. The table `prologue_branch_rule_rows.tsv` in the audits has one line per rule, with its family, lengths, the three properties and anchor sentences quoted from the cited notes. The rules fall into six groups by witness family.
- **The property-1 periodic even base** of [five-instruction loops](five-instruction-loops-on-dimacs-sat.md), one length per j with 10^j clauses and same-length sign edits (W1, W2a–c, W3a–c, W6, W6a, W6c, W6e, W7, W7c, W8a, W8b, W8c1, W8c2). Each contradiction is structural at each j: a bounded address set, O(w) orbits, parity or valuations, or destruction of the next original, against k = Θ(N/w) compulsory words. The initial partial turn is absorbed at O(1) cost.
- **Equality files with two private sign words**, at sufficiently large lengths divisible by w (W3d, W4, W6b). The contradiction is the two-query graph lemma at each such length, and the private sites avoid the input-independent addresses or payloads of the bounded partial turn before the first LOAD.
- **Table-index files of order t**, at n near C(D + 1)2^t t² (W5 and the read-only two-register and case-1 and case-4 rows). Each contradiction holds at every large t: K ≤ 2^{|B|} contexts, or M ≤ (w + 1)Qh codes, against Ω(2^t/t²); at D = 1, Q < 2^16·(n + 2) at every length, so Q/L = O(w) in either length regime. The first probe gets one exceptional slot at each private site.
- **The parity-pin family** of [orbit orders and parity-pinned SAT](orbit-orders-and-parity-pinned-sat.md), at every sufficiently large byte-aligned length, padded with whitespace (W6d, W6f, W8c3). Its expander and balanced-cut claims are taken from the journal, not checked here.
- **Communication families.** W7a (word-aligned equality at every sufficiently large byte-aligned N), W7d (the fixed-stride contiguous-half equality files) and W7b, the shifted crossed scan of [arbitrary-stride private-sign erasure](arbitrary-stride-private-sign-erasure.md). W7b's theorem says "for infinitely many encoded lengths", but its construction uses only that n is divisible by w and large, so it works at every sufficiently large such length.
- **The rest of the read-only classification.** R-case2 uses the [one-accumulator scan](one-accumulator-scan-without-a-clock.md), whose header and total length are fixed in advance, before the prologue is run and the records are frozen; the family depends on the program, which at a fixed length is fixed. The fixed-LOAD, three-register self-addressed, case-3 and remaining case-4 rows use the read-only decimal family N_j = 1024(j + 1)·10^j, and their contradictions (residues mod 4, O(w) or O(hw) addresses, at most two addresses) hold at each j.

No rule uses a clock or a cross-length simulation, the sign of n as a word, or the position of n relative to Q/2; the rows with M ≤ hQ or M ≤ (w + 1)Qh use only the upper bound Q < 2^16(n + 2), which at D = 1 holds at every length. During review the three rows whose source quantifier is weaker than (b) were read at source: the property-1 rows ("arbitrarily large lengths"), the reverse-link row W6e and W7b. Each argument is carried out at one length and holds at every large member of a length set fixed before σ. For the property-1 layout the journal's audit `dimacs_five_slot_layout.verified_family` was run, unmodified, at every j from 3 to 1199: its assertions hold at every j from 61 on and fail exactly for j ≤ 60, where w = 208 and the width of 26 bytes is below twice the 14-byte record.

## 4. A second route: the lengths below Q/2

This is the route of the round-four note, checked at finite size. It avoids the entry-independence step of Section 1 but uses the same per-rule reading, so it is not independent of it. Below Q/2 every prologue test of 0, n, w and literals is constant for large n, which needs the list of comparison types (equality, signed or unsigned order); Lemma P needs no such list. And every family above has members below Q/2 in every width block: that part of a block spans a factor of about 2^15, so a length rule whose consecutive ratio stays below 2^15 meets it. [The length check](../audits/prologue_branch_family_lengths_check.py) prints
```
  property-1 base (FL), j=3..400: members 398, in S_lo 372, widths 32..1344, max consecutive ratio 10 (< 2^15: True), inner width blocks without an S_lo member: 0 of 81
  RO decimal N=1024(j+1)10^j, j=3..400: members 398, in S_lo 374, widths 32..1360, max consecutive ratio 12.5 (< 2^15: True), inner width blocks without an S_lo member: 0 of 82
  table n~64*2*2^t*t^2, t=8..1300: members 1293, in S_lo 1212, widths 32..1328, max consecutive ratio 2.531 (< 2^15: True), inner width blocks without an S_lo member: 0 of 80
  one-accumulator N=8(2K*ceil(log2(K+2))^2+64), K on a 1% grid: members 89387, in S_lo 83794, widths 32..1328, max consecutive ratio 1.315 (< 2^15: True), inner width blocks without an S_lo member: 0 of 80
```
and it finds every sampled prologue test constant on the sampled lengths below Q/2, while signed tests of n flip once the upper half and near-top lengths are added. The table and one-accumulator formulas use representative constants (C = 64, one byte per square bit); only the consecutive ratios matter.

## 5. The class counts

With the three classes EXCLUDED, the map's totals go from 929/76/14 to 932/73/14: L1S0A2B3 goes from 88/17/1 to 89/16/1 classes, with labeled graphs 230436/63000/51840, and L1S1A1B3 from 151/20/1 to 153/18/1, with 258372/35064/51840. The marking script now cites this note for the three classes: `C:AAL` cites the read-only five-instruction theorem plus Lemma P, and `C:ALS` and `C:ASL` cite the writable five-slot theorem, with the case-split note's Section 4 lemma for row W5, plus Lemma P. Lemma P makes rule 4's prologue-branch condition unnecessary wherever the cited rows have properties (a)–(c). For the four `C:AL` classes closed through regimes, the round-four note's row-by-row reading of the one-site theorem supplies (a) and (b); (c) was not re-checked for those rows.

## 6. The three standard tests

No time bound is claimed; this is a program-size statement.
- **(a) A fast, globally correct solver?** Yes. Every witness family has a packed-scan or linear-time solver, and the journal's 43-instruction program decides all inputs.
- **(b) The same argument for 2-SAT?** Expected yes, not checked. The families' hardness is sensitivity, equality and table indexing embedded in the syntax, and Lemma P uses nothing about SAT; no 2-CNF version of the families was built.
- **(c) Relativization.** Both oracles of [the relativized clock](relativized-clock.md) and the multilinear one fail at the step that one LOAD returns one w-bit word from a bounded palette; with the packed oracle a constant number of instructions decides SAT, so the class exclusions are false relative to it. Lemma P itself relativizes, since prologue branches still read no memory. The non-relativizing content is in the cited five-slot rows.

## 7. What remains on the map

- **73 REDUCES.** 33 have a prologue data instruction or a LOAD on an exit path; the prologue word can then be an odd length-dependent marker or stride, the open cases of the round-four note. 22 are read-only loops with one recurrent site plus one-time code, and 18 are LOAD loops beside a separate numerical loop. Lemma P reaches none of them: a prologue *data* instruction changes the operands, not only the entry.
- **14 OPEN**: the four-data cycles and the two bicyclic classes.

The next classes that could move are among the 22 read-only one-site classes with one-time code. A one-time numerical instruction before the loop is a public length-dependent word, the same object as the round-four note's open case, so the one-site rows that use a fixed literal would need a version of the near-top or band argument for that word. Classes whose one-time code sits after the exit need only the exit-code extension and are the cheaper part; which of the 22 are of which kind was not checked.

## 8. What is not proved

- Lemma P and the per-rule reading of (a)–(c) are manuscript arguments. The cited five-slot rows are themselves manuscript proofs, not re-checked here; their family statements and the anchor sentences were read, not every proof line by line. The two-query graph lemma and some helper invariants have Lean proofs in the journal; nothing here was formalized.
- The parity-pin family's expander and balanced-cut claims, which are taken from the journal.
- The entry-independence step rests on the coverage audit's operand classes being free of the entry. The second route avoids this, but its regime lemma and family memberships are checked only at finite size and by the ratio argument.
- The graphs of the three classes without a prologue branch rest, as before, on rule 4's manuscript exit-test extension, which was checked during the map's review in the shape of the argument, not row by row.
- No time bound of any kind.

## Reproducing the checks

Run from the audits directory, where the journal's `five_slot_case_split_coverage.py` sits; nothing is written:
```
python3 -B prologue_branch_rule_split.py
python3 -B prologue_branch_rule_split.py --drop W7b-shifted-crossed-scan
python3 -B prologue_branch_family_lengths_check.py
python3 -B six_slot_control_class_marking.py
python3 -B six_slot_control_class_cross_check.py
```
The split takes about 3 seconds, the length check under a second, and the map's marking script and cross-check about 40 and 12 seconds; the last two now report the 932/73/14 table. [Rule split](../audits/prologue_branch_rule_split.py) · [Length check](../audits/prologue_branch_family_lengths_check.py) · [Marking](../audits/six_slot_control_class_marking.py) · [Cross-check](../audits/six_slot_control_class_cross_check.py)
