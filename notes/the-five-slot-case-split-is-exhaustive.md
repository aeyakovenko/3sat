# The five-slot case split is exhaustive: a mechanical enumeration covers every control graph and operand class

The case split of the five-slot note is exhaustive. A mechanical enumeration of all 8,840,482 control graphs with at most five stored instructions and at most two branch sites, the 814 typed signatures and about 820,000 operand classes finds every class covered by a case that the notes list (four rows through short reductions that the notes use without writing out, given in Section 5), and an independent enumeration written during review reproduces the graph counts and the signature table exactly. Two points are clarified: a constant cursor update is covered by the reverse-link note's fixed-overwrite sentence, and the raw-word case's use of the private-probe theorem on a writable machine is valid, with the explicit lemma stated in Section 4. The soundness of the other cited manuscript lemmas is not checked. This supports the lower end of the [6, 43] program-size frontier and says nothing about time bounds; the linear, quadratic and cubic questions remain open. [Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md) · [A 43-instruction SAT program](a-43-instruction-sat-program-in-the-five-slot-machine.md)

## The statement checked

The target is step 1 and the case trees of the five-slot note, together with the five notes it cites:
- [Writable five slots](writable-five-slots-without-a-clock.md) (WR);
- [Read-only five instructions](read-only-five-instructions-on-ordinary-sat.md) (RO);
- [One arithmetic site](read-only-ram-with-one-arithmetic-site.md) (R1);
- [Five-instruction loops](five-instruction-loops-on-dimacs-sat.md) (FL);
- [Adaptive prefixes](adaptive-five-slot-prefixes-without-a-clock.md) (AP).

The statement checked is:

> For every program P with at most 5 stored instructions, and for every operand allocation and opcode class of P, at least one listed case applies.

An instruction is a LOAD, a STORE, a numerical instruction (NUM) or a BRANCH; successors are arbitrary, and YES and NO are terminals. The listed cases are manuscript lemmas, and this check does not prove them. Rule names below (W5, W7d, R-a and so on) are those of the coverage script `five_slot_case_split_coverage.py`, which tags every class with the rules that cover it and the sentence each rule cites.

## 1. Control graphs

`five_slot_control_graphs.cpp` enumerates every successor function on 5 stored nodes with at most 2 branch sites, with no symmetry reduction: 8,840,482 = 7⁵ + 5·7⁶ + 10·7⁷ graphs. Its summary:

```
graphs enumerated (b<=2): 8840482
  a verdict unreachable: 8029232
  both verdicts, acyclic reachable part: 590610
  both verdicts + directed cycle, b_R=2: 220640
  violations of (i)  [cycle+both verdicts with b_R<2]: 0
  violations of (ii) [not one simple cycle / node both prologue and exit]: 0
  b_R=2 cyclic graphs: 220640, of which no branch on the cycle: 25200
  (ii) sub-violations: not-one-SCC pairs 0, cyclic node without exactly one cyclic successor 0, node both prologue and exit 0
  side nodes (reachable, neither reach nor reached from the cycle) in b_R=2 cyclic graphs: 37296
```

- Claim (i) of step 1, that a cycle with both verdicts reachable needs at least two branches, has no violation. Every one of the 220,640 cyclic graphs with both verdicts reachable has exactly two reachable branches.
- Claim (ii), that with two branches there is one simple cycle traversed in a fixed order and no node both reaches the cycle and is reachable from it, has no violation.
- **Side arms.** The five-slot note does not name prologue branch arms that go straight to a verdict (37,296 node occurrences); FL's sentence "Off-cycle control may choose to halt" arguably covers them. They are harmless. A run that takes a side arm never enters the cycle. When the LOAD is on the cycle, no LOAD precedes the side arm, so whether a run takes it, and what it then answers, are the same on every input of that length. A LOAD on a side arm falls under the rule for a LOAD off the cycle.
- 25,200 cycles contain no branch; reduction R-a (Section 5) handles them.
- Three or more branches leave at most two data sites, so those programs are classified by their type counts alone.

**Independent enumeration.** `five_slot_control_graphs_independent.cpp` was written from scratch during review, with breadth-first reachability, Kosaraju strongly connected components and forward and backward reach from the cycle in place of a closure matrix. It reproduces every count above, and its 814-key typed-signature table, with the graph-typing count of each key, is identical to that of the first enumerator. It also tests every branch mask with up to five branch sites, 550,731,776 successor functions: claim (i) has no violation for any number of branches, and claim (ii) none for any graph with exactly two reachable branches, including graphs with unreachable extra branch sites. Its summary begins and ends:

```
all masks: 550731776 graphs; b<=2: 8840482
viol(i) over all b: 0; b_R=2 cyclic both (b<=2): 220640; viol(ii) (all masks): 0; no branch on cycle: 25200; side nodes: 37296
```

## 2. Typed signatures

Assigning the types LOAD, NUM and STORE to the reachable data nodes gives 814 typed signatures, and all are covered:

```
typed signatures (b_R=2): 814; uncovered at type level: 0
b>=3 uncovered: []
```

Read-only programs whose two NUMs are both off the cycle are covered by RO's sentence "These cases cover off-cycle numerical sites as well": only x varies on the cycle, so the LOAD is either self-addressed or at a fixed address.

## 3. Operand classes

Every operand class is covered:

| Family | Classes | Uncovered |
|---|---|---|
| W-cyc (writable, all three data sites on the cycle) | 358,950 | 0 |
| R2-cyc (read-only, both NUMs on the cycle) | 358,208 | 0 |
| W-proS (STORE in the prologue) | 102,075 | 0 |
| R2-offN (one NUM off the cycle, two variants) | 1,405 each | 0 |
| R2-offNN (both NUMs off the cycle) | 5 | 0 |
| W-exitS (STORE on an exit or side arm) | 1 | 0 |

That is 822,049 classes in all. Two of the summary lines:

```
operand family W-cyc: classes 358950, uncovered 0, multiply-covered 25253, rules never firing []
operand family R2-cyc: classes 358208, uncovered 0, multiply-covered 1932, rules never firing []
```

- Each cited sentence is one predicate, and there is no catch-all rule. Every rule fires at least once.
- Two predicates are wide. `W7-bnd-nontranslation` is a complement: it takes every NUM form that uses only p and is not an odd translation. `w7_bnd_nontranslation_forms.py` lists the 76 distinct forms it absorbs, and each matches an item in FL's list: even translation, d−p, p−p, doubling, odd or even multiplier, squaring, bitwise, shift, rotate, move, compare. The W-exitS rule is unconditional, and reduction R-d is its proof.
- Destination aliasing, fixed-operand kinds, opcode classes (shift and rotate with distinct data and count roles, both subtraction orders) and both cyclic orders (LNS, LSN) are all enumerated. During review the decision trees of the W-cyc and R2-cyc predicates were traced by hand: every combination of LOAD address, STORE address and payload, NUM operand support, opcode class and cyclic order reaches some rule, and 18 sampled classes were checked against their sources.
- **Coverage levels.** The script labels every rule `A` (its cited statement's hypotheses include the class), except the four rows that rest on reductions R-a to R-d, labelled `A-implied`, and W7d, labelled `B`. Sections 5 and 6 prove those rows.

**Mutation test.** `five_slot_case_split_mutation_test.py` drops each of the 57 rules in turn:

```
W6-const-cursor                            typed_uncovered=0 operand_uncovered=185
WP-coinc-two-query                         typed_uncovered=0 operand_uncovered=6600
WE-store-never-precedes-a-LOAD             typed_uncovered=0 operand_uncovered=1
57 rules tested; rules whose removal uncovers nothing: ['T-noLOAD', 'T-noBranchOnCycle']
```

For 55 rules some class becomes uncovered; the rules for no LOAD and for a branch-free cycle are covered by other rules as well. Three rows rest on the reductions alone:
- R-b (W6-const-cursor): 185 operand classes, the constant NUM with STORE M[x]←p in order LSN. This is the reverse-link schedule with constant f; the reverse-link note's fixed-overwrite sentence also covers it (Section 4), and it rests on R-b alone only because the script's reverse-link predicate requires x among the NUM operands.
- R-c (WP-coinc-two-query): 6,600 operand classes.
- R-d (WE): the single abstract class of W-exitS, which accounts for 8,640 graph-typing pairs.
- R-a: none, since other rules also cover its classes.

The mutation test shows that each rule is needed. It cannot show that a predicate is no wider than its citation, or that the hand-written operand generator is complete. For the first, all 57 rules were traced against their sources during review and none was found broader than its source, and the 76-form list checks the widest one; for the second, see the hand trace of the decision trees above.

## 4. The two clarified points

**(a) A constant update and the reverse-link note.** WR's "Other STORE operands", bullet 2, sends the old-cursor payload through x to the reverse-link note. That note's opening sentence says f uses x, but its case paragraph also treats a fixed overwrite: "A comparison or fixed overwrite has constant-size image and hence allows only a constant number of distinct future cursors." A constant f is in any case the constant-cursor degeneracy R-b, where the LOAD reads at most two addresses. The child's first sentence could add "or a fixed overwrite". No class is uncovered. [Unary reverse links](unary-reverse-links-on-an-even-dimacs-base.md)

**(b) The raw-word case W5 and the private-probe theorem.** The private-probe theorem is stated for read-only RAMs. WR's "Writing through the raw word" applies it to a machine that writes. The following lemma, written during review, shows the application is valid; WR does not state it explicitly. [Private-probe contexts](private-probe-contexts-in-read-only-sat.md)

*Setting.*
- The five-slot schedule has x ≠ p and LOAD x←M[p]. The NUM writes p from any operands. The STORE is M[x]←x or M[x]←c, with c fixed at this length.
- Let H be the union of the original word values over all tables, selector settings and translations of the bounded-alphabet table-index files of order t at a common length. Its size h = |H| does not depend on t.
- Put B = H ∪ {c, x₀}, where x₀ is the initial x.
- Translate the private section so that no private address lies in B. This is possible because there are L = Θ(n/w) translations and at most t|B| forbidden ones.

**Lemma.** The private-probe theorem applies to this writable machine. For a fixed table, a context at a private probe consists of the control state at the LOAD and a vector of |B| mark bits; with the reply, it determines the continuation up to the next private probe, a verdict, or divergence. So each private site has at most K ≤ 2^{|B|} contexts, and the graph count (tK+3)^{2tK+1} holds. Realizing all tables forces K = Ω(2^t/t²). Since |B| ≤ h+2 does not depend on t, this is a contradiction for large t.

*Proof.*
1. **Every value held in x lies in B.** x changes only at the LOAD. A LOAD returns either an original word, which is in H, or a STORE payload, which is x (in B by induction) or c. The initial value x₀ is in B.
2. **No write reaches a private word.** Every STORE destination is the current x, which lies in B, and no private address is in B. So a probe of a private word returns its original sign.
3. **Each cell b of B holds its original word until its first STORE, and its mark afterwards.** The mark is b itself under M[x]←x (destination and payload are both x = b), or c under M[x]←c. So one bit per member of B, together with the original input, determines the whole memory, and each step updates these bits deterministically. WR notes that the initial partial turn obeys the same rule.
4. **Between two private probes the run depends only on the context.** Every read in that stretch is of a non-private cell, whose value is a function of the table and translation, which are public for a fixed table, and of the mark bits. So the continuation is deterministic and does not depend on the private bits.
5. **The state after a probe is determined by the mark bits and the reply.** At a private probe, p equals the site address and the LOAD overwrites x. Every other register is immutable, and the control state is that of the LOAD. So there are at most 2^{|B|} contexts per site, and the first, input-independent probe is one of them.
6. **The counting argument goes through.** The private-probe theorem uses read-only memory in exactly two places: the contraction step ("All intervening reads have fixed public values for this table") and the fact that a private probe returns its original sign. Steps 4 and 2 restore these. The rest of its proof is unchanged: contract public runs between probes, count labelled graphs on tK slots, and realize all 2^{2^t} tables. ∎

## 5. Four reductions the case split uses without writing out

**(R-a) A cycle with no branch.**
- The enumeration shows that the reachable directed cycle is unique. If it has no branch, each cycle node's only successor is on the cycle, so a run that enters it never halts.
- A correct program halts on every valid input, so no such run enters the cycle.
- Any walk that avoids the cycle repeats no node, because a repeat would close a second directed cycle. So each halting run executes each of at most 5 sites at most once, and makes at most 3 LOADs.
- Step 1 requires reading each of k = Θ(N/w) sensitive words on the base. This fails once k > 3. ∎

**(R-b) A constant cursor.** Here x ≠ p, the LOAD is x←M[p], and the NUM has no mutable operand.
- Every execution of the NUM writes the same word c, which is fixed at this length. No other instruction writes p.
- So p takes at most two values, p₀ and c, and the only LOAD reads at most two distinct addresses in any run.
- Step 1 needs k > 2 distinct reads. ∎

**(R-c) A prologue STORE with coincident destinations.** The LOAD and the NUM both write one register r, and the LOAD is r←M[r]. (A LOAD at a fixed address is a separate rule.)
- The STORE runs before any LOAD, with every register at its initial value, so its address a and its payload are fixed at this length.
- Afterwards memory is read-only: the file image with M[a] replaced by a public word.
- Take WR's four equality files, with the two private sign sites i, j chosen different from a, so that the prologue STORE cannot overwrite a sign. WR's section "One fixed scratch address" shows that arbitrarily many choices remain.
- Just before a probe of site i, the program counter is at the LOAD and r = i, so there is exactly one state per site. Just after it, r is the reply and nothing else is mutable.
- So the continuation up to the next probe of a private site, or to a verdict, depends only on (i, reply).
- The computation therefore forms a graph with at most two query vertices plus an input-independent start. By the two-query lemma (equality is missing among the 3,125 graphs, Section 7) it cannot compute equality.
- WR states this single-register case in its two-query paragraph ("If there is only one mutable register, its post-LOAD value is likewise fixed by the reply"); its off-cycle paragraph names only the distinct-register and self-addressed cases. ∎

**(R-d) A STORE on an exit arm or side arm.**
- The LOAD is on the cycle; otherwise the rule for a LOAD off the cycle applies.
- An exit node or side node cannot reach the cycle, so no LOAD executes after the STORE.
- The STORE writes no register, and branches compare only registers.
- So replacing the STORE by a jump to its successor changes no verdict and no halting behaviour on any input.
- The result is a read-only program with one numerical site, which R1 excludes for any control graph, explicitly allowing jumps and any number of LOADs and branches. ∎

## 6. W7d checked against its citation

**The class.** As the coverage script defines it (rule `W7d-translation-stable-three-periods`):
- x ≠ p and the LOAD is x←M[p];
- the NUM is p←p+d (or p−d) with d an odd literal;
- the STORE is M[p]←v, executed after the LOAD and before the NUM;
- the payload v is x (writeback), p (self-mark) or a fixed word (fixed mark).

**The citation.** WR's "Other STORE operands", bullet 3, cites the communication note. Its main theorem concerns crossed writes M[x_i]←p_{i+δ}, which is not this class, and W7d does not use it. WR uses the note for three things only, and their hypotheses hold for W7d:
- the fixed-stride equality family with contiguous halves (section "A constant word alphabet for deterministic equality": proper 3-CNF, jointly satisfiable exactly when a = b, with Alice owning a word interval and Bob its complement);
- the bound of J = 2|d| owner changes per full orbit (section "Distributed simulation");
- the k-bit lower bound for deterministic equality.

[Communication bound](communication-bound-for-public-crossed-scans.md)

**The stability step is WR's own argument,** checked here for this class:
- Because d is odd, the orbit of p←p+d has period exactly 2^w and visits every address.
- With writeback, the memory never changes after the prologue. With a self-mark or fixed mark, the first visit to an address a sets M[a] to a or to c, and every later visit rewrites the same word. After one full period the whole memory is fixed.
- At the ends of periods 2 and 3, the memory, p (the same public position), x (the reply at the same last position) and the program counter at the cut are all equal. A run that has not exited would repeat forever, so a total solver exits within three periods plus a bounded partial turn.
- Every read and write in a turn is at the current scan address, which the current owner holds. So the protocol hands over only (x, p, control state), O(w) bits, at most 2|d| times per period: O_d(w) bits in total, below the k = Θ(N/log² N) bits that equality needs.

`w7d_translation_stability_check.py` checks this at widths 4, 6 and 8, for every odd d with |d| ≤ 7 and all three payloads:

```
W7d stability: runs 2880 violations (state after period 2 != after period 3): 0
max owner changes per period by d: {-7: 14, -5: 10, -3: 6, -1: 2, 1: 2, 3: 6, 5: 10, 7: 14} all <= 2|d|: True
```

## 7. Finite checks

`five_slot_finite_checks.py` uses its own file layout, not the journal's 87-byte files, and imports no journal code:
- four files of 98 bytes, so N = 784 and w = 16, differing in exactly two words, 38 and 43, with SAT exactly when s1 = s2 (brute force over all 8 assignments of the parsed clauses);
- all 3,125 two-query graphs, of which 14 of the 16 total two-bit functions occur, with equality and XOR missing;
- a positive control: a program with 2 direct LOADs and 3 branches decides all four files;
- a sweep of the 7,225,344 programs of the shape `LOAD x<-M[p]; NUM p<-op; B1; B2`, at finite size only: none decides all four files.

The full run (`--full`, about 8 minutes) prints:

```
1. file length bytes {98} N bits 784 w 16
   SAT values {(0, 0): True, (0, 1): False, (1, 0): False, (1, 1): True}  equals (s1==s2): True
   differing word addresses [38, 43]  words per file 49
2. graphs 3125; total functions realised 14 of 16; missing: ['EQ', 'XOR']
3. positive control (2 direct LOADs, 3 branches): {(0, 0): 'YES', (0, 1): 'NO', (1, 0): 'NO', (1, 1): 'YES'}  correct on all four: True
4. swept 7225344 programs of the shape LOAD x<-M[p]; NUM p<-op; B1; B2 with 12 literals; deciding all four files: 0
```

Without an argument the script runs sections 1–3 and a smoke test of the sweep that runs one program in 101, in a few seconds.

## 8. The three standard tests

- **(a) Does the hard family have a fast globally correct solver?** Yes. This is a code-size exclusion in one ISA, not a time bound. A 43-instruction solver exists, and larger programs decide the families trivially.
- **(b) Does the same argument give the same bound for 2-SAT?** Plausibly yes. The sign-edit and equality families do not depend on SAT being hard, so a five-slot exclusion for 2-SAT is to be expected. This was not checked.
- **(c) Does it survive the oracles?** Not applicable. No time lower bound is claimed, so no step is subject to the packed oracle of the relativized-clock note or to the multilinear oracle. [Relativized clock](relativized-clock.md) · [Multilinear oracle](multilinear-oracle-clock.md)

## 9. What is not proved

- **Soundness of the cited lemmas.** The check shows that the case split is exhaustive. The soundness of the cited manuscript lemmas (orbit prefixes, crossed scans, odd markers, the one-accumulator unary orbit, the communication and equality bounds) is not checked. The exception is the raw-word lemma of Section 4. The child statements were read but not their proofs: the unary reverse links, both adaptive-prefix rows, the odd markers (p±x and x−p with M[p]←c after the read), the unshifted and arbitrary-stride crossed scans, the "any unary orbit" section of the one-accumulator note, the private-probe theorem and the communication note.
- **Limits of the mutation test.** See Section 3.
- **Opcode classes.** The operand alphabet groups opcodes into classes. Corner cases of individual opcodes, such as saturating shift counts, are left to the cited lemmas.
- **Finite size.** The sweep covers one program shape at w = 16 with bounded literals. The W7d check covers widths up to 8.
- **Time targets.** Nothing here bears on the linear, quadratic or cubic time targets.

[Odd self-marked cursors](odd-self-marked-cursors-without-a-clock.md) · [Unshifted crossed scan](unshifted-crossed-scan-without-a-clock.md) · [Arbitrary-stride sign erasure](arbitrary-stride-private-sign-erasure.md) · [One-accumulator scan](one-accumulator-scan-without-a-clock.md)

## Next step

The open program-size step is six stored instructions, where the journal so far treats particular architectures only. The control-graph layer here is a finite enumeration and could be formalized in Lean. [Six-slot two-ahead lock](six-slot-two-ahead-lock.md) · [Two-ahead stores in a six-slot scan](two-ahead-stores-in-a-six-slot-scan.md)

## Reproducing the checks

Run from `audits/`. The coverage script reads `five_slot_control_graph_signatures.txt`, the first enumerator's output, from its own directory; `--signatures FILE` reads a freshly generated table instead. No script writes files unless given `--out DIR`.

```
c++ -O2 -std=c++17 five_slot_control_graphs.cpp -o /tmp/five-slot-graphs
/tmp/five-slot-graphs > /tmp/five-slot-signatures.txt
c++ -O2 -std=c++17 five_slot_control_graphs_independent.cpp -o /tmp/five-slot-graphs-independent
/tmp/five-slot-graphs-independent > /tmp/five-slot-signatures-independent.txt
python3 five_slot_case_split_coverage.py --signatures /tmp/five-slot-signatures.txt
python3 five_slot_case_split_mutation_test.py
python3 w7_bnd_nontranslation_forms.py
python3 w7d_translation_stability_check.py
python3 five_slot_finite_checks.py --full
```

The enumerators print their summaries on standard error and take about a second and about 25 seconds. The first one's table is byte-identical to `five_slot_control_graph_signatures.txt`; the second prints only the signature lines, identical to the first one's. The mutation test takes about 2 minutes and the full sweep about 8.
