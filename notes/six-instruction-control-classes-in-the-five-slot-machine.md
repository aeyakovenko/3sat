# Six-instruction programs in the five-slot machine: 969 of 1,019 control classes are excluded and 14 are open

For programs of six stored instructions in the five-slot machine, a generated list of 1,019 control classes has 969 classes excluded at every speed: 887 by cited journal theorems, 45 by the five-slot arguments extended to prologue tests and exit code, and 37 by a round-six note's lemmas on one-verdict loops, exit code and LOAD loops without arithmetic. Beside the classes there are 50 rows of graphs that reduce to at most five instructions, to a constant answer or to bounded reads. Another 36 classes reduce to known cases with extra code (a five-slot schedule or a loop with one numerical site) and are not yet checked. The remaining 14 are open: 12 simple six-instruction cycles with four data instructions, and 2 two-cycle classes with three branches. An independent enumeration written during review reproduces every class, every labeled count and the 932 exclusions of rules 1–4, and a second one, written during the review of the round-six note, reproduces the per-graph split behind the other 37. A zero-trap lemma, with a companion lemma for STOREs at the cursor (both manuscript), closes the 24 register-payload subrows of the additive parity row for the writable five-slot cycle with one prologue numerical instruction. The fixed-odd-marker subrows need the journal's odd-marker proof with a length-dependent marker; a round-four note supplies it at the standard width on near-top lengths, where the marker is odd, and the class keeps other open rows. This maps the open part of the six-instruction step and says nothing about time bounds; the linear, quadratic and cubic questions remain open. [Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md) · [The five-slot case split is exhaustive](the-five-slot-case-split-is-exhaustive.md) · [A 43-instruction SAT program](a-43-instruction-sat-program-in-the-five-slot-machine.md)

## What a class is

Step 1 of the five-slot note enumerates control graphs. The same enumeration is done here for six stored instructions in the journal's separate-operation RAM, in the same units: s instructions and b branches give s+2 vertices with YES and NO and exactly s+b edges, so cyclomatic number b−1. A class is defined by:
- the opcode mix (n_LOAD, n_STORE, n_numerical, n_branch);
- the nontrivial strongly connected components (the recurrent parts). For a simple cycle this is the cyclic order of its data instructions; otherwise it is the data multiset, written G{...};
- whether two recurrent parts are sequential or parallel;
- the position of each data instruction outside them: pre, post, mid, or none (on a bypass path).

Branch positions are dropped at this coarse level; column `n_fine` of the class table counts the classes that keep them. Operands and opcodes are not enumerated, except inside the class of Section 3.

Each class gets one of three statuses:
- **EXCLUDED:** excluded at every speed by cited theorems whose hypotheses every graph of the class satisfies, or by a reduction to at most five slots. Where two lemmas share a class, the class table says which graphs each covers.
- **REDUCES:** the recurrent schedule is a known one, but the class adds code that breaks a hypothesis used by some row of its proof, or has a length-dependent entry point. These are not checked.
- **OPEN:** no journal theorem covers the class at every speed.

No class falls wholly under the clock-only results, which cover only operand subcases.

## 1. Enumeration

**Opcode mixes.** A useful program needs at least one LOAD, at least one numerical site and at least two branches. This gives 10 mixes for s = 6:
- L3S0A1B2, L2S1A1B2, L2S0A2B2, L1S2A1B2, L1S1A2B2, L1S0A3B2;
- L2S0A1B3, L1S1A1B3, L1S0A2B3;
- L1S0A1B4.

**Graphs.** Instruction types are fixed to vertex numbers. A data instruction takes any of 8 successors. A branch takes an unordered pair of distinct successors; a branch with equal targets is a jump and contracts to five slots. The start vertex is any of the 6 instructions. So each mix has 6·8⁴·28² labeled graphs with two branches, 6·8³·28³ with three and 6·8²·28⁴ with four. The enumerator prints, for example:

```
L1S1A2B2 total labeled (start x successors) = 19267584
L1S1A1B3 total labeled (start x successors) = 67436544
L1S0A1B4 total labeled (start x successors) = 236027904
```

**Reductions.** The enumerator first removes labeled graphs that reduce, by one of these rules:
- an unreachable instruction (at most five slots remain);
- an unreachable verdict (the answer is constant, so wrong);
- a branch side that returns to the same branch (it repeats an unchanged test forever);
- a branch side that cannot reach a terminal (it diverges);
- an acyclic program (bounded reads).

In the two divergence cases a correct decider never takes that side on valid inputs. Replacing the branch by a jump to its other side gives a program of at most five slots that behaves identically on all valid inputs, and the five-slot theorem excludes it. This is a manuscript argument, checked during review. These are the 50 reduction rows of the class table, five per mix. For every mix with two branches the counts are:
- 18,789,696 unreachable instruction;
- 420,936 unreachable verdict;
- 5,040 self-loop;
- 8,064 dead side;
- 18,648 acyclic.

**Marking.** The summary gives, per mix, the classes as EXCLUDED/REDUCES/OPEN, then the labeled graphs in the same order, then the reduced labeled graphs:

```
allocation  classes(EXCL/REDUCES/OPEN)  labeled graphs (EXCL/REDUCES/OPEN)  reduced-labeled
L1S0A1B4  76/0/0  2741112/0/0  233286792
L1S0A2B3  101/4/1  264204/29232/51840  67091268
L1S0A3B2  54/3/1  19728/3312/2160  19242384
L1S1A1B3  166/5/1  278604/14832/51840  67091268
L1S1A2B2  114/6/3  20352/2688/2160  19242384
L1S2A1B2  116/4/3  21456/1584/2160  19242384
L2S0A1B3  106/0/0  345276/0/0  67091268
L2S0A2B2  67/5/2  17904/5136/2160  19242384
L2S1A1B2  111/9/3  17952/5088/2160  19242384
L3S0A1B2  58/0/0  25200/0/0  19242384
```

The enumerator's last column counts, in each class, the labeled graphs that have a prologue branch before a two-verdict cycle (rule 4, below). It changes no class key.

**The fine level.** The OPEN class L1S1A2B2 `C:AALS` has 14 fine classes and 720 labeled graphs:
- 10 six-cycles with both branches on the cycle, 48 labeled graphs each, matching a direct necklace count of 10;
- 4 five-cycles whose second branch lies off the cycle: on the exit path (20 of each 60 labeled graphs), or as a prologue branch with one side to a terminal (40 of 60).

**Independent enumeration.** An enumerator written independently during review finds strongly connected components by Kosaraju's method with an explicit depth-first search, builds the branch pairs differently and computes reachability by breadth-first search. It reproduces:
- the 1,019 class keys and the labeled count of every class;
- the reduced and kept totals of every mix: 25,200 kept graphs per mix with two branches, 345,276 with three and 2,741,112 with four;
- the 932 classes excluded by rules 1–4;
- the prologue-branch counts on the classes of rule 4;
- the 12 four-data cycles.

Its rule 4 is the rule as first stated. The 7 classes in which it finds a prologue branch before a two-verdict cycle are exactly the 7 of the length-regime gap below; all 7 are now EXCLUDED, so the cross-check moves none of them. The 37 classes of rule 5 below are unexcluded under its rules; the cross-check takes them from the round-six note's class lists, and checks that those lists hold exactly the 73 classes its rules leave unexcluded outside OPEN, and that the 36 the lists do not move are the table's REDUCES classes. The cross-check prints:

```
ok    1. same class keys (1019) and labeled counts
ok    2. per mix, total = reduced + kept and both equal (10 mixes)
ok    3. EXCLUDED sets equal (969: the independent 932, including the 7 rule-4 classes with a prologue branch, and the 37 that the round-six lists move)
ok    4. prologue-branch counts equal on all 45 rule-4 classes
ok    5. four-data cycles equal the OPEN simple cycles (12)
ok    6. the round-six lists hold the 73 classes left by the independent rules outside OPEN; the 36 they do not move are the REDUCES classes
```

## 2. Marking rules

The rules are applied by `six_slot_control_class_marking.py`, and the class table gives the citation of every excluded class.

**EXCLUDED.**
1. **No LOAD in a recurrent part.** Each LOAD then runs at most once, while the sensitive family needs unboundedly many original reads. [Control graph and accessible data](five-instruction-loops-on-dimacs-sat.md#the-control-graph-and-accessible-data) · [Bounded RAM programs](bounded-ram-programs-and-separate-sat-witnesses.md)
2. **No numerical site in a recurrent part.** At most n_A new words are made per run, so on the periodic base the value set and the address set are bounded. The citations are the same.
3. **Read-only with exactly one numerical site in the whole program**, under any control flow. This is the one-site theorem as written, which allows any number of LOADs, branches and jumps. [One arithmetic site](read-only-ram-with-one-arithmetic-site.md)
4. **A single simple recurrent cycle with at most three data instructions (45 classes).** These form a five-slot data schedule. The rule applies under two conditions: no data instruction comes before the cycle, and no LOAD comes after it. A prologue branch before a cycle that reaches both verdicts is covered by the arguments for the length-regime gap below. Extra branches then only test public initial registers or act as exits.
   - **What the rule rests on** (a manuscript observation). After the control-graph step, the cited proofs use only three things: the fixed turn order, exits that cannot rejoin the cycle, and a verdict that is a function of the registers at exit. They use b = 2 only to get one simple recurrent cycle, which the enumeration supplies here. Post-exit numerical instructions or STOREs with no later LOAD only change the verdict function.
   - **The length-regime gap**, found during review. A prologue branch can test only 0, n, w and literals, but such tests are not eventually constant in n: a signed test of n against 0 decides n ≥ 2^(w−1), and the answer flips inside every width block. A six-slot program can therefore behave like a five-slot program with entry point e only on one length regime. The five-slot theorem as stated gives some failing input, not one in that regime. This matters only when a prologue branch comes before a cycle that can still reach both verdicts; with two branches the cycle then has a single verdict and the program is wrong anyway. Such graphs occur in exactly 7 classes:
     - L1S0A2B3: `C:AL post:A`, `C:AAL`, `C:AL none:A`;
     - L1S1A1B3: `C:AL post:S`, `C:ALS`, `C:ASL`, `C:AL none:S`.

     On 27 November a round-four note closed the gap for the four `C:AL` classes, which are now EXCLUDED: their prologue tests reduce to [n ≥ Q/2], [n ≥ Q−c] and [n = Q−c], and the one-site theorem fails the program on every regime. [Length-dependent markers and the prologue-branch classes](length-dependent-markers-and-the-prologue-branch-classes.md) On 28 November a round-five note closed the other three, `C:AAL`, `C:ALS` and `C:ASL`, which are now EXCLUDED: a prologue made only of branches reads no memory and compares only public words, so at each fixed length it is one fixed jump and the program is a five-slot program there (Lemma P), and each cited five-slot row fails the program at every large member of its family. [Prologue branches are fixed jumps at each length](prologue-branches-are-fixed-jumps-at-each-length.md)
   - **Citations, per schedule** (as in the class table):
     - **24 classes, `C:AL` or `C:ALL`:** the one-site theorem, used with exit code after the last LOAD. The theorem as written allows no STORE and no second numerical site; the extension is part of this note's manuscript argument. The four `C:AL` classes with a prologue branch also cite the round-four note: `post:A` uses this extension, `post:S` and `none:S` need only reduction R-d of the case-split note and the theorem as written, and `none:A` the theorem as written.
     - **7 classes, `C:AAL`:** the read-only five-instruction theorem; the one with a prologue branch also cites Lemma P of the round-five note. [Read-only five instructions](read-only-five-instructions-on-ordinary-sat.md)
     - **14 classes, `C:ALS` or `C:ASL`:** the writable five-slot theorem; the two with a prologue branch also cite Lemma P of the round-five note. These rest on its row W5, "Writing through the raw word", and so on the private-probe lemma for the writable machine proved in Section 4 of the case-split note. That lemma says: every STORE destination lies in a bounded set B of words, the private addresses are translated outside B, and |B| mark bits, one per cell of B, together with the input determine the whole memory, so a context and a reply determine the continuation. It carries over unchanged, as checked during review. In each of these classes the sixth instruction is either a STORE or numerical instruction after the exit with no later LOAD, an instruction on a bypass path, or an extra branch. So every STORE executed before the last private probe is the cycle STORE, whose destination lies in B. [Writable five slots](writable-five-slots-without-a-clock.md#writing-through-the-raw-word) · [The two clarified points](the-five-slot-case-split-is-exhaustive.md#4-the-two-clarified-points)
5. **The round-six lemmas (37 classes).** On 28 November a round-six note excluded 37 of the 73 REDUCES classes. A phase lemma excludes the 18 classes with a LOAD loop that has no numerical site beside a loop that has one: such a LOAD loop reads a bounded set of cells on the property-1 base, given a bound on memory at its entry that the note checks class by class. Lemma E (one-time code only after the exit or on a bypass, which opens the one-site theorem's proof) and Lemma V (a LOAD loop from which only one verdict is reachable) exclude 12 of the 22 one-site classes, and Lemma V alone excludes 7 of the 33 five-slot-schedule classes. The marking script applies the phase lemma as a shape rule, with one LOAD and either no STORE or one numerical instruction, and the other 19 classes as a list, since the class key does not decide them; the note's per-graph split, reproduced during its review by an independent enumerator, gives the reason for every graph. [One-verdict loops, exit code and LOAD loops without arithmetic](one-verdict-loops-exit-code-and-load-loops-without-arithmetic.md)

Rules 1–3 cover 887 classes: 556 with no recurrent LOAD, 286 with no recurrent numerical site, and 45 read-only with one numerical site.

**Normalisations** made before applying the rules (manuscript, checked during review):
- A recurrent part made only of branches cannot be traversed twice on a halting run, so it is treated as acyclic code.
- A recurrent part whose only data instructions are STOREs repeats its full state after one traversal. Its STOREs are treated as one-time STOREs. This can move a class only to REDUCES, never to EXCLUDED. The one such class that rule 5 excludes, L1S1A1B3 `C:AL C:S |par`, is excluded by Lemma V, whose proof allows a STORE-only loop before the LOAD loop.

**REDUCES (36 classes).**
- **26:** a five-slot data schedule with a data instruction before the cycle, or a LOAD on an exit path. Each has graphs whose LOAD loop reaches both verdicts, 13,416 in all.
- **10:** a read-only loop with one recurrent numerical site, plus one-time numerical instructions, LOADs or STOREs (1 class has a STORE) or a computation-only loop. Each has graphs in which a numerical instruction or a STORE runs before a LOAD loop that reaches both verdicts, 23,832 in all. The one-site theorem as written forbids STOREs and a second numerical site, and its parity and cursor rows, as written, do not cover a length-dependent word computed or planted before the loop.

Rule 5 excluded the other 7 five-slot-schedule classes, the other 12 one-site classes and all 18 classes with a LOAD loop beside a numerical loop.

**OPEN (14 classes).**
- Twelve simple six-instruction cycles with four data instructions, the necklace counts 3 + 3 + 3 + 2 + 1:
  - L1S1A2B2: `AALS`, `AASL`, `ALAS`;
  - L1S2A1B2: `ALSS`, `ASLS`, `ASSL`;
  - L2S1A1B2: `ALLS`, `ALSL`, `ASLL`;
  - L2S0A2B2: `AALL`, `ALAL`;
  - L1S0A3B2: `AAAL`.
- Two two-cycle classes with three branches: L1S0A2B3 `G{LAA}` and L1S1A1B3 `G{LSA}`, with 51,840 labeled graphs each.

Within the open cycles, journal theorems already cover some members at the operand level:
- the two-ahead lock is an any-speed member of L1S1A2B2 `ALAS`; one realization is L, A(q←p+2d), S, A(p←p+d);
- the one-accumulator scan with an arbitrary public unary orbit covers some read-only operand choices;
- even literal multipliers (and a = w) with an odd literal stride, under native initialization, are any-speed members of L1S1A2B2 `AALS`, `AASL` and `ALAS` ([covered swaps](even-multiplier-scans-with-odd-strides-fail-at-every-speed.md)).

These cover operand subcases, not whole classes. [Six-slot two-ahead lock](six-slot-two-ahead-lock.md) · [Two-ahead stores in a six-slot scan](two-ahead-stores-in-a-six-slot-scan.md) · [Any unary orbit](one-accumulator-scan-without-a-clock.md#any-unary-orbit-of-public-read-addresses)

## 3. The writable cycle with one prologue numerical instruction

**Choice.** Among the unexcluded classes, the one that breaks the fewest five-slot hypotheses is L1S1A2B2 `C:ALS` or `C:ASL` with `pre:A`, with 480 labeled graphs each. In it the five-slot writable cycle is unchanged, and one numerical instruction runs once before the first LOAD. It writes a public length-dependent word z, computed from 0, n, w and literals. For example, `rotr 1 1` gives Q/2, and `add n 1` is odd. Relative to five slots this changes two things:
- (H1) the cursor or loaded register may start at z, which can be odd;
- (H2) a third immutable register z can serve as a stride, payload, marker or fixed address. In the five-slot proofs these are fixed integers or the even words 0, n, w.

**Row-by-row check** of the writable split (manuscript reasoning):

| five-slot row | survives? | reason |
|---|---|---|
| fixed scratch address a (writable five-slot note, first section) | yes | the private sites are chosen after the length is fixed, so they can avoid a = z as well |
| coincident LOAD/ALU destination (adaptive-prefix note) | yes | a fixed payload z only adds one word to the palette |
| self-addressed LOAD x←M[x] | yes | the palette argument gains one word |
| bitwise / shift / comparison palette rows | yes | z adds one word to the bounded palette |
| multiplication y←y·x with a register or fixed payload (y←x·x ignores y and belongs to the f(x) rows) | yes | in order LAS with STORE at y every LOAD after the first reads a stored word; otherwise at most one of x0, y0 is odd (only one register receives z), so the first update gives an even y and y stays even, missing odd sensitive addresses |
| raw-word writes M[x]←x, M[x]←c (table argument) | yes | the set B gains z and x0; the translations still avoid B |
| y←f(x) rows (orbit prefixes, valid for any fixed-on-length f) | yes, except possibly the unary reverse-link row, whose even-base hypothesis was not re-checked | — |
| **ALU uses both registers, additive: y+x, y−x, x−y (parity row)** | **no as written; repaired for register payloads (Section 4)** | the invariant "all registers and memory stay even" fails. With y0 = z odd and a STORE copying y, odd words enter memory, and reading one flips the cursor's parity. Lemmas A and B close every register-payload subrow, and parity invariance closes even fixed payloads. The odd fixed payload remains (the odd-marker row) |
| y←y+d (unary scan) with d = z | **no as written** | the owner-change count O_d(1) per lap, and the shifted crossed scan of the arbitrary-stride note ("fixed odd integer d"), assume a fixed d. Placing the pins after the scan order, the device of the one-accumulator note, should repair the communication rows because the orbit is public. Nothing in hand covers the shifted crossed scan with a length-dependent d |
| odd fixed marker at the cursor (odd-marker note) with c = z | not re-checked | — |

[Coincident register destinations](adaptive-five-slot-prefixes-without-a-clock.md#coincident-register-destinations) · [Arbitrary stride](arbitrary-stride-private-sign-erasure.md) · [Odd markers](odd-self-marked-cursors-without-a-clock.md)

**Finite check of the failing parity row.**
- Base: a synthetic even periodic base at w = 16, made of 8 even header words, k tail words equal to R, and zero elsewhere.
- Command: `python3 odd_start_parity_rows.py` (about 2 s).
- Grid: 54 operand subrows, i.e. y←y+x, y−x or x−y; STORE address and payload each in {x, y, z}; orders LSA and LAS. Parameters y0 ∈ {1, 9, 257, 32769}, z ∈ {1, 32769}, R = 0x2A20.
- Every subrow reads at most [1, 1] or [1, 2] distinct original tail words for k = [500, 2000], and the last line is:

```
rows whose count reaches k/4 at the largest k: 0
```

These runs stop at 4·k+2000 turns, which is less than one lap of Q = 65,536. The long reruns below remove that limitation.

**Adversarial check of the self-mark escape.**
- Mechanism: once the cursor reads a zero cell it stays, or alternates between y and −y, unless the STORE writes a nonzero word into the current cell. That happens with the self-mark M[y]←y or a fixed marker M[y]←z.
- Command: `python3 odd_start_self_mark_escape.py` (about 12 s).
- Grid: 40 tail words R with bytes in [10, 56], 3 ops, 2 orders, 9 odd y0.

```
k=500: max distinct original tail reads = 2 at ('0x1016', 'y+x', 'LSA', 9)  (40 R values x 3 ops x 2 orders x 9 y0)
k=2000: max distinct original tail reads = 5 at ('0x2422', 'y+x', 'LSA', 1001)  (40 R values x 3 ops x 2 orders x 9 y0)
```

**Long-horizon reruns.** `python3 odd_start_self_mark_long_runs.py` (about 2.5 minutes) reruns the worst self-mark case and the register-payload subrows at 2,000,000 turns. The second line covers 36 subrows (STORE address x, y or z), with y0 ∈ {1, 9, 32769} and z ∈ {1, 32769}:

```
self-mark worst case k=2000 R=0x2422 y+x LSA y0=1001: [(16000, 5), (2000000, 5)]
register-payload rows (payload x or y), k=500, 2,000,000 turns: max distinct original tail reads = 1 at ('y+x', 'x', 'x', 'LSA', 9, 1)
```

`python3 odd_start_long_horizon_runs.py` (about 6 s) runs the fixed odd marker M[y]←z, and one self-mark case, for up to 3,000,000 turns:

```
fixed odd marker M[y]<-z, z=1 [(100000, 1), (1000000, 10), (3000000, 46)]
fixed odd marker M[y]<-z, z=1, k=2000 [(100000, 1), (1000000, 10), (3000000, 46)]
fixed odd marker M[y]<-z, z=3, y-x [(100000, 3), (1000000, 52), (3000000, 162)]
self-mark M[y]<-y, y+x, k=500 [(100000, 1), (1000000, 1), (3000000, 1)]
```

**What this shows.**
- Register-payload members of the failing row are still defeated on these bases by missed originals, through a trap rather than parity. This is a check at finite size only; Section 4 proves it.
- Fixed-odd-marker members read new originals indefinitely, so missed originals cannot close them. In five slots these are the odd-marker row: a fixed odd program integer c, closed by its own color-interval argument. Here c = z may be length-dependent, and the cursor may start odd. Whether that proof survives is not re-checked; its 2|c| crossing bound does assume a fixed c.

## 4. The zero-trap lemma for register payloads

These proofs are at manuscript level and were checked at finite size.

**Setting.** A memory image with:
- input region I=[0,L), where L=o(Q);
- zero outside I;
- every word in I nonzero and below Q/2;
- every full word of I, header words included, of circular norm above 2L. Only the last partial word, at address L−1, may be small; it carries the final newline;
- every tail word R of circular norm at least cQ, for a fixed c>0.

The five-slot property-1 base satisfies all of these. Let H be its word palette. Let P be H together with the public words of the prologue and the first partial turn (y0, x0, and any public prologue address or payload).

The continuing cycle is x←M[y]; y←y+x, y−x or x−y; STORE M[a]←b with a,b ∈ {x,y}. Exits are allowed anywhere. A turn is LSA or LAS: the cyclic order of LOAD, STORE, numerical.

**Lemma A (zero trap).** Take a STORE among M[x]←x and M[x]←y in either order, or M[y]←x in order LSA. Call a tail address a *exceptional* if a+R, a−R, R−a or the negative of one of them lies in P, where R=M_0[a]. There are at most 6·|{tail values}|·|P| = O(1) exceptional addresses. Suppose the continuing run reads the original word at a non-exceptional tail address a at turn t. Then from turn t+1 onward the cursor stays forever in {v} for y±x, or alternates in {v,−v} for x−y, where v is the next cursor. Both cells hold 0 there. Every later STORE either writes address 0 (STORE at x), or writes back into the trap cell the 0 it just read (M[y]←x in order LSA), so the trap cells keep the value 0. So a continuing run reads at most 1+O(1) distinct original tail words.

*Proof.*
1. **Two invariants.**
   - (i) For a STORE at x, the STORE address of each turn is the word the LOAD of that turn returned, or x0 in the first partial turn. For M[y]←x in order LSA the STORE writes back the word just read, so after the first partial turn memory never changes, and step 2 holds for it at once.
   - (ii) Every word ever written is in P, or is a cursor value. For payload y it is the current cursor (LSA) or the next cursor (LAS); payload x copies a word already in memory; M[y]←x in order LSA writes back what was just read.
2. **First visits find zero.** Let v ∉ I∪P be visited for the first time at turn τ. By (ii), the word v is in memory before turn τ's LOAD only if it was written as a cursor payload. That happens only during turn τ−1 (LAS), after that turn's LOAD, or during turn τ (LSA), after the LOAD. So no LOAD before turn τ returned v, and by (i) address v was never written. Hence M[v]=0 at turn τ.
3. **The cursor stays.** With y±x, x=0 leaves y=v, and the STORE goes to address 0 ≠ v. So the next read of v returns 0 again, and so on forever. With x−y, the cursor moves to −v. The same reasoning applies there provided −v ∉ I∪P, and it shows that −v is also first visited and holds 0. The cursor then returns to v, whose cell is still 0, since only address 0 was written.
4. **The trap is reached.** After the original R is read at a, the next cursor v ∈ {a+R, a−R, R−a} lies outside I, because the norm of R is at least cQ and a<L. It is outside P because a is not exceptional. If v had been visited earlier, the run would have been trapped then and could not have reached a. So this is v's first visit. ∎

**Lemma B (STORE at y).**
- In order LAS, any STORE at y writes the cell that the next LOAD reads, so every LOAD after the first returns a stored word. This is the five-slot destruction argument.
- In order LSA with the self-mark M[y]←y, every written cell holds its own address. So the next cursor is y+M_0[y], y−M_0[y] or M_0[y]−y on a first visit, and 2y, 0 or 0 on a revisit.
  - From a full word of I, a first visit leaves I, because the word is below Q/2 and of norm above 2L.
  - The small last word f at L−1 sends y+x to L−1+f ≥ L, so out of I. It sends y−x, and x−y after one reflection, to the single position L−1−f.
  - From a zero cell outside I, a first visit stays put (y±x) or reflects to −y (x−y).
  - Hence with y+x, every position of I visited after the first LOAD is a doubled position, so it is **even**.
  - With y−x, every such position is **0 or L−1−f**.
  - With x−y, every such position is **0, L−1−f, or the negative of a public first-turn word such as −y0**: reflections of words M_0[a]−a never land in I.
  - In each case, beyond the even positions, there are O(1) public positions. They come from the first partial turn, which may run the STORE or the numerical site on x0 and y0 before the first LOAD.
- In all three cases a continuing run reads O(1) original words at odd tail addresses.

**Consequence.** On the five-slot property-1 family, take any program of the class of Section 3 whose recurrent row is the additive parity row with a register payload. The family has consecutive sensitive tail words, so unboundedly many at odd addresses. The program misses all but O(1) of the sensitive words at odd addresses, so it errs on an edited input, at any speed and for every public y0 and x0. For the self-mark with y+x, Lemma B restricts only the odd positions; such a run may read even ones, and the long self-mark rerun reads 5. This replaces the failing parity invariant for register payloads.

The parity argument also extends to a fixed **even** payload M[·]←c. Every loaded word is then even, so the parity of y never changes after the first LOAD, and the other parity class is missed. This case is manuscript only; it was not run.

**Check.** `python3 zero_trap_lemma_check.py` (about a minute) runs synthetic bases at w = 16:
- 12 random bases;
- 1 to 3 tail values with bytes in [10,56];
- even header words of ASCII bytes;
- a small last word, the value 10;
- k ∈ {300, 1000, 3000};
- all 24 register-payload subrows;
- all three entry points of each cyclic order, so the first partial turn may run the STORE and the numerical site on x0 and y0 before the first LOAD;
- y0 odd inside I with probability 3/4, otherwise uniform; x0 uniform with probability 1/2, otherwise 0;
- 3·Q turns per run.

Runs that start on a zero cell outside I are trapped at once and are uninformative. 362 of the 864 runs read at least one original tail word. The P used for exceptional addresses includes y0±x0 and x0−y0.

```
runs that read at least one original tail word: 362
T1: runs=540 violations=0 max distinct original tail reads in a run=1
T2: runs=216 violations=0 max distinct original tail reads in a run=1
T3: runs=108 violations=0 max distinct original tail reads in a run=1
```

The three checks:
- **T1** is Lemma A.
- **T2** is the LAS part of Lemma B in its exact form: no LOAD after the first reads a cell that was never written, inside or outside I.
- **T3** is the self-mark part of Lemma B. It checks the predicted parity, or the predicted positions, of every later original read.

**Independent check.** `zero_trap_lemma_independent_check.py` was written during review from the lemma statements alone. It uses words of any parity, Q ∈ {4096, 65536}, all 24 subrows, all three entry points and random public y0, x0, over 2Q turns. Besides the count, it checks that after the first non-exceptional read the cursor stays on zero cells. Seeds 1, 2 and 3 give 11,232 runs, 4,401 of which read an original tail word, and no violation:

```
subrows 24 runs 3744 informative (read >=1 original tail word) 1447 violations 0
subrows 24 runs 3744 informative (read >=1 original tail word) 1474 violations 0
subrows 24 runs 3744 informative (read >=1 original tail word) 1480 violations 0
```

With `--edge` the tail values are edge cases (Q/2−1, (Q−a)/2, 2L+1, Q/2−L) and the last word is f ∈ {1, L−2}. Seeds 11 and 12 give 7,488 more runs, again with no violation:

```
subrows 24 runs 3744 informative (read >=1 original tail word) 1494 violations 0
subrows 24 runs 3744 informative (read >=1 original tail word) 1423 violations 0
```

The norm hypothesis is needed. With `--norm-floor-cq`, tail values need only norm above cQ, which at Q = 4096 and L = 100 is 160, below 2L = 200. Seed 1 then draws a tail word of norm 174, and the check reports 4 violations, all for x−y, where R−a lands back in I:

```
subrows 24 runs 3744 informative (read >=1 original tail word) 1448 violations 4
VIOLATION (4096, 100, ('x-y', 'LSA', 'xx'), 'L', 86, 70, [86, 88])
VIOLATION (4096, 100, ('x-y', 'LSA', 'yx'), 'L', 83, 3176, [83, 91])
VIOLATION (4096, 100, ('x-y', 'LAS', 'xx'), 'L', 90, 77, [84, 90])
VIOLATION (4096, 100, ('x-y', 'LAS', 'xx'), 'S', 79, 66, [79, 95])
```

**Effect on the counts.** None. The class L1S1A2B2 `C:ALS`/`C:ASL` + `pre:A` still contains three rows that are not closed:
- the odd fixed marker M[y]←c, with c odd and possibly length-dependent;
- the unary scan y←y+z with a length-dependent stride;
- the unary reverse-link row.

So it stays REDUCES, and Lemmas A and B change no total. What is newly closed, at every speed (manuscript), is an operand subclass: the register-payload part of the additive parity row of that class. The same lemmas hold for any public initial cursor. So they also close this subrow wherever a prologue makes the starting registers public but arbitrary.

## 5. The three standard tests

No time lower bound is claimed; this is a statement about program size.
- **(a) Fast globally correct solver for the hard families?** Yes. The witness families (periodic sign edits, equality files, table files) have fast packed-scan solvers, and a 43-instruction program decides the whole input class. The classification bounds program size only.
- **(b) Same bound for 2-SAT?** Yes. The arguments use only sensitivity, equality embedded in the syntax and the bounded word palette, all of which 2-CNF encodings also have. So "no six-slot program decides X" arguments of this kind would apply equally to 2-SAT, and they say nothing about SAT's hardness.
- **(c) Relativization.** Both relativized models fail at the same step: the use that one LOAD returns one w-bit word from a bounded palette, which underlies missed originals, probe contexts and handoff counts.
  - In the packed oracle of the relativized-clock note, a constant number of instructions with one query on the whole input decides SAT.
  - In the multilinear oracle, the same holds with Boolean queries.

  The classification is not a lower bound and so is not subject to these tests, but any extension of it must keep using the O(w)-bit per-instruction restriction. [Relativized clock](relativized-clock.md) · [Multilinear oracle](multilinear-oracle-clock.md)

## 6. Exact obstruction and next step

- **First failing row in the simplest class.** In "five-slot writable cycle + one prologue numerical instruction", the parity row fails. The precise false statement is: "When STORE copies a register or an even fixed payload, all registers and memory stay even on the periodic base" (the five-slot loop note, "The ALU uses both mutable registers"). It is false once y0 is odd. [Which operation can generate the addresses?](five-instruction-loops-on-dimacs-sat.md#which-operation-can-generate-the-addresses)
- **Repaired for register payloads (Section 4).** Lemma A (zero trap) and Lemma B (STORE at y) replace parity for every register-payload subrow, at every speed and from any public start (manuscript proofs plus a finite check). A STORE address z, which is fixed, falls under the fixed-scratch row; an even fixed payload falls under parity invariance.
- **Remaining part of the parity row: the odd fixed marker M[y]←c.** Here c is a literal or the length-dependent prologue word z. Such members read about one new original per lap, so no missed-original argument can work. They need the odd-marker proof re-checked with a possibly length-dependent marker and an odd starting cursor.
- **Second obstruction.** Fixed-stride rows with a length-dependent odd stride z. The shifted crossed scan for a non-fixed stride is the one row without a proposed repair.
- **Other classes.** For the 12 open six-instruction cycles and the 2 two-cycle classes, the next step is the operand enumeration, at the grain of the read-only two-ALU audit. For the single-numerical-site mixes (L1S2A1B2, L2S1A1B2) the parity and palette analysis restricts the numerical site to an odd translation or the marker forms, so those mixes have the smallest operand spaces. [Read-only two-ALU audit](../audits/read_only_two_alu_audit.py)

## 7. What is not proved

- Sections 3 and 4 newly exclude no six-slot class.
- The 969 EXCLUDED marks rest on the cited manuscript theorems. They also rest on this note's manuscript contraction and exit-test arguments: dead branch sides, self-loops, branch-only and STORE-only loops, extra exit branches. Rule 4 alone accounts for 45 classes; four of them also rest on the round-four note's argument and three on the round-five note's Lemma P (both manuscript), and among the four only `post:A` uses the exit-code extension. That every row of the writable and read-only five-slot proofs tolerates any exit function, extra exit tests and public entry points was checked during review in the shape of the argument, not row by row.
- Fourteen of the 45 rule-4 classes, and the 12 contraction rows of the four mixes with a STORE (L1S1A2B2, L1S2A1B2, L2S1A1B2, L1S1A1B3), rest on row W5 of the writable split. W5 holds by the private-probe lemma for the writable machine in Section 4 of the case-split note. The 887 classes of rules 1–3, the other 31 rule-4 classes and Lemmas A and B do not depend on W5.
- The 37 classes of rule 5 rest on the round-six note's manuscript lemmas: Lemma V and the phase lemma on property 1 alone, Lemma E on the one-site theorem's proof read row by row as invariants of the run before the one-time code. They also rest on that note's per-graph split, which an independent enumerator reproduced during its review.
- The 36 REDUCES classes are unchecked.
- The enumeration is a computation. An independent enumeration written during review reproduces its classes, labeled counts and the exclusions of rules 1–4, and a second one the per-graph split behind rule 5, but the marking rules themselves are manuscript arguments. Operands, opcodes and literals were not enumerated, except within the class of Section 3.
- In the table of Section 3, only the multiplication and parity rows were re-checked during review. The orbit-prefix, reverse-link and coincident-destination rows with an odd start were not.
- Lemmas A and B, and the even-payload parity remark, are manuscript proofs with no Lean check. They were tested only on synthetic bases (w = 16, and also w = 12 in the independent check), not on the journal's exact DIMACS layout; that property 1 implies the Setting was checked by reading. They close an operand subclass, not a control class. The odd fixed marker, the length-dependent stride rows and the unary reverse-link row of the class of Section 3 remain unchecked.

## Reproducing the checks

Run from `audits/`. No script writes files unless given `--out DIR`.

```
python3 six_slot_control_class_marking.py
python3 six_slot_control_class_cross_check.py
python3 odd_start_parity_rows.py
python3 odd_start_self_mark_escape.py
python3 odd_start_long_horizon_runs.py
python3 odd_start_self_mark_long_runs.py
python3 zero_trap_lemma_check.py
python3 zero_trap_lemma_independent_check.py
```

The marking script compiles `six_slot_control_classes.cpp` into a temporary directory, runs it for 2, 3 and 4 branches, and marks the classes. It then checks that the class table and the summary are byte-identical to `six_slot_control_classes.tsv` and `six_slot_control_class_summary.txt`, which takes about 40 seconds. With `--enumerated DIR` it reads saved enumerator output instead, and `--out DIR` writes the table and the summary. The cross-check compiles the review's enumerator, `six_slot_control_classes_independent.cpp`, and compares its output with the table and with the round-six note's three class lists, in about 10 seconds. The simulations take the times given above. The independent zero-trap check takes about 35 seconds per run; `--seed 2`, `--seed 3`, `--edge --seed 11`, `--edge --seed 12` and `--norm-floor-cq` give the other runs quoted in Section 4. [Marking](../audits/six_slot_control_class_marking.py) · [Enumerator](../audits/six_slot_control_classes.cpp) · [Independent enumerator](../audits/six_slot_control_classes_independent.cpp) · [Cross-check](../audits/six_slot_control_class_cross_check.py) · [Independent zero-trap check](../audits/zero_trap_lemma_independent_check.py)
