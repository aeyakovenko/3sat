# One-verdict loops, exit code and LOAD loops without arithmetic exclude 37 more six-instruction classes

A LOAD loop with no numerical instruction loads only original words, the address it has just read, or one of boundedly many stored values; so on the property-1 base it reads a set of addresses bounded independently of the length, and the program errs or diverges on the base or on one of its sign edits for every sufficiently large base. This phase lemma, with its hypothesis on memory at the loop's entry checked class by class, excludes all 18 two-loop classes of the six-instruction map. Lemma E, which opens the one-site theorem's proof for one-time code that runs only after the exit or on a bypass, and Lemma V, for a LOAD loop from which only one verdict is reachable, exclude 12 of the 22 one-site classes; the other 10 keep 23,832 labeled graphs in which one-time code runs before a loop that still reaches both verdicts. Lemma V also excludes 7 of the 33 five-slot-schedule classes. The map moves from 932/73/14 to 969/36/14, and an independent enumerator written during review reproduces the per-graph split and both recounts. The lemmas are manuscript proofs, and nothing here is a time bound; the linear, quadratic and cubic questions remain open. [Six-instruction map](six-instruction-control-classes-in-the-five-slot-machine.md) · [One arithmetic site](read-only-ram-with-one-arithmetic-site.md) · [Property 1](five-instruction-loops-on-dimacs-sat.md#two-properties-of-the-encoding)

## Setting

The model is the five-slot machine of [five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md):
- width w = 16⌈log₂(N + 2)/16⌉ and Q = 2^w;
- registers start at 0, apart from the public N and w;
- literals are fixed integers reduced mod Q;
- LOAD and STORE take a register or an immediate as address, and a STORE payload may be a register or a literal;
- there is no implicit increment.

Classes, labeled graphs and the positions pre, post, mid and none are those of the [six-instruction map](six-instruction-control-classes-in-the-five-slot-machine.md). **Property 1** is the periodic even-word base of [five-instruction loops](five-instruction-loops-on-dimacs-sat.md#two-properties-of-the-encoding):
- for each j, a satisfiable base with 10^j clauses at one length n_j, with k = Θ(N/w) tail words, each of which has a same-length sign edit that makes the formula unsatisfiable;
- every base word is even, and the palette H of word values, zero included, has bounded size;
- "If its original contents were not loaded before an overwrite or a verdict, the alternative formula would receive the same answer."

The journal's layout audit of this family was run at every j from 3 to 1199, and its assertions hold from j = 61 to 1199, as recorded in the [round-five note on prologue branches](prologue-branches-are-fixed-jumps-at-each-length.md).

Throughout, **R** is the recurrent part (a nontrivial strongly connected component of the control graph) that contains a LOAD. In every labeled graph of the 73 classes treated here there is exactly one such part; Section 2 checks this per graph.

**The 73 classes** are the ones the map marked REDUCES before this note:
- 22 one-site classes: a read-only loop with one recurrent numerical site, plus one-time numerical instructions, LOADs or STOREs, or a computation-only loop;
- 18 two-loop classes: a LOAD loop with no numerical site beside a separate loop that has one;
- 33 five-slot-schedule classes: a five-slot data schedule with a data instruction before the cycle, or a LOAD on an exit path.

## 1. Three lemmas

**Lemma V (single-verdict LOAD loop).** Let P be any program with exactly one LOAD-bearing recurrent part R, and suppose only one verdict is reachable from R. Then for every sufficiently large base of property 1, P errs or diverges on that base or on one of its sign edits.

**Lemma E (exit and bypass code).** Let P be any program with these properties:
- exactly one LOAD-bearing recurrent part R;
- R contains exactly one numerical instruction ι and no STORE;
- every other numerical instruction and every STORE is post or none relative to R.

Then P does not decide DIMACS SAT, at any speed.

**Phase lemma.** Let P be any program with these properties:
- (i) every LOAD lies in one recurrent part R;
- (ii) R contains no numerical instruction;
- (iii) whenever a run enters R, every memory cell holds its original word, its own address, or a value in a set E. Here |E| ≤ e, and e depends only on the program.

Then every LOAD of every run reads an address in V = Z ∪ Λ ∪ H ∪ E, where:
- Z is the set of register values at entry to R (at most r values, for r registers);
- Λ is the set of program literals.

So on a property-1 base a run reads at most r + |Λ| + |H| + e distinct cells, a bound independent of j, and for every sufficiently large j, P errs or diverges on the base or on one of its sign edits (the family has one length n_j per j).

In all 18 two-loop classes the numerical loop contains no LOAD and the LOAD loop contains no numerical instruction, so the phase lemma needs no one-site theorem. The closure of the registers at entry under memory is bounded only because of hypothesis (iii). That hypothesis has to be checked when a loop with a STORE runs first (Section 5), and it fails for a loop with two numerical sites (the control in Section 6).

## 2. The split of the 73 classes, per labeled graph

`six_slot_control_class_split.cpp` repeats the graph enumeration, the reductions and the coarse class key of the map's enumerator. For each kept labeled graph it adds:
- the LOAD-bearing recurrent parts, flagged if there is more than one;
- whether R reaches both verdicts;
- the numbers of numerical instructions and STOREs in R;
- the position relative to R of every numerical instruction outside R and every STORE;
- for the two-loop classes, where the STORE sits and the order of the numerical loop relative to R.

Positions are taken relative to R because the class table's positions are relative to *any* recurrent part, including a branch-only `C:-` and a computation-only `C:A`. In a one-site class, let U be the extra instructions: every numerical instruction other than the single one inside R, and every STORE. Each u ∈ U is:
- pre: u reaches R and is not reachable from R;
- post: u is reachable from R and does not reach R;
- none: neither.

No U instruction can be mid relative to R: an instruction outside R that reached R and was reachable from R would lie in R. Each graph of a one-site class gets one of three types:
- **E**: every U instruction is post or none relative to R, and R reaches both verdicts;
- **1V**: R reaches only one verdict;
- **PRE**: some U instruction is pre relative to R, and R reaches both verdicts.

`python3 six_slot_control_class_split.py` compiles the enumerator, runs it on the seven opcode mixes that hold the 73 classes, checks it against the class table, and regenerates the three class lists `six_slot_one_site_class_split.tsv`, `six_slot_two_loop_class_split.tsv` and `six_slot_five_slot_schedule_class_split.tsv`, which it compares byte for byte with the stored ones. It begins:

```
1. class keys of the seven mixes equal the class table: True (779 classes); labeled counts equal: True
   L1S0A2B3 total labeled = 67436544 kept = 345276
   L1S1A1B3 total labeled = 67436544 kept = 345276
   L2S0A2B2 total labeled = 19267584 kept = 25200
   L1S0A3B2 total labeled = 19267584 kept = 25200
   L1S1A2B2 total labeled = 19267584 kept = 25200
   L1S2A1B2 total labeled = 19267584 kept = 25200
   L2S1A1B2 total labeled = 19267584 kept = 25200
2. one-site classes with one recurrent part whose per-graph positions relative to R equal the table key: 18 classes, 75696 labeled graphs, all equal
```

The kept totals are the map's: 25,200 labeled graphs per mix with two branches and 345,276 per mix with three. Line 2 ties the new positions to the map's own labels. In a class with one recurrent part, "relative to R" and "relative to any recurrent part" coincide, so in the 18 one-site classes with one recurrent part the positions in every graph must equal the table key, and they do. The other 4 one-site classes have two recurrent parts, and in them the new positions are the point.

**The 22 one-site classes** (full table: `six_slot_one_site_class_split.tsv`):

```
  L1S0A2B3  C:- C:AL |seq    mid:A,             lab=432    E=144    1V=288    PRE=0      MOVES(E+1V)
  L1S0A2B3  C:- C:AL |seq    pre:A,             lab=432    E=0      1V=288    PRE=144    STAYS(mixed)
  L1S0A2B3  C:A C:AL |par    -                  lab=288    E=0      1V=288    PRE=0      MOVES(1V only)
  L1S0A2B3  C:A C:AL |seq    -                  lab=4464   E=2016   1V=1728   PRE=720    STAYS(mixed)
  L1S0A2B3  C:AL             pre:A,             lab=10656  E=0      1V=4896   PRE=5760   STAYS(mixed)
  L1S0A2B3  G{LA}            none:A,            lab=2016   E=0      1V=2016   PRE=0      MOVES(1V only)
  L1S0A2B3  G{LA}            post:A,            lab=22320  E=20304  1V=2016   PRE=0      MOVES(E+1V)
  L1S0A2B3  G{LA}            pre:A,             lab=13680  E=0      1V=4032   PRE=9648   STAYS(mixed)
  L1S0A3B2  C:AL             none:A,pre:A,      lab=288    E=0      1V=288    PRE=0      MOVES(1V only)
  L1S0A3B2  C:AL             post:A,pre:A,      lab=1080   E=0      1V=288    PRE=792    STAYS(mixed)
  L1S0A3B2  C:AL             pre:A,pre:A,       lab=792    E=0      1V=432    PRE=360    STAYS(mixed)
  L1S1A1B3  G{LA}            none:S,            lab=1008   E=0      1V=1008   PRE=0      MOVES(1V only)
  L1S1A1B3  G{LA}            post:S,            lab=11160  E=10152  1V=1008   PRE=0      MOVES(E+1V)
  L1S1A1B3  G{LA}            pre:S,             lab=6840   E=0      1V=2016   PRE=4824   STAYS(mixed)
  L2S0A2B2  C:AL             none:A,post:L,     lab=96     E=0      1V=96     PRE=0      MOVES(1V only)
  L2S0A2B2  C:AL             none:A,pre:L,      lab=192    E=0      1V=192    PRE=0      MOVES(1V only)
  L2S0A2B2  C:AL             none:L,pre:A,      lab=192    E=0      1V=192    PRE=0      MOVES(1V only)
  L2S0A2B2  C:AL             post:A,post:L,     lab=1920   E=1728   1V=192    PRE=0      MOVES(E+1V)
  L2S0A2B2  C:AL             post:A,pre:L,      lab=720    E=528    1V=192    PRE=0      MOVES(E+1V)
  L2S0A2B2  C:AL             post:L,pre:A,      lab=720    E=0      1V=192    PRE=528    STAYS(mixed)
  L2S0A2B2  C:AL             pre:A,pre:L,       lab=1056   E=0      1V=576    PRE=480    STAYS(mixed)
  L2S0A2B2  C:ALL            pre:A,             lab=960    E=0      1V=384    PRE=576    STAYS(mixed)
   moved: 12 classes (7 all 1V), 40632 graphs: E 32856, 1V 7776, PRE 0
   staying: 10 classes, 40680 graphs: PRE 23832, E 2016, 1V 14832; classes with PRE in every graph: 0
```

By position of the one-time code relative to R:
- **12 classes** have no PRE graph. In 7 of them every graph is 1V; in the other 5 the graphs are E or 1V. Together they hold 40,632 labeled graphs: 32,856 E and 7,776 1V.
- **10 classes** contain PRE graphs. Their 40,680 labeled graphs are 23,832 PRE, 2,016 E and 14,832 1V.
- No class has PRE in every graph.

Two of the 12 have pre code in the class key but no PRE graph, `C:AL none:A,pre:A` and `C:AL none:L,pre:A`. In a two-branch mix a bypass instruction needs a prologue branch, which leaves the cycle one branch and so one verdict. One class is not what its key suggests: in `C:- C:AL |seq mid:A`, the 144 graphs with the order `C:AL → A → C:-` are E, and the 288 graphs with the order `C:- → A → C:AL` are all 1V. Of the two classes whose key leaves the order of the two recurrent parts open, `C:A C:AL |seq` keeps 720 PRE graphs, with the numerical loop first and two verdicts, and `C:- C:AL |seq mid:A` has none.

**The 18 two-loop classes** (full table: `six_slot_two_loop_class_split.tsv`). In all 16,632 labeled graphs every LOAD lies in R and R has no numerical instruction, which are hypotheses (i) and (ii) of the phase lemma. The STORE sits:
- nowhere (8 classes, L1S0A2B3);
- in a one-time instruction, pre, post or none relative to R (6 classes);
- inside R, `C:A C:LS` (2 classes);
- inside the numerical loop, `C:AS C:L` (2 classes). That loop has exactly one numerical instruction, one STORE and no LOAD in every graph.

The numerical loop comes first in 1,152 of the 2,232 `C:AS C:L |seq` graphs:

```
  L1S1A1B3  C:AS C:L |seq    -        lab=2232  PH=2232  R1V=1008  stores={'S-in-numSCC(A1,S1,L0)': 2232} orders={'R-first;': 1080, 'num-first;': 1152}
   18 classes, 16632 labeled graphs, all of shape PH
```

**The 33 five-slot-schedule classes** (full table: `six_slot_five_slot_schedule_class_split.tsv`). No graph has two LOAD-bearing recurrent parts or none. Per class the script prints the graphs in which R reaches one verdict (1V) or both (2V), and then:

```
   all graphs single-verdict in 7 classes; single-verdict graphs 8448 of 21864; the other 26 classes keep 13416 two-verdict graphs

   regenerated lists identical to six_slot_one_site_class_split.tsv: True, six_slot_two_loop_class_split.tsv: True, six_slot_five_slot_schedule_class_split.tsv: True
```

Six of the seven are two-branch classes with a `none` instruction, where the bypass needs a prologue branch and leaves the cycle one branch: L1S1A2B2 `C:AL none:A,pre:S` and `C:AL none:S,pre:A`, L1S2A1B2 `C:AL none:S,pre:S`, and L2S1A1B2 `C:AL none:L,pre:S`, `C:AL none:S,post:L` and `C:AL none:S,pre:L`. The seventh is L1S1A1B3 `C:AL C:S |par`, whose three branches are split one each among the prologue, the STORE loop and the LOAD loop.

**Independent check during review.** An enumerator written during review from the map's class definitions, not from the journal's code, uses breadth-first reachability, Tarjan's strongly connected components, a simple-cycle test by internal edge count, and start vertices as weights. `python3 six_slot_control_class_split_independent_check.py` runs it on nine mixes and compares it with the class table and the three lists. Among its lines:

```
1. keys equal (9 mixes): True 943 943
   labeled counts equal: True
   L2S0A2B2 C:AL            post:A,post:L,   lab=1920   E=1728   1V=192    PRE=0      MOVES same  E-graphs-with-LOAD-after-U=624
   mismatches vs list: 0  moved: 12 {'mv_lab': 40632, 'mv_E': 32856, 'mv_1V': 7776, 'mv_PRE': 0, 'st_lab': 40680, 'st_E': 2016, 'st_1V': 14832, 'st_PRE': 23832}
   L1S1A1B3 C:AS C:L |seq   -        lab=2232  (i)+(ii) all; V1=1008  list_V1=1008  stores={'S-in-SCC(A1,S1,L0)': 1152, 'S-in-SCC(A1,S1,L0)+dataBefore': 1080} orders={'R-first;': 1080, 'num-first;': 1152}
   two-loop labeled total: 16632  mismatches vs list: 0
   single-verdict graphs 8448 of 21864 ; all-single-verdict classes: 7  mismatches vs list: 0
5. listed classes 73; moved by these predicates 37; the table's EXCLUDED listed classes are exactly these and its REDUCES classes are the other 36: True
```

It reproduces the class keys and labeled counts of all 943 classes in the nine mixes, the E, 1V and PRE counts of every one-site class, hypotheses (i) and (ii) in every two-loop graph with the STORE locations and loop orders, and the single-verdict counts of the 33. It also finds that among the E graphs a LOAD can follow a U instruction only in L2S0A2B2 `C:AL post:A,post:L`, in 624 of its 1,728 E graphs, and that in `C:AS C:L |seq` data instructions precede the STORE loop exactly in the 1,080 graphs where R comes first.

## 3. Proof of Lemma V

1. LOADs outside R lie on no cycle, since R is the only LOAD-bearing recurrent part. So each executes at most once per run. Let n₁ be their number; n₁ ≤ n_L.
2. Take a base of property 1 with k > n₁, and let ρ be P's run on it. If ρ diverges, P fails. So assume ρ halts.
3. Let S be the set of cells that ρ reads before it first enters R, or during the whole run if it never enters R. Then |S| ≤ n₁. Pick a sensitive tail word a ∉ S, and let ρ′ be the run on the sign edit at a.
4. By induction on steps, ρ′ agrees with ρ (same PC, registers, and memory except possibly at a) as long as ρ has not loaded the original word at a. So ρ′ agrees with ρ up to the entry into R, or to the verdict if ρ never enters R.
5. If ρ never enters R, the two runs give the same verdict on a satisfiable and an unsatisfiable formula.
6. Otherwise both runs enter R, from which only one verdict is reachable. If that verdict is NO, ρ already errs on the satisfiable base. If it is YES, ρ′ answers YES or diverges on the unsatisfiable edit, so it errs. ∎

This is a control-graph fact plus property 1. It uses no numerical semantics, so it holds whatever the one-time code computes, before or after R. STOREs before R, including a STORE-only loop, are allowed: the induction keeps the two memories equal except possibly at a, and a STORE at a makes them equal there.

The map already uses this principle informally for a two-branch cycle after a prologue branch (its rule 4: "with two branches the cycle then has a single verdict and the program is wrong anyway"), and so does the [even-multiplier note](even-multiplier-stores-in-a-six-slot-scan.md) ("A prologue branch before a one-verdict cycle gives a constant verdict at each length, which is wrong…"). Lemma V states it for any program with one LOAD-bearing recurrent part.

## 4. Proof of Lemma E

Let ρ be a halting run, let t* be the first time ρ executes an instruction of U (t* = ∞ if never), and let u be that instruction.

1. **Before t\*.** ρ executes only ι, LOADs, branches and jumps, and memory is the input image. So the prefix ρ[0, t*) is an execution of a read-only machine whose only numerical instruction is ι, started from the initial registers. This is the machine of the [one-site theorem](read-only-ram-with-one-arithmetic-site.md), which allows any control flow and any number of LOADs.
2. **After t\*.** No instruction of R is executed again, because u reaches no instruction of R. So only instructions outside R run. LOADs outside R lie on no cycle, so at most n₁ LOAD executions occur after t*. ι is the only numerical instruction inside R, so every other numerical instruction lies outside R.
3. **The rows on the even base.** These are the rows for a site that ignores the old y; move, constant, comparison, bitwise, shift and rotation; multiplication involving y; the additive forms with two mutable sources or a fixed even operand; and y ← c − y. Each row's argument is an invariant of executions of the read-only one-site machine from the initial registers, and so applies to the prefix:
   - either the prefix reads o(N/w) distinct cells, as the one-site note states: O(1) cells for the image rows and for y ← c − y, and O(w) per palette word for shifts and rotations;
   - or it reads no odd tail address apart from the O(1) literal addresses (the parity row).

   With at most n₁ more reads after t*, the base run misses a sensitive word that would have to be read, and the edit argument of Section 3 gives an error at every large base.
4. **The cursor row** (ι is y ← y + c, with c a fixed odd integer), on the theorem's equality family:
   - The theorem's protocol runs unchanged on the prefix.
   - Its bounds on resets and laps use only that a post-reset (PC, registers) state cannot repeat in a halting run of a deterministic machine with static memory. Memory is static on the prefix. A repetition before t* would make ρ cycle forever before t*, so the bounds hold for the prefix.
   - At t* the current owner sends the PC and the register tuple, O(r·w) bits.
   - After t*, both parties simulate ρ. Each of the at most n₁ later LOADs costs one word from the owner of its address. A later STORE has its address and value determined by the shared state, so both parties track it.
   - The total is O_P(w) bits. As in the theorem, this contradicts the rectangle bound for equality of k = Θ(N/log²N) private bits at every sufficiently large byte-aligned length, where the equality family exists. ∎

During review each non-cursor row was confirmed to be a closure invariant of executions from the initial registers, and the cursor row's bounds on resets and laps to use only the theorem's sentence "Repeating a post-reset state with the same PC and tuple would repeat the entire state of this read-only deterministic machine forever".

In the moved classes Lemma E is used in three strengths, recorded per class in Section 7:
- **A dead STORE** (`G{LA} post:S`). No LOAD follows it, since the only LOAD is in R. Deleting it is reduction R-d of [the case-split note](the-five-slot-case-split-is-exhaustive.md#5-four-reductions-the-case-split-uses-without-writing-out), "A STORE on an exit arm or side arm", and the result is a read-only one-site program covered by the theorem as written.
- **Numerical exit code with no later LOAD.** This is the extension the map already uses for rule 4's 24 `C:AL`/`C:ALL` classes ("the one-site theorem, used with exit code after the last LOAD").
- **A LOAD after numerical exit code.** This is possible only in L2S0A2B2 `C:AL post:A,post:L`, where post:L may follow post:A, in 624 of its 1,728 E graphs. It is the one new clause: in step 4 each later LOAD costs one word.

## 5. Proof of the phase lemma, and hypothesis (iii) for the 18 classes

*Proof.* R is entered at most once, since a run that leaves a strongly connected component cannot return to it. Induct over the steps spent in R with two invariants: (a) every register value lies in V; (b) every cell holds its original word, its own address, or a value in V.
- At entry, (a) holds because Z ⊆ V, and (b) holds by (iii), since E ⊆ V.
- A LOAD reads an address a ∈ V (register) or a ∈ Λ (immediate). It returns an original word in H, the address a itself, or a value in V, so (a) is kept.
- A STORE, possible only in `C:A C:LS`, writes a value in V ∪ Λ = V to an address in V, so (b) is kept.
- Branches change nothing, and R has no numerical instruction.

Every LOAD lies in R by (i), so every read is at an address in V. On a property-1 base, |V| ≤ r + |Λ| + |H| + e is bounded independently of j, while k = Θ(N/w) grows. So for every sufficiently large j some sensitive word is never loaded, and the edit argument of Section 3 gives an error or a divergence on the base or on one of its sign edits. ∎

The reads are data-dependent but bounded. A LOAD-only loop can chase pointers (x ← M[x]), but every loaded word is in H, is the address just read, or is a stored value in V, so the chase stays inside V.

*Hypothesis (iii), class by class.* Hypotheses (i) and (ii) were checked mechanically in Section 2.
- **L1S0A2B3** (8 classes): there is no STORE, so memory is the input image at entry and E = ∅.
- **L1S1A1B3, one-time STORE** (`C:A C:L` with S at pre, mid, post or none, 6 classes): the STORE executes at most once, so at most one cell differs at entry and e = 1.
- **L1S1A1B3 `C:A C:LS`**: the only STORE is in R, so no STORE runs before entry and E = ∅.
- **L1S1A1B3 `C:AS C:L`**:
  - If R comes first, or the parts are parallel, no STORE runs before entry on a run that enters R.
  - If the numerical loop comes first, no data instruction precedes it, since the class key has no off-cycle data. So at its entry the registers are 0, N and w. Inside it the only register-writing instruction is its one numerical instruction, with destination d. So every register other than d keeps a value in F ⊆ {0, N, w}.
  - Its STORE is M[u] ← v with u, v ∈ {d} ∪ F ∪ Λ. If u = v = d, the cell holds its own address. If u = d and v ≠ d, the cell holds a value in F ∪ Λ. If u ∈ F ∪ Λ, the STORE always writes the same cell, which holds one last value.
  - So E ⊆ F ∪ Λ ∪ {one value}, and e ≤ 3 + |Λ| + 1.

  A linked list M[a] = a′ ≠ a cannot be written, because only one register varies in that loop. The independent check of Section 2 confirms the case distinction: in the 1,152 graphs of `C:AS C:L |seq` where the numerical loop comes first no data instruction precedes it, and data instructions precede it exactly in the 1,080 graphs where R comes first.

So all 18 classes are excluded at every speed. Unlike the one-site classes, they need neither the one-site theorem nor any extension of it, only property 1.

## 6. Finite check of the phase lemma (synthetic memory)

`six_slot_phase_lemma_simulation.py` samples the two hardest shapes, `C:AS → C:L` (the hard case of (iii)) and `C:A → C:LS`, each with the numerical loop first:
- w = 16, 400 input words of an even three-word palette, zero elsewhere;
- per run, a random opcode (add, sub, mul, xor, and, or, shl, shr, rotl, mov), operands among four registers and three random literals, a random order of the numerical instruction and the STORE in `C:AS`, and a random exit test;
- a numerical phase that stops at its exit test or after a cap of 1 to 3,000 steps, then the LOAD loop, which runs its LOAD and, in `C:LS`, its STORE.

It checks that every read address lies in V and that |E| ≤ |F| + |Λ| + 1 for `C:AS`, and it reports the largest number of distinct addresses read. The control has two numerical sites in its first loop (e ← d + 2; M[d] ← e; d ← e), which is outside the 18 classes and writes a linked list. With no argument (seed 1), and with `--control`, it prints:

```
AS-L: runs=20000 reads outside V: 0  |E| bound violated: 0  max distinct addresses read=5  max |V|=11  (input words L=400)
A-LS: runs=20000 reads outside V: 0  |E| bound violated: 0  max distinct addresses read=5  max |V|=10  (input words L=400)
control (two numerical sites, not one of the 18): distinct addresses read=301, reads outside V=299, |E|=300
```

Seed 2 prints the same two lines as seed 1. The control shows that the check can fail, and that hypothesis (iii) is what fails once a loop has two varying registers. During review the code was read: V is built from the entry registers, the literals, H, E and {0}, not from the trace of read addresses, the `C:AS` loop has exactly one numerical site, and E leaves out cells that hold their own address. This is a finite check on synthetic memory, not on the journal's DIMACS layout.

## 7. The map update

The moved classes are:
- all 18 two-loop classes, by the phase lemma;
- the 12 one-site classes with no PRE graph, by Lemma E on their E graphs and Lemma V on their 1V graphs;
- the 7 five-slot-schedule classes whose graphs are all single-verdict, by Lemma V alone. Lemma V's proof allows STOREs before R, so these are excluded at every speed by Lemma V and property 1. The other 26 of the 33 keep 13,416 two-verdict graphs and are not treated here.

`six_slot_control_class_marking.py` marks the 18 two-loop classes EXCLUDED by a shape rule: the LOAD loop has no numerical site, with one LOAD and either no STORE or a single numerical instruction, which are the shapes whose hypothesis (iii) Section 5 checks. The other 19 classes are an explicit list, since the class key does not decide them. The regenerated table differs from the previous one in exactly these 37 rows, each from REDUCES to EXCLUDED. The split's last lines give the per-mix counts before this note, after the 30 one-site and two-loop classes, and after all 37, which is the regenerated table:

```
6. class table: the 37 listed classes the split moves are EXCLUDED citing the note, and the other 36 listed classes are its REDUCES classes: True
7. per mix, classes and labeled graphs (EXCLUDED/REDUCES/OPEN): before -> after the 30 -> after the 37 (the table)
   L1S0A2B3  89/16/1 230436/63000/51840 -> 101/4/1 264204/29232/51840 -> 101/4/1 264204/29232/51840
   L1S0A3B2  53/4/1 19440/3600/2160 -> 54/3/1 19728/3312/2160 -> 54/3/1 19728/3312/2160
   L1S1A1B3  153/18/1 258372/35064/51840 -> 165/6/1 278460/14976/51840 -> 166/5/1 278604/14832/51840
   L1S1A2B2  112/8/3 20160/2880/2160 -> 112/8/3 20160/2880/2160 -> 114/6/3 20352/2688/2160
   L1S2A1B2  115/5/3 21360/1680/2160 -> 115/5/3 21360/1680/2160 -> 116/4/3 21456/1584/2160
   L2S0A2B2  62/10/2 14784/8256/2160 -> 67/5/2 17904/5136/2160 -> 67/5/2 17904/5136/2160
   L2S1A1B2  108/12/3 17712/5328/2160 -> 108/12/3 17712/5328/2160 -> 111/9/3 17952/5088/2160
   total     932/73/14 3693852/119808/114480 -> 962/43/14 3751116/62544/114480 -> 969/36/14 3751788/61872/114480
```

OPEN labeled graphs stay at 114,480. The mixes L1S0A1B4, L2S0A1B3 and L3S0A1B2 have no REDUCES class and do not change. The REDUCES breakdown 33/22/18 becomes 26/10/0, and the 14 OPEN classes are untouched. The independent check of Section 2 gives the same recounts from its own move decisions.

**What each moved class rests on.**

| class | graphs E / 1V | rests on |
|---|---|---|
| L1S0A2B3 `C:A C:AL \|par` | 0 / 288 | Lemma V only |
| L1S0A2B3 `G{LA} none:A` | 0 / 2016 | Lemma V only |
| L1S0A3B2 `C:AL none:A,pre:A` | 0 / 288 | Lemma V only |
| L1S1A1B3 `G{LA} none:S` | 0 / 1008 | Lemma V only; also R-d plus the one-site theorem as written, for all graphs |
| L2S0A2B2 `C:AL none:A,post:L` | 0 / 96 | Lemma V only |
| L2S0A2B2 `C:AL none:A,pre:L` | 0 / 192 | Lemma V only |
| L2S0A2B2 `C:AL none:L,pre:A` | 0 / 192 | Lemma V only |
| L1S1A1B3 `G{LA} post:S` | 10152 / 1008 | R-d plus the one-site theorem as written, for all graphs |
| L1S0A2B3 `G{LA} post:A` | 20304 / 2016 | E graphs: exit code after the last LOAD (rule 4's extension); 1V graphs: Lemma V |
| L1S0A2B3 `C:- C:AL \|seq mid:A` | 144 / 288 | E graphs: exit code after the last LOAD, `C:-` being acyclic on halting runs (a normalisation of the map); 1V graphs: Lemma V |
| L2S0A2B2 `C:AL post:A,pre:L` | 528 / 192 | E graphs: exit code after the last LOAD (pre:L cannot follow post:A); 1V graphs: Lemma V |
| L2S0A2B2 `C:AL post:A,post:L` | 1728 / 192 | E graphs: Lemma E with one LOAD after the exit code, the new clause; 1V graphs: Lemma V |
| the 18 two-loop classes | 16,632 graphs | phase lemma only |
| the 7 five-slot-schedule classes | 0 / 672 | Lemma V only |

Lemma V and the phase lemma rest only on property 1; the E rows rest on the one-site theorem as well. The second citation of the two STORE rows was pointed out during review: in every graph of both classes the STORE is none or post relative to R and the only LOAD is in R, so no LOAD follows the STORE. Reduction R-d of the case-split note then applies to every graph, and the one-site theorem as written excludes the result; the map already uses this citation for `C:AL post:S` and `C:AL none:S`. "Lemma V only" is kept for the all-1V classes, since it needs only property 1, which is lighter than any citation that goes through the one-site theorem.

Lemma V and Lemma E both argue on runs, not on lengths, so neither needs the length regimes of the [round-four note on length-dependent markers](length-dependent-markers-and-the-prologue-branch-classes.md) or Lemma P of the round-five note on prologue branches.

## 8. The three standard tests

No time lower bound is claimed; these are program-size statements at any speed.
- **(a) A fast, globally correct solver for the hard family?** Yes. The property-1 base and the equality files have linear-time packed-scan solvers, and the journal's 43-instruction program decides all inputs. The exclusions bound program size only.
- **(b) The same argument for 2-SAT?** Expected yes; not checked. Lemma V and the phase lemma use only property 1: single-word edits that flip the answer, and a bounded palette. Lemma E adds the one-site theorem's equality family. A 2-CNF version of these families would behave the same, but none was built. So these arguments say nothing about SAT's hardness beyond the families.
- **(c) Relativization.** With the packed oracle of the [relativized clock](relativized-clock.md), a constant number of instructions decides SAT with one query; with the [multilinear oracle](multilinear-oracle-clock.md), the Boolean query suffices. So the class exclusions are false relative to both.
  - The step that fails is the one the whole map uses: a LOAD returns one w-bit word. Lemma V and the phase lemma count *cells read*, and that count bounds the information read only for one-word loads.
  - The control-graph parts of the lemmas (the run never returns to R; one-time LOADs run at most once) relativize. The non-relativizing content is property 1's step that a word never loaded cannot affect the answer.

## 9. Exact obstruction and next step

**What blocks the 10 remaining one-site classes.** Their 23,832 PRE graphs execute, before R and on runs that enter R, one of the following, while R can still reach both verdicts.
- **A one-time numerical instruction.** Before R the registers hold 0, N, w, or a word loaded from a fixed address. That word is a palette word on the base, and possibly a private word on an equality file, which costs a protocol one word. The result is a length-dependent word z, which is public when it is computed from 0, N, w and literals only.
  - In `C:A C:AL |seq` with the numerical loop first, z is an iterate of one operation stopped by public tests.
  - In `C:AL pre:A,pre:L`, z may be an operation on a word loaded from a fixed address.
- **A one-time STORE** (`G{LA} pre:S`), which plants one public word at a public address.

Write B, as in the one-site note, for H together with the initial register values and the literals. Read against "B gains z" or "H gains the planted word", the rows of the one-site theorem fare as follows (by reading, not row by row in full):
- **site ignoring the old y:** survives, since the image of B ∪ {z} is bounded;
- **move, constant, comparison, bitwise, shift, rotation:** survive, since the bounds depend on |B| and w only;
- **y ← c − y** (also with c = z): survives, since orbits still have at most two points between resets;
- **parity row (multiplication involving y; additive forms with two mutable sources; fixed even operand): breaks as written.** The false sentence is "both operands and the result stay even by induction", once an odd z reaches y or an operand register, or once the planted payload is an odd literal.
  - For example, a prologue y ← 1 followed by the recurrent y ← 5·y visits every address ≡ 1 (mod 4).
  - This example is probably excluded anyway: a cyclic subgroup of the units mod 2^w has index at least 2, so this orbit misses the odd residues ≡ 3 (mod 4). But that is a coset argument, not parity, and with resets and any control flow it is not done here.
- **cursor row y ← y + c: breaks for c = z.** With an odd stride z held in a register, the bound of at most 2|c| + O(1) owner crossings per lap is no longer a program constant. This is the obstruction of the [length-dependent stride](length-dependent-markers-and-the-prologue-branch-classes.md#5-the-length-dependent-stride) in the round-four note, whose near-top band colouring closes the q = 1 forms of z for the writable row, by reading; the q = 2^s forms are open there too.

For `G{LA} pre:S`, a register payload at that point is 0, N or w, all even, and parity survives. The obstruction there is only an odd literal payload.

**Next lemma.** In the read-only one-site machine started from registers that include one odd length-dependent word z, no program whose site is additive or multiplicative decides DIMACS SAT. Here z is public, or is computed from one word at a fixed address, which may be private on an equality file. That is the parity row with one odd extra word, with resets and any control flow. The natural tools are a read-only zero trap and coset counting for odd multipliers. After that comes the cursor row with stride z, by the round-four note's band colouring at near-top lengths.

**Not done here.**
- Lemma E may reach the two-verdict graphs of some of the 26 remaining five-slot-schedule classes, for example `C:AL post:L,post:S` (a post STORE followed by a post LOAD) and the `C:AL post:A,…` classes. That needs the writable rows, not the one-site theorem, and was not checked.
- No table was made of the five-slot rows against arbitrary public initial registers and a bounded public change of memory. The analysis above covers only the rows of the one-site theorem, and only by reading.

**Two possible failures that do not occur.**
- No one-site row was found whose proof needs the absence of post-exit STOREs or of a second numerical site. Lemma E shows that every row of the one-site theorem tolerates any code run after the first post-exit or bypass instruction, provided that code executes boundedly many LOADs. In the moved classes that code is a dead STORE, numerical code, or one later LOAD. What the rows do not tolerate is code *before* the loop (above).
- A LOAD-only loop that reaches a private word is not an obstruction. In the phase lemma a literal address, or a public word that lands on a sensitive cell, is one element of V, so it adds one cell. A bounded number of extra reads does not affect the count of missed originals.

## 10. What is not proved

- Lemma V, Lemma E and the phase lemma are manuscript proofs with no Lean check. During review the phase lemma was re-derived, Lemma V was confirmed with the treatment of the NO verdict in its step 6, and Lemma E was read against the one-site note.
- Lemma E opens the proof of the one-site theorem. It rests on reading each of its rows as an invariant of executions of the read-only one-site machine, which applies to the prefix before t*. The rows are not re-proved line by line, and the theorem itself is a manuscript proof of the journal.
- The split is a computation on the map's enumeration. Its class keys and labeled counts equal the class table for the 779 classes of the seven mixes, and its positions relative to R agree with the table's own labels on all 75,696 graphs of the 18 one-site classes with one recurrent part. Its verdict and STORE-location predicates have no such tie to the table; they, and the positions, were reproduced during review by an independent enumerator on nine of the ten mixes. The tenth, L1S0A1B4, has no REDUCES class and was not re-enumerated.
- Property 1 is taken from the journal, including its layout audit, whose assertions hold at every j from 61 to 1199, the range where it was run; the audit was not re-run here.
- The phase-lemma check is a random simulation on synthetic memory at w = 16, not on the journal's DIMACS layout, and it samples only the order with the numerical loop first.
- The parity and cursor-row analysis of Section 9 is by reading, not checked row by row in full. The y ← 5·y example is not run.
- The 36 REDUCES classes left are unchecked: 26 five-slot-schedule classes with two-verdict graphs and 10 one-site classes with PRE graphs.
- No time bound of any kind is claimed.

## Reproducing the checks

Run from `audits/`. No script writes files unless given `--out DIR`.

```
python3 six_slot_control_class_split.py
python3 six_slot_control_class_split_independent_check.py
python3 six_slot_phase_lemma_simulation.py
python3 six_slot_phase_lemma_simulation.py 2
python3 six_slot_phase_lemma_simulation.py --control
python3 six_slot_control_class_marking.py
python3 six_slot_control_class_cross_check.py
```

The split compiles `six_slot_control_class_split.cpp` into a temporary directory and takes about 5 seconds; with `--out DIR` it also writes the three regenerated lists. The independent check compiles `six_slot_control_class_split_independent.cpp` and takes about 5 seconds. Each simulation run takes about 15 seconds, and the map's marking script and cross-check about 40 and 12 seconds; the cross-check reads the three lists to account for the 37 classes. [Split](../audits/six_slot_control_class_split.py) · [Split enumerator](../audits/six_slot_control_class_split.cpp) · [Independent check](../audits/six_slot_control_class_split_independent_check.py) · [Independent enumerator](../audits/six_slot_control_class_split_independent.cpp) · [Phase-lemma simulation](../audits/six_slot_phase_lemma_simulation.py) · [Marking](../audits/six_slot_control_class_marking.py) · [Cross-check](../audits/six_slot_control_class_cross_check.py)
