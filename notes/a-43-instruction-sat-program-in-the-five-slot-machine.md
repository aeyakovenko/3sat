# A 43-instruction program decides proper 3-CNF in the five-slot machine, so the minimum correct program size lies in [6, 43]

An explicit program with **43 stored instructions** decides every comment-free proper DIMACS 3-CNF with canonical decimal identifiers (no leading zeros) in the journal's separate-operation RAM, the machine of the five-slot theorem. So on that class the minimum size of a correct program lies in **[6, 43]**. The lower bound 6 is the journal's manuscript five-slot theorem, whose witness files lie in this class. The upper bound 43 is a manuscript argument plus finite tests: 270 random formulas at two widths each against CaDiCaL, and an independent suite written during review, 10,620 random files plus 40 edge files with a separate interpreter that parses the file bytes. The program runs in exponential time on unsatisfiable inputs and says nothing about time lower bounds. Extending the exhaustion of small programs from 6 instructions upward is the open program-size step, and the linear, quadratic and cubic questions remain open. [Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md)

- **The lower bound.** The five-slot theorem's witness files lie in this class: their names begin with `1` and every clause has three distinct variables. [Public crossed scans](communication-bound-for-public-crossed-scans.md) · [Private probe contexts](private-probe-contexts-in-read-only-sat.md) · [Private sign erasure](arbitrary-stride-private-sign-erasure.md)
- **Leading zeros are outside the claim.** The journal treats them only as a format option ("including spellings with leading zeros when the format permits them"). On such files the program can fail: it answers YES on an UNSAT file that writes variable 1 both as `01` and as `1`. [One nonzero work read](one-pass-sat-with-one-nonzero-work-read.md)
- **Running time.** It is at most 2^R·O(B²)+O(B) in general, exponential on UNSAT inputs, and quadratic on inputs that need a single attempt (Section 4).
- **The open question.** Whether every correct program with at most 43 instructions is superlinear is open; that is the missing step (Section 6).

## 1. The machine, pinned down (sources cited; hardest reading where they leave a choice)

Quoted from the five-instruction note (its first two paragraphs):
- "The program may use all $2^w$ writable words and execute arbitrarily many steps. The standard width here is $w=16\lceil\log_2(n+2)/16\rceil$, for encoded input length $n$ in bits."
- "Registers are zero initially, apart from optional public $n,w$. A LOAD and a STORE each move one word, with immediate or register address. A numerical site has one fixed destination and at most two operands, and implements modular addition, subtraction, multiplication, bitwise Boolean operations, shifts, rotations, moves or comparisons. Branches compare words and have fixed targets. There is a fixed initial instruction, and YES and NO are terminal vertices. Literals are fixed integers interpreted at the current width. The ISA has no autoincrement, fused load/arithmetic, indirect jump or data-dependent return instruction. Input starts at address zero in little-endian words, with zero outside the file. The input grammar allows whitespace between tokens and unused identifiers below the header's variable bound. Some constructions use decimal identifiers with $O(\log^2 n)$ digits."

Also used:
- The five-instruction loop note: "zero padding in the last word and zero elsewhere"; "A binary branch tests a comparison and writes no data"; "ordinary comment-free ASCII DIMACS 3-CNF, allowing whitespace between tokens". [Five-instruction loops](five-instruction-loops-on-dimacs-sat.md)
- **Successor and terminal convention.** Each data instruction carries one fixed successor for free, and each branch has two fixed targets. YES and NO are terminal vertices and are not counted. This is the unit of the five-slot theorem: its control graph has s+2 vertices and at most s+b edges (step 1 of the five-instruction note). The two-sign-plane program-size note says it directly: "Data instructions may jump to any fixed successor for free." The program uses three explicit successors (`shr … -> U1`, `sub q 1 -> K1`, `add s u -> L1`). Under fall-through with counted jumps it would need up to 46 instructions (count made during review). [Static program size](static-program-size-on-two-sign-planes.md)
- The twenty-operation catalog lists And, Or, Xor, Add, Sub, Mul, saturating and mod-w shifts, rotations, and Eq/Lt/Slt/Ne/Ge/Sge. The branch tests in its `tests()` function are equality and both signed and unsigned orders. [native_four_bit_planes.hpp](../audits/native_four_bit_planes.hpp)
- "Proper": the five-slot note says "each clause excludes one eighth of assignments". This means three distinct variables per clause. The program needs only that each clause has **exactly three** literals.

Hardest choices, all honoured by the program:
1. There is no public n or w, and every register starts at zero.
2. A STORE payload is a register, never a literal. (The interpreter rejects literal payloads.)
3. The only shift is a right shift by the literal 8. Since w ≥ 16, the saturating and mod-w conventions agree. The program uses no rotations and no signed operations.
4. Branches use only `eq`, `ne` and unsigned `<`. The numerical sites used are `and`, `or`, `xor`, `add`, `sub`, `mul` (by 4), `shr` (by 8), `eq` (0/1 result) and `mov`. Any `mov` can be replaced by `add r 0`.
5. Whitespace may be any of the six ASCII whitespace bytes 9–13 and 32. Every byte below 48 other than `-` acts as a separator. Leading and trailing whitespace are allowed, and the file need not end in a newline.
6. Identifiers are canonical decimals of **any length**, possibly far longer than w bits. The header bound is also of any length. Identifiers are compared exactly as digit strings, never as words.

Stated input assumptions: the file has no comments; identifiers have no leading zeros and no `+`; each clause has exactly three literals. Leading zeros would be a separate convention. The program would mistake `07` for a terminator.

## 2. The program (43 stored instructions)

The listing is `five_slot_sat_program_43.asm` in `audits/`, run by [five_slot_ram_interpreter.py](../audits/five_slot_ram_interpreter.py), an interpreter and assembler written from the definition above.

Layout. Byte k of the file goes to address −1−k, so the top of memory holds the bytes. After unpacking, e = E = −B is the address of the last byte. The flag of position j lives at j+e. These flag addresses run from 2E to E−1 and are disjoint from the bytes and from the input words, because 2^w ≥ 8B+2.

Phases:
1. **Unpack (8 instructions).** Load each word, then repeatedly `and 255`, store, and `shr 8`. A zero word ends the phase. File bytes are nonzero, so a word is exhausted exactly when it becomes 0.
2. **Attempt (scan).** Reset the scan pointer (1). The skip loop (5) sets `n = (previous byte == '-')`, steps, loads, skips bytes below 48, and answers YES at the first zero cell (end of file). At a token start, a byte equal to `0` marks a terminator (1). The terminator test (2) fails the attempt if `s & 21 == 0`. Any other token is treated as a literal, and the header tokens `p`, `cnf`, V and C are literals too. For a literal, the program finds its **representative**: the first position j in the file such that the bytes from j up to the next byte below 48 spell the token. This is a naive search, 3+3 setup and 6+1 compare. The flag cell at j+e is read and marked by `or 2` and a store. The literal's truth `u = flag XOR n` is shifted into a window with `s = 4s + u` (5 instructions).
3. **Counter (8).** An odometer over the flag cells from 2E up to E−1. It skips unmarked cells (value 0) and toggles marked cells 2↔3. A carry out of the top answers NO.

Why it is correct (manuscript proof, checked by the tests below):
- *Representatives.* The compare loop continues while the literal byte b ≥ 48 and the candidate byte h = b. It reports a match iff h < 48 when b < 48. So a match means the bytes from j up to the next byte below 48 spell exactly the token. The search starts at the file's first byte and stops at the first match, which is at the latest the token itself. Equal identifiers therefore get the same representative, and different identifiers get different ones. A representative may lie inside a longer token: the run of `2` occurs inside `12`. That is harmless, because only representatives' flags are ever read.
- *Window.* Terminators do not shift. Each clause has exactly three literals. So at every terminator, bits 0, 2 and 4 of s are the truths of that clause's three literals. The four header tokens are pushed above bit 5 before the first terminator. If V or C is the token `0`, the formula must be empty. When C is `0`, the first check sees V, `cnf` and `p` from the current attempt. When V is `0`, only `p` and `cnf` precede the first terminator. The register s is never reset, so bit 4 of that check is left over from the previous attempt. The verdict is still YES, because the counter makes `p` or `cnf` true before it overflows.
- *Enumeration with lazy marks.* A flag cell is 0 until the first time its representative is reached, and then 2 (false) or 3 (true). Read an unmarked cell as false. Let σ be the current state and S the marked set. Invariant: every assignment τ with int(τ) < int(σ) falsifies some clause whose literals all have marked representatives. Here int is the binary integer over flag addresses, with low addresses least significant. Each attempt either passes every clause, giving a genuine model, or fails at the first falsified clause C. All of C's representatives are marked by then. The S-increment skips only states that differ from σ in unmarked cells below the carry position. Each skipped state agrees on S either with σ, so C refutes it, or with a state below σ, so it is covered by the invariant. Marks only grow. Overflow therefore means every assignment is refuted, and NO is correct. A new mark may land anywhere in the digit order, for example inside an earlier token; the argument does not use the order of discovery.
- *End of file.* The cell after the last byte is the flag cell of the file's first byte. The skip loop at EOF may pass over nonzero flag cells (values 2 and 3, both below 48). It stops at the flag of the first whitespace byte, which is never marked, and answers YES.

A 44-instruction predecessor added the address at the FOUND step; keeping the candidate pointer as the flag address (`j = mov e`, `p = sub j e`) removes that addition and gives 43. The predecessor also passed 60 formulas in each of the four test modes below; it is not kept.

## 3. Verification (commands and key output)

Each command is `python3 five_slot_sat_program_cadical_test.py five_slot_sat_program_43.asm SEED COUNT MODE`, run from `audits/`; each run takes one to two minutes, and the printed times vary. [five_slot_sat_program_cadical_test.py](../audits/five_slot_sat_program_cadical_test.py)

```
ok prog=five_slot_sat_program_43.asm mode=small seed=11 tests=150 SAT=88 UNSAT=62 widths=[16] max_steps=61733011 time=124s stored_instructions=43
ok prog=five_slot_sat_program_43.asm mode=w32 seed=12 tests=120 SAT=78 UNSAT=42 widths=[32] max_steps=64940147 time=123s stored_instructions=43
ok prog=five_slot_sat_program_43.asm mode=forced48 seed=11 tests=150 SAT=88 UNSAT=62 widths=[48] max_steps=61724101 time=125s stored_instructions=43
ok prog=five_slot_sat_program_43.asm mode=forced64 seed=12 tests=120 SAT=78 UNSAT=42 widths=[64] max_steps=51756504 time=48s stored_instructions=43
```

The mode changes only padding and width, and modes that share a seed run the same formulas. Small and forced48 use seed 11 and run byte-identical files. Forced64 runs the unpadded files of the w32 formulas (seed 12). The four lines are therefore **270 formulas, each run at two widths (540 runs)**. Without arguments the script runs a 20-file smoke test of the program (seed 11, mode small).

How the suite is generated:
- Formulas have 3–6 variables. They are either random proper 3-CNF with 1–54 clauses, or (30%) the 8 sign patterns on three variables, with one pattern dropped half the time.
- Name styles:
  - dense (1..v);
  - sparse (up to 10^6);
  - long (16–46 digits, more than w bits at every tested width);
  - suffix/prefix families such as `12`, `2`, `312`, `1212`, which stress representatives inside longer tokens;
  - mixed.
- The header bound is either the largest name or up to 31 extra digits larger.
- Whitespace runs between tokens are drawn from all six whitespace bytes. Leading whitespace is optional. The file ends with a newline, with other whitespace, or with nothing.
- Mode `w32` pads with trailing spaces to 8,200 bytes, so the width rule gives w=32. Rule widths 48 and 64 would need files of at least 2^29 bytes. Those widths were therefore forced in the interpreter to check that the program does not depend on the width.

The truth for each file is CaDiCaL's exit code (10/20) on a renumbered clean copy. That copy is built from the abstract formula, not parsed from the file bytes, so a rendering bug in the test script would go unseen here. The independent suite written during review closes this gap: it parses the bytes. It found no mismatch in 10,620 random files (8,264 SAT, 2,356 UNSAT) checked against CaDiCaL and brute force:
- 6,000 at the rule width;
- 120 at natural w=32, padded at the front, middle or end;
- 1,500 each at forced w=32, 48 and 64.

Of its 40 edge files, 39 pass; the exception is the excluded `01`/`1` probe. Its interpreter, also written independently, reproduces every step count in Section 4 and enforces the ISA restrictions of Section 1 at parse time: register-only STORE payloads, at most two operands, and fixed successors. That suite is not part of the journal.

## 4. Running time of the program

Measured with `python3 five_slot_sat_program_timing.py five_slot_sat_program_43.asm` (w=16 for all of these files; about 15 s): [five_slot_sat_program_timing.py](../audits/five_slot_sat_program_timing.py)

| U_v: v | bytes | steps | verdict |
|---:|---:|---:|---|
| 3 | 120 | 188,573 | NO |
| 4 | 131 | 425,826 | NO |
| 5 | 142 | 935,522 | NO |
| 6 | 153 | 2,191,943 | NO |
| 7 | 164 | 4,918,623 | NO |
| 8 | 175 | 11,161,004 | NO |
| 9 | 186 | 25,353,788 | NO |

| S_m: m | bytes | steps | verdict |
|---:|---:|---:|---|
| 4 | 58 | 3,350 | YES |
| 8 | 114 | 11,234 | YES |
| 16 | 227 | 41,581 | YES |
| 32 | 451 | 159,931 | YES |
| 64 | 993 | 692,168 | YES |

U_v consists of the v clauses (−a −(a+1) −(a+2)) taken cyclically, followed by the 8 sign patterns on variables 1, 2 and 3. It is UNSAT. S_m consists of m clauses (−(3k+1) −(3k+2) −(3k+3)) on distinct names. It is SAT and is satisfied by the initial all-false state. Each added variable multiplies the steps on U_v by 2.20–2.34. Each doubling of m (bytes ×1.97–2.20) multiplies the steps on S_m by 3.35–4.33.

Bounds (manuscript arguments; B = bytes, N = 8B):
- Unpacking takes exactly 5B + 5⌈B/W⌉ + 5 steps. Each byte costs 5 steps (`and`, branch, `sub`, store, `shr`). Each word load costs 5 (`and`, branch, load, `add`, branch), and there are ⌈B/W⌉+1 loads, counting the final zero word. For example, S_4 has B=58 and W=2, giving 440.
- One attempt takes O(B²) steps. A literal at file offset t with a run of length L tries at most t+1 candidates, each costing O(L+2) steps. The sum of L+2 over the tokens is at most 2B.
- One counter increment takes O(B) steps.
- A failed attempt strictly increases int(σ), and σ has ones only on marked cells. So there are at most 2^R attempts, where R is the number of distinct token strings among the literals and the four header tokens. Distinct decimal strings packed into B bytes give R = O(B/log B).
- In total, **T ≤ O(B) + 2^R·O(B²) = 2^{O(N/log N)}**.
- **On U_v, T ≥ 2^R ≥ 2^v.** The first attempt satisfies the v negative clauses, marks every variable, and fails at the pattern (1 2 3). After that no new marks appear, so the odometer visits all 2^R states before overflowing. With v = Θ(N/log N), this gives worst-case time 2^{Θ(N/log N)}. (The independent interpreter counted exactly 2^{v+3} = 2^R attempts for v = 3..12.)
- **Even one attempt is superlinear.** On S_m every literal is a first occurrence, so its search walks over all earlier positions. That gives T = Θ(B²/log B), consistent with the measured 3.35–4.33 per doubling. The O(B²) bound per attempt is tight: a one-attempt family whose new variable first appears mid-file gives ratios 3.75–3.97 per doubling (measured during review).

## 5. The three standard tests

No lower bound on SAT is claimed. The running-time statements concern this one program.
- (a) Does the hard family have a fast globally correct solver? Yes. U_v is decided in linear time by a recognizer plus a fallback, and CaDiCaL solves it instantly. The exponential time is a property of this program only.
- (b) Does the same argument give the same bound for 2-SAT? Yes. The program's quadratic search cost appears on trivially satisfiable inputs, and it would appear in a 2-SAT variant too. It says nothing about SAT.
- (c) Relativization: not applicable. Nothing is claimed about all programs.

## 6. Exact obstruction and next step

The size-limited superlinear statement would be: every correct program with at most S = 43 stored instructions takes ω(N) steps on some inputs. The journal's exhaustion method (control-graph census plus operand case split) reaches only S = 5, and S = 6 is listed as open in the five-instruction note. Going from 5 to 43 would multiply the number of control graphs and operand patterns by many orders of magnitude. No mechanism for the C → C+1 step is known; program-size induction is one of the recorded obstacles. There is also a structural ceiling. If some fixed linear-time solver existed with S* stored instructions, the statement would fail for every S ≥ S*. So a proof for S = 43 needs a reason why 43 instructions cannot implement linear-time SAT. That is a finite question, but nothing in hand bears on it. [Five instructions](five-instructions-cannot-decide-dimacs-sat.md) · [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)

Concrete next steps:
1. Shrink the upper bound. The candidate places are the 8-instruction counter (marks plus skipping are needed only for testability on UNSAT files; a counter over all flags would be correct but untestable) and the 3-instruction terminator test.
2. Settle S = 6 by exhaustion, the first open size.

## 7. What is not proved

- Correctness of the program is a manuscript argument plus finite tests. It has no Lean proof.
- The minimum size is not determined. Only 6 ≤ S_min ≤ 43 is known, and only for comment-free proper 3-CNF with canonical identifiers. Files that spell one name with leading zeros are outside the claim, and the program can err on them.
- The five-slot lower bound itself is a manuscript theorem and was not re-checked here.
- Nothing is proved about the running time of other small programs. The program's exponential worst case is measured on U_v and argued above.

## Reproducing the checks

Run from `audits/`. Place `five_slot_sat_program_43.asm` there; the test script needs CaDiCaL (via `$CADICAL`, PATH or a Lean toolchain under `~/.elan/toolchains`).

```
python3 five_slot_sat_program_cadical_test.py five_slot_sat_program_43.asm 11 150 small
python3 five_slot_sat_program_cadical_test.py five_slot_sat_program_43.asm 12 120 w32
python3 five_slot_sat_program_cadical_test.py five_slot_sat_program_43.asm 11 150 forced48
python3 five_slot_sat_program_cadical_test.py five_slot_sat_program_43.asm 12 120 forced64
python3 five_slot_sat_program_timing.py five_slot_sat_program_43.asm
```
