# Even-multiplier six-slot scans with an odd stride fail on the equality files at every speed

Consider the six-stored-instruction programs x = M[p]; M[x] ← a·p; p += d of the [even-multiplier note](even-multiplier-stores-in-a-six-slot-scan.md), under native initialization (registers 0, except optional n and w), with a an even literal (or a = w, or a = n when D ≥ 2) and d an odd literal. Every such program fails on the equality files at every speed. For each member there is N₀, depending on a, d and the member's literals, such that at every larger byte-aligned length N at which gcd(3K+4, |d|) = 1, where 3K+4 is the clause length in words (always so for d = ±1, ±3), and, at D = 1, outside one exceptional interval of lengths, every equal file has an unequal partner, differing in one private bit, on which the member executes the same instruction sequence. The reason is parity: odd addresses outside the file's palette are never written, and both sign words recur at such addresses after the flipped cell, so the two stamps are overwritten alike before they are read. So in these cases the even-multiplier note's clock bound, which it calls possibly vacuous, is vacuous. The conditions are sufficient, not necessary. Every even stride stays open, and the method provably fails when the scan lies inside aZ_Q, as for a = d = 2; so do the other payloads of the generic corollary. The overwrite-before-read mechanism is that of the [shifted-scan erasure note](erasing-private-signs-in-a-shifted-scan.md); what is new is that parity guarantees the covers are never written, and that they occur in the unmodified equality files. The proofs are manuscript proofs, checked by member simulations and on generated files, with independent checks during review. No class of the six-instruction map changes status, and nothing here is a time bound; the linear, quadratic and cubic questions remain open. [Communication bound for public crossed scans](communication-bound-for-public-crossed-scans.md) · [Six-instruction control classes](six-instruction-control-classes-in-the-five-slot-machine.md) · [Odd multipliers](odd-multiplier-stores-in-a-six-slot-scan.md)

## Setting and statements

**Architecture.** A(g,d) is the even-multiplier note's architecture with payload map g: registers x, y, p; the cycle LD x←M[p], MU y←g(p), ST M[x]←y, AD p←p+d mod Q, in one of the six cyclic orders; two comparison branches, either both on the cycle or one on the cycle exiting to the second; entry at any instruction; registers starting at public values (native: 0, n, w). A branch compares two operands, each a register or a literal, by =, unsigned < or signed <, and the exit side gives the negations: the ISA's "word comparisons" of the [five-instruction loops](five-instruction-loops-on-dimacs-sat.md), including the signed test of n against 0 used in the six-instruction note. A bit test is not a branch predicate in this ISA; it would separate the two sign words, and the argument would fail. M₀ is the memory at the first LD, y₀ the value of y there, H′ = image(M₀) ∪ {y₀}, and Ω = Z_Q ∖ (H′ ∪ g(Z_Q)).

**Lemma A (destinations).** After the first LD every loaded value lies in H′ ∪ g(Z_Q), and every STORE destination is a loaded value. So every cell of Ω keeps its M₀ content forever. For g(z) = a·z with a even, g(Z_Q) = 2^{v₂(a)}Z_Q ⊆ 2Z_Q for a ≠ 0, and {0} for a = 0, so every odd address outside H′ is never written after the first LD.

**Lemma B (covered swap).** Take a member Π and initial memories F₁, F₂ whose memories at the first LD differ exactly at one cell c, with M₀¹[c] = u ≠ u′ = M₀²[c]; H′ uses both images, and L is the period of d in Z_Q. Suppose
- **(H2)** u ≠ c ≠ u′, and there are 1 ≤ j₁, j₂ < L with c+j₁d ∈ Ω, M₀[c+j₁d] = u, c+j₂d ∈ Ω, M₀[c+j₂d] = u′, u ∉ {c+jd : 1 ≤ j < j₁} and u′ ∉ {c+jd : 1 ≤ j < j₂};
- **(H3)** every branch executed while x holds a value loaded from c has the same outcome with x = u as with x = u′.

Then Π executes the same instruction sequence on F₁ and F₂: the same branch outcomes, and either the same verdict at the same step or no halt in both.

**Lemma C (layout).** For the files built by the journal's `equality_file_generator.py`, whose first half encodes Alice's string and second half Bob's, as in the communication note: (i) every group of four clauses contains odd-address occurrences of both sign words uNeg and uPos among its u- and v-literal sign words; (ii) flipping the second string's bit i changes exactly the four x_i sign cells of that half's group i, each from one sign word to the other; (iii) every file address is below uPos; (iv) no odd file address is a palette value.

**Lemma D (comparands).** With native registers and a flipped x-sign cell c ≠ p₀ in the second half, the comparands at the iteration that loads c are y ∈ {g(c−d), g(c), g(c+d)}, p ∈ {c, c+d}, 0, n, w, the program's literals and the public initial values. For a fixed even literal a and N large with N ∉ [uPos, uNeg] when D = 1, none of these lies in [uPos, uNeg], the interval that contains every comparand separating the two sign words. The same holds when D ≥ 2 for a = w and for a = n. For a = w at D = 1 it holds for all but O(10⁻³·k) + 3 of the second half's groups.

**Theorem.** Let a be an even literal, or a = w, or a = n with D ≥ 2. Let d be an odd literal and Π a member of A(a,d) with native initialization. Take N byte-aligned and sufficiently large, with gcd(3K+4, |d|) = 1, and at D = 1 also N ∉ [uPos(w), uNeg(w)]. Then for every second string s there is a bit i such that Π has the same trace on F(s,s) and F(s, s⊕e_i). So Π does not decide the equality files at length N, at any speed, and does not decide SAT. Good lengths exist for every d: any N with K ≡ −1 mod rad(d), outside the exceptional interval.

The threshold depends on the member: at any fixed N, a member that compares x with a literal in [uPos, uNeg] does separate the two files (control C2 below), so no threshold works for all members at once.

## Proofs

**Lemma A.** At a LD after the first, the cell holds either its M₀ value, in image(M₀) ⊆ H′, or a value stored after the first LD. Stored values are payloads: g(p) for some p, or y₀ in iteration 0 when ST precedes MU. Every STORE goes to M[x], and x is written only by LD. ∎

**Lemma B.** p and y never depend on memory, so they are equal in the two runs as long as control agrees. By induction over steps, control agrees, the memories differ only on a set Δ ⊆ {c, u, u′}, u ∈ Δ only between a load of c and the next load of the u-cover c+j₁d (likewise for u′), and x differs only in iterations, from one LD to the next, whose LD read c.
- *Base.* After the prologue, Δ ⊆ {c}: the prologue is public, and its single possible ST has the public target x_init and a public payload.
- *A LD outside Δ* returns equal values. Inside a window the loaded addresses are c+d, …, c+j₁d (respectively c+j₂d); by (H2) none is u before the u-cover or u′ before the u′-cover, and none is c, since j₁, j₂ < L.
- *A LD of c* gives x = u or u′. The following ST writes the same payload to M[u] in one run and to M[u′] in the other, adding u and u′ to Δ. Every other ST in a window has equal destination and payload.
- *The u-cover* lies in Ω, so by Lemma A it still holds u in both runs; its ST writes the same payload to M[u] in both runs and removes u from Δ, and likewise for u′. A store to c, if any, is equal in both runs and removes c from Δ for good.
- *Branches.* Every operand other than x is equal in the two runs; x differs only in iterations whose LD read c, where (H3) applies, including the exit branch of the second layout. So the outcomes agree, and halting happens at the same step with the same verdict. ∎

In the no-exit cycle, Lemma B's induction says that the sequence of loaded values x differs only at loads of c; given (H3), that implies the trace statement for every branch configuration. So the exhaustive checks test the x-sequence over all orders, entries, payloads, strides and initial cursors, and they test branch members separately by sampling.

**Lemma C.** A literal is K+1 words whose first word is ' '^{W−2}·(sign)·'1', which with little-endian packing is uPos (sign ' ') or uNeg (sign '-'), with top byte '1' = 0x31, so uPos ≥ 49·2^{w−8}. A clause is 3K+4 words: the x-sign at offset 0, the u-sign at K+1, the v-sign at 2K+2, then the terminator. Group i is 4 clauses, 4(3K+4) words, and clause j has (u-sign, v-sign) = (' ',' '), (' ','-'), ('-',' '), ('-','-') for j = 0, 1, 2, 3. With hw header words and π = hw mod 2, every group in both halves starts at parity π, since the group length is even.
- (i) If K is odd, the clause length is odd and the three offsets are even, so clause j has its sign words at parity π+j: for π = 0 the odd clauses are 1 and 3, and clause 1 has ' ' and '-'; for π = 1 they are 0 and 2, giving ' ' and the '-' u-sign of clause 2. If K is even, the x- and v-signs are at parity π and the u-signs at π+1: for π = 0 the odd u-signs are ' ',' ','-','-', and for π = 1 the odd v-signs are ' ','-',' ','-'.
- (ii) The bit sets only the x_i sign, '-' if the bit is 0. (iii) nwords ≤ N/w + 1 ≤ 2^w/24 + 1 < 49·2^{w−8} for w ≥ 24.
- (iv) The smallest byte in the file is '\n' = 10, so every full word is at least 10·2^{w−8}, which exceeds nwords once w ≥ 32. The remaining palette values are 0 and the possibly zero-padded last word, whose low byte is ' ' or '\n', both even. Native y₀ and x_init are even (0, n, w or a·(…)). So every odd file cell outside the prologue's public targets lies in Ω. ∎

**Covers for odd d.** For d = +1, the second half's groups i ≤ k−1 are covered: group i+1 lies after all four changed cells and contains odd occurrences of both words that are never changed. For d = −1, every group is covered by group i−1, or by the first half's group k when i = 1. For general odd d with gcd(3K+4, |d|) = 1, the group length 4(3K+4) is invertible mod |d|, so an odd occurrence at address q in a later group reappears at q + t·4(3K+4), and as t runs over |d| consecutive values this meets every class mod |d| with unchanged parity; the scan c, c+d, … visits every address of the class of c inside the file, so groups i ≤ k−|d| (for d > 0) have covers within the first lap. The window stays inside the file, below uPos, so u and u′ are not loaded in it. For d = ±3, 3K+4 ≡ 1 mod 3, so the condition always holds. For d = ±5 and ±7 it fails exactly when K ≡ 2 mod 5, respectively K ≡ 1 mod 7; then every sign word of the x-class has offset 0 mod |d| within its clause, and no u- or v-sign lies in that class.

**Lemma D.** Both sign words are below 2^{w−1}, so signed and unsigned order agree on them, and a comparand z separates them under =, < or ≤, in either operand order, only if z ∈ [uPos, uNeg], an interval of length 13·2^{w−16}.
- p ∈ {c, c+d} lies below uPos by (iii).
- For y with a > 0, a(c+|d|) ≤ a(2^w/w + 1 + |d|) < 49·2^{w−8} once w > 5.23a + O(1). For a < 0, Q − |a|(c+|d|) > 50·2^{w−8} > uNeg for w large; a = 0 gives y = 0.
- A fixed literal ℓ reduces to [0, ℓ] or [Q−|ℓ|, Q), outside the interval for large w. 0 and w are small. n ∈ [uPos, uNeg] is the exceptional set; at D ≥ 2, Q ≥ (N+2)², so N < uPos.
- c ≠ p₀: under native initialization p₀ ∈ {0, n, w, d, n+d, w+d}, while c lies far inside the file and below n, so y₀ is not a comparand at c for large N.
- For a = w and D ≥ 2, y ≤ w(nwords+2) ≈ N < uPos. For a = w at D = 1, bad c exist only when N ≳ uPos ≈ 0.19·2^w, and they then fill an interval of at most 13·2^{w−16}/w + 2|d| + 1 words, because three shifts e ∈ {−d, 0, d} occur. That is at most 1.05·10⁻³·N/(w·g) + 3 groups once the group length g is at least 2|d| + 1, against k ≈ 0.031·N/(w·g/12) groups, so at least 99% of the groups are good for large N.
- For a = n and D ≥ 2, y ≤ N(N/w + 2) < Q/5 < uPos. For a = n at D = 1, y = N(c+jd) mod Q wraps around, and there is no proof.

**Theorem.** Choose a group i of the second half that is covered (Lemma C and the covers above) and has good comparands (Lemma D); for large N almost every group qualifies. Native x_init and y₀ are even, so they are not odd covers. Go from F(s,s) to F(s, s⊕e_i) through four one-cell steps, one per x_i sign cell, and apply Lemma B at each step. The covers are u- or v-sign cells, which never change; both sign words occur in every intermediate file, so H′ and Ω are the same throughout, and the prologue is the same in every step. ∎

## Checks

**Exhaustive and random lockstep checks of Lemma B.** For every swap (c, u→u′) with u′ in the palette, (H2) is evaluated on the memory at the first LD; both runs then go 3 passes in lockstep, without exits, and the check counts loaded-value differences at addresses other than c. At Q = 8 this covers all 7,120 memories with at most two values and all members (6 orders × even a ∈ {0, 2, 4, 6} × odd d ∈ {1, 3, 5, 7} × 4 entries × 8 initial cursors); at Q = 16, all 6 × 8 × 8 × 4 × 16 members on 400 random small-palette memories; at Q = 32 and 64, all orders and even a, d ∈ {1, −1, 3, −3, 5}, 4 entries and 4 cursors on 120 and 40 random memories. The controls are swaps that fail (H2):
```
small W=3: swaps satisfying (H2)=33457152, x-trace violations among them=0, c-iteration differences=86734016
small W=3: control: swaps failing (H2)=187302912, of which with an x difference away from c=86909160; trivial (prologue overwrote c)=19127808
small W=6: swaps satisfying (H2)=50858400, x-trace violations among them=0, c-iteration differences=140870370
```

**Random full members.** Each member has a random layout, gaps, entry slot, comparisons (=, <u, <s on x, y, p, a public register or a random literal), arbitrary public initial registers, even a and odd d, and (H3) is tracked along the first run:
```
branch W=3: random full members tested=1021382 (halted within cap: 890707); (H2)&(H3) hold=136509, trace differences among them=0
branch W=3: control: (H2) fails=880001 (traces differ in 37140); (H2) holds but (H3) fails=4872 (traces differ in 4426)
branch W=6: random full members tested=172122 (halted within cap: 152651); (H2)&(H3) hold=145908, trace differences among them=0
branch W=6: control: (H2) fails=25749 (traces differ in 386); (H2) holds but (H3) fails=465 (traces differ in 437)
```
The evidence is thinner than the totals suggest: an instrumented copy run during review found that of the 457,868 runs in which (H2) and (H3) hold over W = 3..6, only 90,436 load c and then execute a branch (32,694, 19,162, 14,055 and 24,525 at Q = 8, 16, 32 and 64); the others halt before reaching c, so their traces agree trivially.

**A real equality file at w = 24.** The generator's file has N = 2^20, k = 81, K = 7 and 43,691 words, with Q = 2^24; the flip is the second string's bit 40, at cells 12011, 12036, 12061 and 12086, and uNeg = 3,222,816, uPos = 3,219,488. Each run covers 3 full passes, about 5·10⁷ loads. The eight payloads are a ∈ {2, 4, 6, 8, −2, 0, n, w}:
```
real part1: lockstep runs (6 orders x 4 entries x 8 payloads x strides {1,-1,3,-3}, native registers)=768, runs with an x difference away from the swapped cells=0
real part1b: a=2, d=1, initial registers in {0,n,w}^3 (26 nonzero choices x 6 orders)=156 runs, with a difference away from the swapped cells=0
real control C1 (uncovered swap in Bob's last group, a=2, d=+1): x differences away from the swapped cells=12 (first at iteration 3219488)
real control C1' (same swap, d=-1, covers below it): x differences away from the swapped cells=0
real control C2: order LD MU ST AD, B1: p == 12011, B2: x < 3222816 (inside [uPos,uNeg]): verdicts 0/1 at steps 60057/60057 -> DIFFERENT
real control C2: order LD MU ST AD, B1: p == 12011, B2: x < 3223816 (outside [uPos,uNeg]): verdicts 1/1 at steps 60057/60057 -> same
```
The two controls show that both hypotheses do work: in C1 the first difference appears exactly at iteration uPos = 3,219,488, when the scan loads the uncovered stamp cell; in C2 a member that exits at p = c and tests x < uNeg tells the two files apart in all six orders, while the literal 3,223,816, just outside [uPos, uNeg], does not. Of the 48 random full members of part 3, only 14 load a flipped cell, as an instrumented copy run during review shows (13 of them load cell 12011), so the non-vacuous evidence there is 14 members; the part's built-in C2 control is dead, since its members exit within 12 steps, before loading c. The payloads p AND ~1, p OR 1, p<<1 and p² also show 0 differences for d = ±1 in all 6 orders, but so do the bijective payloads 3p, p and p+2 within 3 passes, so 3 passes do not separate them; only the static hypothesis (H2) gives an any-speed proof.

**Covers and comparands at the standard width.** At N = 2^17 … 2^22 for D = 1, 2, 3, and 6 random byte-aligned lengths at D = 1, every file has odd-address occurrences of both sign words; the only palette values below nwords are 0 and 2592, both even; and the comparands are good for every group, including a = n at D = 1. The exceptional interval at w = 32 is [824188960, 825040928]:
```
static: palette values that are file addresses (all even; asserted no odd one): [(0,), (0, 2592)]
static: every file has odd-address occurrences of both sign words and (H2) for d=+-1 in all but at most one Bob group: True
exceptional n-interval at w=32: [824188960, 825040928], length 851969 = 13*2^(w-16)+1, log2(uPos)=29.6184
```
The per-length cover counts of this check accept any unchanged odd cell as a cover, including other groups' x-sign cells, whose values depend on the strings; at K = 7, where gcd(25, 5) = 5, they show covers for d = ±5 that Lemma C does not supply. The independent layout check written during review uses u- and v-sign covers only, locating sign cells by scanning the words: on 159 files at D = 1, 2, 3 and w = 24 to 80, with all-zero, all-one and random strings and all four parity combinations, it confirms Lemma C(i), the even palette, and the first-lap cover prediction for every d ∈ ±{1, 3, …, 15} with gcd(3K+4, |d|) = 1, and it finds 0 covers in all 324 rows where the gcd exceeds 1:
```
Lemma C(i) failures=0; first-lap u/v-cover prediction failures (gcd=1)=0
gcd(3K+4,|d|)>1 rows (u/v-only covered groups; note predicts 0): 324 max covered= 0
```

**Independent covered-swap check.** Written during review from Lemma B's statement, it runs full members with two branches, both layouts and every entry slot, arbitrary public initial registers, even multipliers, even affine maps and random small-image payloads, and odd and even strides, taking M₀ and y₀ at the real first LD. Across Q = 8 to 64 it finds 0 trace differences in 226,807 runs where (H2) and (H3) hold, 68,280 of them non-vacuous, while (H2) without (H3) differs in about 96% of runs:
```
refB W=6 seed=7: tested=190640 trivial=98141 | (H2)=97048, (H2)&(H3)=96637 [even-mult 30996, even-affine 30838, random small-image 34803; even d among (H2) 26899; c=p_init 1510], trace differences among (H2)&(H3)=0
refB W=6: (H2)&(H3) runs that executed a branch after loading c (non-vacuous)=28504
```

## The three standard tests

- **(a) Fast globally correct solver on the hard family?** Yes: a packed comparison of the two halves decides the equality files in O(N/w) steps on the unrestricted RAM. The statement concerns one fixed six-instruction architecture.
- **(b) The same argument for a trivially easy language?** Yes. No member computes string equality on these layouts at all, and equality is in linear time; the argument uses only that the two kinds of file differ in sign words that recur at never-written addresses, so any 2-CNF equality layout with the same word structure is fooled the same way (not built). The result measures the architecture, not SAT.
- **(c) The relativized clock?** The proof uses that one LD returns one word and that one ST changes one cell, at an address that was just loaded. An oracle query on a packed string is not an instruction of A(a,d), so the statement says nothing about machines with such queries and does not relativize. [Relativized clock](relativized-clock.md)

## Exact obstruction and next step

- **Even strides.** Let C = p₀ + 2^{v₂(d)}Z_Q be the scan's coset. If C ⊆ aZ_Q, every cell the scan reads can be written and Ω ∩ C = ∅; this happens when v₂(d) ≥ v₂(a) and p₀ ≡ 0 mod 2^{v₂(a)}. Under native initialization p₀ ∈ {0, n, w} + {0, d} is even, so a = d = 2 is in this case. Covers can then erode, and the even-multiplier note's dichotomy allows up to P·|U| writes outside U in P passes, so no static protection survives unboundedly many passes. The cases v₂(d) < v₂(a), and C disjoint from aZ_Q, look within reach of the same method but are not analyzed.
- **a = n at D = 1.** y = N(c+jd) mod Q wraps, and the progression over the groups can be constant mod Q, for example when v₂(N) + v₂(g) ≥ w; then (H3) for one group decides it for all. There is no proof that some group always avoids [uPos, uNeg]; it held at the 12 tested D = 1 lengths.
- **Exceptional lengths at D = 1, N ∈ [uPos, uNeg].** A branch "x < n" reads each sign directly, and only the even-multiplier note's conditional clock bound applies.
- **Odd d with gcd(3K+4, |d|) > 1.** Covers in the first lap fail. Following the scan through later laps, or choosing the string so that other groups' x-signs serve as covers, might close this.
- **Bijective payloads** (odd multipliers, translations, XOR, rotations). Ω contains no cover, and Lemma B gives nothing; the odd-multiplier note gives only clock bounds, for odd multipliers and, by a remark, for translations. A proof must show that covers survive erosion over many passes.
- **Next lemma.** For even d with C ⊆ aZ_Q: an erosion bound showing that some u- and v-sign cells in the same coset after c are never written, for example because the stamps written into file cells are confined to an orbit set U that misses whole groups.

## What is not proved

- Everything is manuscript; there is no Lean. Lemma B is checked only by computation, over 3 passes per run, with arbitrary initial x and y only in the sampled branch members.
- a = w at D = 1 (the 99% count) is manuscript only; no tested length reaches the regime N ≳ 0.19·2^w where it matters.
- The real-file checks use one file at w = 24, not the standard width, over 3 passes; the standard-width checks are static (covers and comparands), at N ≤ 2^22.
- a = n at D = 1 is checked at the tested lengths only. Left shifts, and AND or OR with a literal that clears or sets bit 0, follow from the same proof (the image misses a parity class, both sign words occur at both parities in every group, and the comparands stay small); for OR with an odd literal the never-written class is the even addresses, and the even palette values below nwords (0 and a zero-padded last word such as 2592) must be excluded as covers, which the second half's groups never contain. Squaring is not proved. These remarks are manuscript and outside the Theorem.
- Even strides, exceptional lengths, odd d with gcd(3K+4, |d|) > 1 and arbitrary public initial registers are open; a public register holding a value in [uPos, uNeg] defeats (H3).
- No class of the six-instruction map changes status: the result covers an operand subfamily of `C:ALAS`, `C:AASL` and `C:AALS`.
- Overlap: the even-multiplier note's §8 proposed a periodicity argument instead; the [arbitrary-stride erasure note](arbitrary-stride-private-sign-erasure.md) erases private signs in a scan with an arbitrary fixed odd stride, a different architecture in which the payload is the advanced cursor; and the overwrite-before-read mechanism is already in the shifted-scan erasure note ("Before any such destination is read, the scan at 7 and at 9 has already overwritten the respective possible scratch writes made by the private reads"), with planted anchor words and payload equal to the cursor.

## Reproducing the checks

Run from `audits/`; nothing is written outside a temporary directory.
```
python3 -B even_multiplier_covered_swap_checks.py
python3 -B even_multiplier_covered_swap_checks.py all
python3 -B even_multiplier_equality_file_covers.py
python3 -B even_multiplier_covered_swap_independent_check.py
python3 -B even_multiplier_equality_file_covers_independent_check.py
```
The first script compiles `even_multiplier_covered_swap_checks.cpp` into a temporary directory, writes the w = 24 file there with the second script, and runs the branch members and real-file parts 2–4 in about 30 seconds; with `all` it adds the exhaustive and random lockstep checks and real-file part 1, in about 9 minutes. The second, run alone, gives the standard-width static check in about a second. The review's two checks take about 5 seconds and a minute. [Covered-swap checks](../audits/even_multiplier_covered_swap_checks.py) · [File covers](../audits/even_multiplier_equality_file_covers.py) · [Independent covered-swap check](../audits/even_multiplier_covered_swap_independent_check.py) · [Independent layout check](../audits/even_multiplier_equality_file_covers_independent_check.py) · [Checks (C++)](../audits/even_multiplier_covered_swap_checks.cpp) · [Independent checks (C++)](../audits/even_multiplier_covered_swap_independent_checks.cpp)
