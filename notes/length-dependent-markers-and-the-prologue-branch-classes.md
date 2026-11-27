# A length-dependent odd marker is beaten at near-top lengths, and four of the seven prologue-branch classes are excluded

This note treats two gaps that the six-instruction map leaves in the five-slot machine. (a) The journal's odd-marker proof fails for a public length-dependent marker z, computed by one prologue numerical instruction, at the sentence "It takes O_P(w) bits to record all these interval endpoints". It is repaired, at the standard width (D = 1), at the lengths n = 2^w − m with m = O(w), with w = 16j and j a power of two when a shift or rotation count is a negative literal. At those lengths every odd z that one prologue instruction computes satisfies q·z ≡ δ (mod 2^w) with q ∈ {1, 2^s} and |δ| small, so a band colouring keeps the crossing count small and the splice goes through. By reading the three cited proofs, the same lengths close the length-dependent stride row for the q = 1 forms, while the q = 2^s forms (right shifts and rotations) stay open. (b) In the seven prologue-branch classes the prologue's tests reduce to [n ≥ Q/2], [n ≥ Q−c] and [n = Q−c]. The one-site theorem then excludes the four `C:AL` classes: only `post:A` needs the map's exit-code extension, `post:S` and `none:S` follow from reduction R-d plus the one-site theorem, and `none:A` follows directly. `C:AAL`, `C:ALS` and `C:ASL` stay reduced, so the map's totals become 929/76/14. Everything is at manuscript level and was checked during review. Nothing here is a time bound; the linear, quadratic and cubic questions remain open. [Six-instruction control classes](six-instruction-control-classes-in-the-five-slot-machine.md) · [Odd markers](odd-self-marked-cursors-without-a-clock.md) · [One arithmetic site](read-only-ram-with-one-arithmetic-site.md)

## Setting

**Model.** The five-slot machine of the five-slot note:
- registers are zero initially, apart from optional public n (the bit length) and w;
- w = 16⌈log₂(n+2)/16⌉ and Q = 2^w. This is the standard width, D = 1. The odd-marker and one-site notes allow any D ≥ 1, but part (a) needs D = 1: for D ≥ 2, n ≤ Q^{1/D}, so no near-top length exists;
- literals are fixed integers reduced modulo Q;
- the input occupies words [0, L), L = n/w, and memory is zero elsewhere.

[Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md)

**The class of part (a).** The map's writable five-slot cycle with one prologue numerical instruction: L1S1A2B2 with cycle `C:ALS` or `C:ASL` and `pre:A`. Its prologue instruction writes z = op(α, β) into a register that the cycle does not write, where α, β ∈ {0, n, w} ∪ literals and op is any numerical opcode of the instruction set. The cycle is LOAD x←M[p], STORE M[p]←z, NUM p←p+x, p−x or x−p, with any exit branches.

**Lemma (a).** Let c_P exceed the absolute value of every literal of P, and let s_P be the largest absolute value of a shift literal of P (or 0). Then:
- for all sufficiently large j, with j a power of two when the prologue instruction's count operand is a negative literal,
- and every n = 2^{16j} − m with 16j | n and c_P < m < c_P + 2^{s_P+1}·16j,
- if z(n) is odd, then for every public initial p₀, x₀ and every entry instruction of the cycle,
- P gives a wrong verdict or never halts on some proper ASCII parity-pin 3-CNF of length n.

This holds at every speed. Part (a) changes no class count: the class keeps the unary-scan row y←y+z and the unary reverse-link row.

**Lemma (b).** Take any of the 7 prologue-branch classes, any program P in it and any entry regime S_e, the set of lengths at which the prologue branch selects entry e. The question is whether the five-slot row that excludes the five-slot program P_e (the cycle entered at e) has a failing input whose length lies in S_e. Section 4 answers it for the four `C:AL` classes.

## 1. Where the odd-marker proof fails for a length-dependent marker

In the odd-marker note every use of the fixed marker c was read. Each use either holds unchanged for c = z at a fixed length, or is the crossing count:
- "The undirected graph of the translation is a cycle because c is odd." This needs only z odd.
- "At most 2|c| of its edges cross the color boundary, since J is an interval on the physical residue circle and the translation has displacement at most |c|." This is the first line whose bound depends on c. For c = z it stays true, but with J = {p : ‖p‖ ≤ L} (2L+1 residues) the exact number of crossing edges of p ↦ p+z is 2·min(‖z‖, 2L+1): when ‖z‖ > 2L, every point of J leaves J in one step. For x−p, R_z maps J onto z+J, which is disjoint from J when ‖z‖ > 2L.
  - So "O(1+|c|) monochromatic path segments" becomes Θ(L) segments, and the first false sentence is "It takes O_P(w) bits to record all these interval endpoints": the endpoints now take Θ(L·w) = Θ(N) bits. The splice can afford only γk/2 bits, with k = Θ(N/log² N).
  - Example: z = n+1 at any length with n ≤ Q/2 has ‖z‖ = n+1 > 2L+1.
- "each regularly visited word contains the same fixed c". This holds at each length, which is all the splice uses, since both spliced runs have the same length.
- The start. The proof's "at most one additional interval across all segments for the initial part of the run" holds for any public p₀, odd or even, and for any entry instruction: the first partial turn is public. No line uses an even start.

## 2. The repair at near-top lengths

**Lengths.** Fix j, w = 16j and Q = 2^w. Let m be the least integer above c_P with m ≡ Q (mod w), adjusted within m + w·t for t < 2^{s_P} where noted below, and set n = Q − m. Then:
- Q/2 < n+2 < Q, so the width rule gives w(n) = 16j;
- w divides n, and n is byte-aligned;
- parity-pin files exist at length n, since the odd-marker note uses them "at every sufficiently large byte-aligned length" divisible by w;
- L = n/w < Q/w.

**Arithmetic lemma** (manuscript proof by cases; checked). For every instruction op(α, β) with α, β ∈ {0, n, w} ∪ literals whose value z at n is odd, there is q ∈ {1, 2^s} with q·z ≡ δ (mod Q) and |δ| ≤ 2^{s+1}·max(m, w, c_P). Here s is the absolute value of the instruction's shift or rotation literal, and s = 0 for other instructions. This holds at every j, except that j must be a power of two when the count operand is a negative literal.

The cases:
- **Sums and differences.** n ≡ −m (mod Q), so combinations of 0, −m, w and literals have norm O(m + w + c_P). Here q = 1.
- **Products.** n and w are even, so an odd product is a product of two odd literals. Here q = 1 and |δ| = O_P(1).
- **Bitwise operations, all 16.** Above bit b = bitlength(max(m, w, c_P)) + 1, every bit of n is 1. Every bit of w and of a nonnegative literal is 0 there, and every bit of a negative literal is 1. So the result's high bits are all equal, and the value lies below 2^b or above Q − 2^b. Here q = 1.
- **Left shifts and rotations by a literal s.** These give −m·2^s, or rotl(n, s) = Q − (m−1)2^s − 1, or small values. Here q = 1.
- **Right shifts and rotations by a literal s.** These give t·Q/2^s + e with |e| ≤ max(m, w, c_P). Here q = 2^s and δ = 2^s·e.
- **Shift or rotation amounts n or w.** Both are ≡ 0 (mod w). Rotations act as the identity; shifts give 0 or the identity, depending on the instruction set.
- **Counts given by a negative literal −c** (found during review). Take j a power of two. Then w divides Q, so the count acts as w − c, and the instruction equals the opposite rotation by c.
  - Under count-mod-w shifts, n >> (w−c) = 2^c − 1, n << (w−c) is even, and an arithmetic shift of n gives Q − 1.
  - Under saturating shifts the value is 0 or Q − 1.
  - So q ∈ {1, 2^c} and |δ| ≤ 2^{c+1}·max(m, w, c_P).
  - At these lengths m ≡ 0 (mod w), and rotl(n, −c) = rotr(n, c) is even. So it joins the even-payload case together with right shifts by s ≤ 3.
  - Without the restriction the lemma is false. At j = 17 (w = 272, Q mod w = 256), rotr(n, −12) = rotl(n, 28) has ‖z‖ ≈ 2^36, and rotl(n, −12) = rotr(n, 28) needs q = 2^28.
- **Comparisons and moves** give 0, 1, α or β.

The instruction set does not fix shift and rotation count semantics. The case split holds under count-mod-w rotations with either shift rule; under a signed reading of counts the negative-literal case does not arise.

**Parity at these lengths.**
- For q = 1 forms, z is odd at every even n exactly when the literal makes it odd. Examples: n+c, c−n, n⊕c, n|c with c odd; rotl(n, s), whose low bit is the top bit of n, equal to 1.
- For right shifts and rotations of n by s, the low bit of z is bit s of n.
  - Take j odd, so v₂(w) = 4. For s ≥ 4, some t < 2^{s−3} makes bit s of Q − m − w·t equal to 1. Each program has one prologue instruction, so this never meets the power-of-two condition above.
  - For s ≤ 3, z is even at every length divisible by 16, including the lengths of the property-1 base, where the map's even-payload remark applies (manuscript, not re-checked). The same holds for rotl(n, −c) at power-of-two j.

**Band colouring.** Put J₀ = [−L, L] and J = ∪_{0 ≤ i < q} (iz + J₀). For q = 1 this is the odd-marker note's own J.

**Claim 1 (crossings).**
- For p ↦ p ± z, at most 2|δ| cycle edges join J and its complement.
  - Proof. Write B_i = iz + J₀. For i ≤ q−2, B_i + z = B_{i+1} ⊆ J. So an edge leaving J starts in B_{q−1} and ends in (B_{q−1} + z) ∖ J ⊆ (δ + J₀) ∖ J₀, which has at most |δ| points.
  - An edge entering J ends in B₀, since B_i − z = B_{i−1} for i ≥ 1. It starts in (J₀ − z) ∖ J = (B_{q−1} − δ) ∖ J, which also has at most |δ| points. ∎
- For x−p, the path of the involutions R₀(p) = −p and R_z(p) = z − p has at most (2q−3)|δ| crossing edges for q ≥ 2, and at most |δ| for q = 1.
  - Proof. Since J₀ is symmetric, R₀B_i = B_{−i} = B_{q−i} − δ and R_zB_i = B_{1−i} = B_{q+1−i} − δ. Each B_i other than B₀ (for R₀), and other than B₀ and B₁ (for R_z), loses at most |δ| points. ∎

**Claim 2 (special jumps).** A fresh read of an original word v at a ∈ I starts in J, because I ⊆ J₀. It lands outside J provided ‖v ∓ iz‖ > 2L for all 0 ≤ i < q.
- For i = 0 this is the odd-marker note's own hypothesis: high byte ≥ 9, so ‖v‖ ≥ 9Q/256 > 2L once w > 57.
- For q = 2^s > 1, each ±iz lies within |δ| of a multiple of Q/2^s.
  - A word whose bytes all lie in [9, 126] is at distance more than 9Q/256^{b+1} from every nonzero multiple of Q/2^s, with b = ⌈s/8⌉. Otherwise the byte just below the top b bytes would have to be ≤ 8 or ≥ 247.
  - Such a word is also at distance at least 9Q/256 from 0.
  - Since 2L + |δ| ≤ 2Q/w + O(w), the hypothesis holds once w > (2/9)·256^{b+1}·(1+o(1)): a constant that depends on s only.

**Claim 3 (structure).** With the band colouring, the odd-marker note's paragraph "To see this, break the sequence into maximal consecutive visits …" holds word for word. It uses only three facts:
- special jumps start in J and land outside it (Claim 2);
- the stopping moment is a fresh read in I ⊆ J;
- every other transition moves to a neighbour on the public cycle or path, or stays put.

So at every boundary just after a fresh original read, each of the O(q|δ| + 1) segments carries a visited prefix and suffix, plus at most one interval overall for the start.

**Conclusion of (a).**
- **Order LSA.** The label has O(q|δ|·w) = O_P(w²) bits: the prefix and suffix lengths of every segment, the initial interval, the registers, the control state and the entry-turn exceptions. The odd-marker note's splice then applies without change. There are 2^{O_P(w²)} labels. Each covers at most a 2^{−γk} fraction of yes inputs, and k = Θ(N/log² N) with N ≈ Q, which is a contradiction for large j.
- **Order LAS.** The STORE at p follows the update, so it overwrites the next read address. Every LOAD after the first returns z (the map's Lemma B, first bullet), and only O(1) originals are read.

## 3. Finite checks of part (a)

**The arithmetic lemma.** Check (1) of `near_top_regime_and_bytes_check.py` enumerates, for every pair of operands in {0, n, w} and literals |c| ≤ 12:
- add, sub and mul;
- all 16 bitwise Boolean functions;
- five comparisons and moves;
- logical, arithmetic and left shifts and both rotations, with a literal count (positive or negative) or a register count (0, n or w), under two count rules: everything mod w, or saturating shifts with rotations mod w.

It does so at j ∈ {8, 16, 32, 64} (powers of two) and j ∈ {9, 13, 17, 25}, with m = m₀ + w·t for t < 4, and tests exactly the lemma's claim. Check (2) tries adversarial words for Claim 2 at w = 14,592: top byte equal to a band's top byte or one off, next byte 9, 10, 32 or 126, the rest extreme. Check (3) counts how often the read-only decimal family falls below Q/2 (Section 4). The script takes about 3 seconds:

```
(1) other j all other forms       : odd forms 155960, violating q in {1,2^s}, |delta| <= 2^(s+1)*max(m,w,c_P): 0
(1) other j negative-literal count: odd forms  17480, violating q in {1,2^s}, |delta| <= 2^(s+1)*max(m,w,c_P): 10205
(1) pow2 j  all other forms       : odd forms 155552, violating q in {1,2^s}, |delta| <= 2^(s+1)*max(m,w,c_P): 0
(1) pow2 j  negative-literal count: odd forms  17296, violating q in {1,2^s}, |delta| <= 2^(s+1)*max(m,w,c_P): 0
```

So the lemma holds as stated, and the violations occur only for negative-literal counts at j that is not a power of two. The independent check written during review, `near_top_forms_independent_check.py`, tests the lemma as first stated (without the power-of-two condition) and finds the same split. Every violation has a negative-literal count; there are none at powers of two:

```
modw j=  8 w=  128 m=  128 odd forms=  8853 violating=   0 (negative-literal count: 0, other: 0)
modw j= 17 w=  272 m=  256 odd forms=  8856 violating= 444 (negative-literal count: 444, other: 0)
sat  j= 64 w= 1024 m= 1024 odd forms=  8639 violating=   0 (negative-literal count: 0, other: 0)
```

**Claims 1–3 on synthetic memories.** `band_colouring_marker_check.cpp` uses Q = 2^w with L decoupled from n, so that the hypotheses of Claim 2 hold at small w:
- n = Q − m for m ∈ {48, 80, 112};
- 14 forms of z: n+1, n−3, 5−n, n⊕7, n|1, rotl(n,3), w+1, ¬n, rotr(3,1), rotr(w|1,2) (two instructions; a q = 4 test case), rotr(n,4), n>>4, rotr(n,5), n>>6. Even values are skipped as not in this row;
- the three updates;
- palettes of four words with bytes in [9,126] that avoid the bands;
- six public starts, including odd starts inside I, 0, n, w and a random word;
- three random inputs per configuration.

Every run enters the cycle at the LOAD. Entries at the STORE or the numerical instruction, which Lemma (a) also covers, add one public marked cell or one public first move; they were not simulated. The program checks the crossing count against the bound of Claim 1, that every fresh read starts in J and lands outside it, and, after every fresh read, that at most one visited component lies strictly inside a segment. The run at w = 16 takes about 30 seconds and the run at w = 20 about 5 minutes:

```
runs=1890 informative(>=2 fresh reads)=1260 fresh reads=75993 | violations: crossing-bound=0 jump-colour=0 interval-property=0
runs=2052 informative(>=2 fresh reads)=1368 fresh reads=379815 | violations: crossing-bound=0 jump-colour=0 interval-property=0
generic length n=387968 (0.37Q): z=n+1=387969, colour changes of J=[-L,L] along the z-cycle = 1202 (2L+1=601); best q<=256: q=100 |delta|=412
```

The last line is the failing case of Section 1 at w = 20: at that length no q ≤ 256 makes q·‖qz‖ small. Sample lines at w = 20, L = 300, where the original J has 2(2L+1) = 1202 changes along the cycle against 2|δ| for the band colouring:

```
  m=48 rotr(3,1)    z=524289   q=2   delta=+2    op=p+x changes(band J)=4 bound=4 changes(orig J=[-L,L])=1202
  m=48 n>>4         z=65533    q=16  delta=-48   op=p+x changes(band J)=96 bound=96 changes(orig J=[-L,L])=1202
  m=48 n>>4         z=65533    q=16  delta=-48   op=x-p changes(band J)=1392 bound=1490 changes(orig J=[-L,L])=601
```

The translation counts equal 2|δ|, and the x−p counts equal (2q−3)|δ| (1392 = 29·48) or |δ| for q = 1. During review every one of the 105 + 114 crossing counts was confirmed to be at most the exact bound. At these small sizes q|δ| for x−p with q = 16 still exceeds 2L+1; the asymptotic comparison, O_P(w) against Θ(Q/w), is the analytic one.

## 4. The length regimes of the seven prologue-branch classes

**Regime lemma** (manuscript). Assume a program with no prologue data instruction; the 7 classes are such programs (rule 4 of the map: no data before the cycle). Each prologue branch compares two words from {0, n, w} ∪ literals. For large n:
- comparisons among 0, w and literals are constant;
- n against 0, w or a nonnegative literal is constant as unsigned, and equals [n ≥ Q/2] as signed;
- n against a negative literal −c, whose value is Q − c, gives [n ≥ Q−c] or [n = Q−c] as unsigned, and [Q/2 ≤ n < Q−c] as signed.

So the regimes are unions of three kinds of length set:
- S_lo = {n < Q/2};
- S_hi = {Q/2 ≤ n < Q − c_P};
- the at most c_P/8 byte-aligned lengths above Q − c_P in each width block.

**Reduction.** P is incorrect as soon as, for one regime S, the five-slot program P_S fails at some length in S. If S sends P straight to a verdict, P is wrong at every large length of S. So (b) follows from (b′): each row cited by rule 4 fails the program at every sufficiently large length of a family that has infinitely many members below Q/2.

**Families, checked by reading** (each note's family statement only):

| note or family | lengths at which the family is built |
|---|---|
| one-site theorem | "For all sufficiently large byte-aligned N" |
| writable five-slot theorem | "at sufficiently large lengths divisible by w"; table family as below |
| private-probe table family | "select a byte-aligned length n near C(D+1)2^t t² … and append ordinary whitespace" |
| parity-pin family | every sufficiently large byte-aligned length |
| read-only decimal family | only N = 1024(j+1)·10^j |

For the decimal family, check (3) gives `lower half (N<Q/2): 357, upper half: 23` for j ∈ [20, 400). Since log₂10 is irrational, both regimes recur infinitely often. [Read-only five instructions](read-only-five-instructions-on-ordinary-sat.md) · [Writable five slots](writable-five-slots-without-a-clock.md)

**The one-site theorem, row by row.** Each row was read for two things: whether its contradiction holds at every large length of its family rather than along a subsequence, and whether it uses the size or sign of n relative to Q.

| row | family | contradiction at every large length? | uses n vs Q? |
|---|---|---|---|
| site without a y operand: bounded image ≤ \|B\|²+\|B\|+1 | periodic even-word base | yes: O(1) addresses against an unbounded sensitive interval | no |
| move, constant, comparison, bitwise (≤ 2^{2^{\|B\|}} words), one-direction shift (≤ w+1 per word), rotation (≤ w per word) | same | yes: o(N/w) addresses | no; B contains n and w, which are only counted |
| multiplication, or add/subtract with two mutable operands or an even fixed operand: parity | same | yes: the odd sensitive addresses are unreachable | no; it uses only that n and w are even |
| y ← c − y with c odd | same | yes: orbits of size two | no |
| y ← y + c with c a fixed odd literal: public cursor, O_P(w) bits of communication | word-aligned equality family | yes: k = Θ(N/log² N) against O_P(w) | no; laps and resets are bounded by s\|B₀\|^r, with B₀ = H ∪ {0, N, w} |

Where the families exist:
- The equality family exists "for all sufficiently large byte-aligned N".
- The periodic even-word base of the five-slot loop note uses 10^j clause lines of fixed even length, so its lengths N_j grow by a factor tending to 10, plus final padding. These lengths are sparse and need not meet every regime; for instance, they need not meet the at most c_P/8 lengths at the top of a block. But log₂ N_j mod 16 is equidistributed, so infinitely many N_j lie in S_lo, the only regime the argument uses. [Five-instruction loops](five-instruction-loops-on-dimacs-sat.md)

**So (b) holds for the four `C:AL` classes among the 7:** L1S0A2B3 `C:AL post:A` and `C:AL none:A`; L1S1A1B3 `C:AL post:S` and `C:AL none:S`. On S_lo the program either reaches a verdict through a bypass with boundedly many reads, which fails at every large length of the regime, or runs the one-site cycle with exit code; the one-site theorem then fails it at every large length of a family that has members in S_lo. The grounds differ by class, as found during review:
- **`post:A`** puts a second numerical site after the exit, so it is conditional on rule 4's exit-code extension: the six-instruction map's manuscript argument, checked during that note's review in the shape of the argument, not row by row.
- **`post:S` and `none:S`.** Reduction R-d of the case-split note deletes the STORE, since no LOAD follows it. The one-site theorem as written, which allows any comparison branches including prologue tests on n, then excludes the whole program without any regime argument.
- **`none:A`.** The bypass reads nothing, so on its regime it gives a constant answer. The cycle side is a plain one-site program.

[Case-split reductions](the-five-slot-case-split-is-exhaustive.md#5-four-reductions-the-case-split-uses-without-writing-out)

**The class map is updated.** The four classes move from REDUCES to EXCLUDED, and the totals go from 925/80/14 to 929/76/14:

| allocation | classes moved | classes, before → after (EXCL/REDUCES/OPEN) | labeled graphs, before → after |
|---|---|---|---|
| L1S0A2B3 | `C:AL none:A` (3,240 labeled), `C:AL post:A` (17,280) | 86/19/1 → 88/17/1 | 196524/96912/51840 → 217044/76392/51840 |
| L1S1A1B3 | `C:AL none:S` (1,620), `C:AL post:S` (8,640) | 149/22/1 → 151/20/1 | 234720/58716/51840 → 244980/48456/51840 |

**Not checked:**
- For `C:AAL` (read-only five-instruction theorem) and `C:ALS`/`C:ASL` (writable five-slot theorem), whether each row's contradiction holds at every large length of its family. Only the family statements above were read, so these 3 classes stay REDUCES.
- The padding of the one-accumulator family (N = Θ(K log² K) with a fixed header). [One-accumulator scan](one-accumulator-scan-without-a-clock.md)

**Interaction with (a).** The repair of (a) uses lengths near the top of a block, which lie inside S_hi. A larger program with both a prologue z and a prologue branch on [n ≥ Q/2] would need (a) below Q/2. There z = n+1 has norm n+1, which is exactly the failing case of Section 1.

## 5. The length-dependent stride

Of the even-multiplier note's open residues, only the length-dependent stride is treated here, and only in the class of part (a): the cycle LOAD x←M[p], NUM p←p+z, and one STORE, with z odd. The any-speed even-multiplier form and the odd multiplier 3 are not treated here. [Even-multiplier stores](even-multiplier-stores-in-a-six-slot-scan.md)

**q = 1 forms.** At the near-top lengths of Section 2, take j a power of two when the count operand is a negative literal; a rotation by −c is then the opposite rotation by c. At those lengths the q = 1 forms are all except:
- the logical right shifts;
- the right rotations by a nonnegative count;
- the left rotations by a negative count.

An arithmetic right shift of n is small, so q = 1. Without the power-of-two restriction the split fails: at j = 17, rotl(n, −12) = rotr(n, 28) is odd with ‖z‖ ≈ 2^252, and rotr(n, −12) = rotl(n, 28) has |δ| ≈ 2^36. The independent check `near_top_stride_split_independent_check.py`, written during review, tests the split as first stated, with only the logical right shifts and right rotations excluded. Every failure it finds has a negative-literal count; at powers of two these are the left rotations by −c, which the corrected split counts on the q = 2^s side:

```
modw j=  8 w=  128 m=  128 odd forms=  8853 violating= 131 (negative-literal count: 131, other: 0)
     e.g. rotl(n,-12) best 2^s: 12 norm(2^s z) = 4096 (~2^13)
modw j= 17 w=  272 m=  256 odd forms=  8856 violating= 144 (negative-literal count: 144, other: 0)
```

For the q = 1 forms z ≡ δ (mod Q) with |δ| = O_P(w), so translation by z *is* translation by the odd residue δ. The three proofs that the writable note cites for this row were read for every use of the stride:
- **Unshifted crossed scan** (STORE M[x]←p in order LSA). The stride enters only as "A fixed integer stride changes owners O_d(1) times per public period". With prefix and complement ownership, translation by δ crosses each of the two boundaries exactly |δ| times per period, so there are 2|δ| = O(w) changes. On the word-aligned family (h = O(1), O(1) periods) the protocol costs O(w²) = o(k) bits.
- **STORE through p** (writeback, self-mark, or a fixed mark including z; the writable note's row "For p←f(p)"). Stability within three periods does not use the stride. The communication again has 2|δ| owner changes per period, so O(w²) bits.
- **Shifted crossed scan** (STORE M[x]←p+z in order LAS). The bound k ≤ s + O((b+1)w) has no d in it. The construction uses d in three places, and each holds for |d| = O(w):
  - the span O(|d|k) of the sign stretch must be o(m), and here w·n^{1/16} = o(n/w);
  - the markers B_i at the scan predecessors i − d must lie inside the file;
  - the greedy marker choice excludes "a bounded number of required translates", which does not depend on d.

[Unshifted scan](unshifted-crossed-scan-without-a-clock.md) · [Arbitrary stride](arbitrary-stride-private-sign-erasure.md)

So, by reading, the stride row closes for q = 1 forms at near-top lengths. This is manuscript only; no proof was re-checked line by line. During review the use of d in the arbitrary-stride note and the identity p←p+z = p←p+δ (mod Q) were confirmed; the unshifted scan and the p←f(p) row beyond this account, the communication step for large δ and the q = 2^s sketch below were not.

One finite check. The journal's erasure audit covers only strides ±1, ±3 and ±5. `shifted_stride_erasure_large_strides.py` imports it unchanged and runs its `check_case` at width 1024 with strides of size O(w), over its own start set, in about 16 seconds:

```
strides and start counts: {-1023: 21, -111: 21, -47: 21, -7: 21, 47: 21, 111: 21, 255: 21, 1023: 21}
168 signed-stride/start cases at width 1024 on four proper DIMACS files each: all assertions passed
45 first-lap coalescences, 168 second-lap coalescences
```

In all 168 cases the four sign variants coalesce by the second lap: the compulsory schedule erases the private signs with these large strides as well. This checks the shifted scan's erasure step only, not the communication step. [Erasure audit](../audits/shifted_stride_erasure_audit.py)

**q = 2^s forms** (z ≈ tQ/2^s + e): the logical right shifts, the right rotations by a nonnegative count, and the left rotations by a negative count −c, which act as right rotations by c at power-of-two j.
- **Shifted crossed scan: fails as constructed.** The scan predecessor i − z of a sign site lies in a high band, where memory is zero and no marker word can be placed. Every such predecessor then reads 0 and writes its payload to address 0, a hub shared by all sites. The per-site stamp of the erasure argument is lost. Open.
- **Unshifted scan and STOREs through p: a plausible repair, not checked.** Each q-block of the orbit contains at most one input cell. Give each block to the owner of its input cell, and give blocks without one to the previous owner. The input cells are then visited in runs of step δ, with an estimated O(|δ|) owner changes per period. This is a sketch only.

So the class of part (a) stays REDUCES: it keeps the q = 2^s stride forms and the unary reverse-link row.

## 6. The three standard tests

No time bound is claimed; this is a program-size statement.
- **(a) Fast globally correct solver?** Yes. The parity-pin family has a linear-time RAM solver (the parity-pin note, last two paragraphs), and the journal's 43-instruction program decides all inputs. [Parity-pinned SAT](orbit-orders-and-parity-pinned-sat.md) · [A 43-instruction SAT program](a-43-instruction-sat-program-in-the-five-slot-machine.md)
- **(b) Same argument for 2-SAT?** Expected yes. The argument uses sensitivity, a bounded byte palette and an expander-cut rectangle bound. Parity pins X_u ⊕ X_v = b can be written with 2-clauses, so a 2-CNF version of the family should work. Not checked.
- **(c) Relativization.** Both oracles fail at the step that one LOAD returns one w-bit word from a bounded palette. That step supplies the special-jump colours and the label. With the packed oracle of the relativized-clock note, or the multilinear oracle, a constant number of instructions decides SAT. [Relativized clock](relativized-clock.md) · [Multilinear oracle](multilinear-oracle-clock.md)

## 7. Exact obstruction and next step

1. **Arbitrary public markers, and D ≥ 2.** No replacement colouring is known in the following cases, where the original J has Θ(L) crossings:
   - an odd public z(n) that is not one instruction over {0, n, w, literals}, as happens in larger programs, may have no usable length where some q has q·‖qz‖ = O(polylog N);
   - at the wider widths w = 16⌈D·log₂(n+2)/16⌉ with D ≥ 2 that the odd-marker note also allows, already z = n+1 has norm n+1 > 2L at every length;
   - for a program with a prologue branch on [n ≥ Q/2], the lengths below Q/2 are needed.
   - The open statement is: "the visited set of the odd-marker walk at the half-sign boundary has a description of o(k) bits for every odd z".
   - The w = 20 generic-length line of Section 3 is an instance: no q ≤ 256 has q·‖qz‖ < 2L+1.
2. **The stride row of the class of part (a).** Section 5 settles it by reading for q = 1 forms. The precise open statement for q = 2^s is: "the shifted crossed scan p←p+z, M[x]←p+z, with z ≈ tQ/2^s, cannot decide the equality family at any speed". The erasure construction needs a marker at the scan predecessor of each sign site, and here that predecessor lies outside the file.
   - The next try is a layout whose sign sites have their q-th predecessor i − δ inside the file, with the marker carried through q−1 zero cells. Whether a stamp survives that chain is unchecked.
   - The unary reverse-link row with an odd start remains in any case.
3. **(b′) row by row** for the read-only and writable five-slot theorems, which would settle `C:AAL`, `C:ALS` and `C:ASL`, and the one-accumulator family's padding.
4. **The operand enumeration** of the single-numerical-site cycles is not done here.

## 8. What is not proved

- Part (a) changes no class status: the class it treats stays REDUCES.
- The arithmetic lemma is restricted to j a power of two when the count operand is a negative literal; without that restriction it is false (Section 2).
- Lemma (a) is manuscript only and holds at the standard width D = 1 only. It closes the odd-marker row with a prologue-computed marker in its class, at near-top lengths where z is odd. The even values at those lengths (right shifts and rotations of n by s ≤ 3) rest on the map's unchecked even-payload remark.
- The finite check of Claims 1–3 is synthetic. L is decoupled from n, the palettes are filtered to meet Claim 2, and the widths are small. Claim 2 at real sizes rests on the byte argument, checked only on adversarial words at one width. The splice argument itself is the odd-marker note's manuscript proof, which was not re-checked.
- (b) is reduced to (b′). It is checked row by row only for the one-site theorem, which covers the four `C:AL` classes. Of those, only `post:A` is conditional on rule 4's exit-code extension. For the other three classes only the family statements were read.
- Section 5 rests mainly on reading. The q = 1 closure of the stride row has no line-by-line re-check of the three cited proofs. Its only finite check is the erasure audit rerun with strides up to ±1023 (168 cases); the communication step was not simulated. The q = 2^s ownership repair is a sketch.
- Nothing here bears on the linear, quadratic or cubic time targets.

## Reproducing the checks

Run from `audits/`; no script writes files.

```
python3 near_top_regime_and_bytes_check.py
python3 near_top_forms_independent_check.py
python3 near_top_stride_split_independent_check.py
python3 shifted_stride_erasure_large_strides.py
c++ -O2 -std=c++17 band_colouring_marker_check.cpp -o /tmp/band-colouring-marker-check
/tmp/band-colouring-marker-check 16 60 1 4000000
/tmp/band-colouring-marker-check 20 300 2 20000000
```

The Python scripts take about 3 seconds, under a second, under a second and about 16 seconds. The C++ check takes about 30 seconds at w = 16 and about 5 minutes at w = 20. The class map's marking script and cross-check now carry the four classes as EXCLUDED. [Regime and byte checks](../audits/near_top_regime_and_bytes_check.py) · [Independent forms check](../audits/near_top_forms_independent_check.py) · [Independent split check](../audits/near_top_stride_split_independent_check.py) · [Large-stride erasure](../audits/shifted_stride_erasure_large_strides.py) · [Band colouring check](../audits/band_colouring_marker_check.cpp)
