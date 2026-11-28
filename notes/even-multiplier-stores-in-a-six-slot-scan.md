# Six-slot scans that store an even multiple of the cursor need Ω(N²/log⁴N) steps to answer every equality file correctly

Consider the six-stored-instruction programs of the form x = M[p]; M[x] ← a·p; p += d with two branches, where a is even and d is a fixed nonzero integer, in any of the six data orders. Let N be the bit length and let the word width be w = 16⌈D·log₂(N+2)/16⌉. Every such program that answers correctly on every equality file of length N needs Ω(N^{D+1}/log⁴N) steps on some satisfiable equality file, with constants depending on D and d. At standard width (D = 1) this is Ω(N²/log⁴N). The proof combines a closed-set memory invariant formulated by an external review (if H ⊆ U and f(U) ⊆ U, every cell lies in U or holds a value in U), the orbit bound ⌈w/v₂(a)⌉+1 for even multipliers, and the buffered protocol of the communication note. The proof is at manuscript level and was checked during review with independent code on real equality files. With explicit constants the bound is positive only from about N = 2^34 bits at D = 1. The architecture is an operand subfamily of three classes that the six-instruction class map leaves open, so no class changes status. For odd literal strides the bound is vacuous at the following lengths. Take native initialization, a an even literal or a = w (or a = n when D ≥ 2), and d an odd literal. Then every member, at every byte-aligned length N beyond a threshold depending on the member, runs identically on an equal file and on an unequal file that differs from it in one of Bob's bits. This holds when gcd(3K+4, |d|) = 1, where 3K+4 is the clause length in words (always true for d = ±1, ±3), and, at D = 1, when N lies outside one exceptional interval of length 13·2^{w−16}. So no such member decides the equality files or SAT at any speed (manuscript; [odd strides at every speed](even-multiplier-scans-with-odd-strides-fail-at-every-speed.md)). The bound may still be vacuous for even strides (including a = d = 2), for a = n at D = 1, at the remaining lengths, for arbitrary public initial registers and for the other payloads of the generic corollary. Nothing here bears on the unrestricted RAM. Odd multipliers other than ±1 and lookbehind payloads have a clock-only bound of Ω(N^{D+1/2}/log²N) in the [odd-multiplier note](odd-multiplier-stores-in-a-six-slot-scan.md); masks or rotations after the shift stay open; the linear, quadratic and cubic questions remain open. [Communication bound for public crossed scans](communication-bound-for-public-crossed-scans.md) · [Six-instruction control classes](six-instruction-control-classes-in-the-five-slot-machine.md)

## The architecture and the statements

**Architecture A(a,d).** Six stored instructions in the journal's separate-operation RAM. Four are data instructions on one recurrent cycle:
- `LD`: x ← M[p];
- `MU`: y ← a·p mod Q;
- `ST`: M[x] ← y;
- `AD`: p ← p + d mod Q.

The other two are comparison branches with fixed targets. Here:
- Q = 2^w, and the registers x, y, p are distinct.
- a is a literal or a public word (0, n or w) that is even at the length considered. n is the bit length, so a = n is a multiple of 8 and always even.
- d is a fixed nonzero literal integer.
- The data instructions may come in any of the 6 cyclic orders.
- The branches either both lie on the cycle, each exiting to one verdict, or one lies on the cycle and exits to the second, which chooses the verdict. With two branches these are the only layouts in which the cycle can still reach both verdicts. As checked during review, the control graph has cyclomatic number 1, and the three classes have no off-cycle data instruction and no graph with a prologue branch before a cycle that reaches both verdicts. A prologue branch before a one-verdict cycle gives a constant verdict at each length, which is wrong on one kind of equality file, as the six-instruction note observes.
- Entry is at any instruction, under native initialization (registers 0 except optional public n, w). The proof also allows arbitrary public initial registers.

[Five instructions cannot decide DIMACS SAT](five-instructions-cannot-decide-dimacs-sat.md)

**Lemma 1 (closed-set invariant).** The statement and a short proof were given by an external review. Let f: Z_Q → Z_Q be any map. Consider any finite sequence of operations of the form "read x = M[p] at an arbitrary, possibly adaptive address p; then either do nothing or write M[x] ← f(p)", with no other write between the read and its write. Let H contain the image of the initial memory and U ⊇ H satisfy f(U) ⊆ U. Then at every time, for every z, z ∈ U or M[z] ∈ U.

**Lemma 2 (orbits).** If a is even and c is arbitrary, then for every h the forward orbit {g^j(h) : j ≥ 0} of g(z) = a·z + c mod 2^w has at most ⌈w/v₂(a)⌉ + 1 ≤ w + 1 elements. If a ≡ 0, the orbit has at most 2.

**Theorem (transfer).** Fix D ≥ 1, a nonzero integer d, and a program Π of A(a,d) with a even. Let N be any sufficiently large byte-aligned length. Suppose Π gives the correct SAT answer on every equality file of the communication note at length N. Then on some satisfiable such file Π executes at least

T ≥ (k / (6(|d|+1)·h'·w²) − 1) · (N+2)^D / |d|

instructions. Here:
- k = ⌊N/(C_D log₂²N)⌋ is the number of private bits;
- h' := h_D + 2 = O_D(1) bounds |H'| (defined in Section 3) uniformly for every file of the family at length N;
- h_D is the communication note's palette bound;
- N is the bit length;
- w ≥ 8.

Hence every such correct Π has T = Ω_{D,d}(N^{D+1}/log⁴N) on some satisfiable equality file. [A constant word alphabet for deterministic equality](communication-bound-for-public-crossed-scans.md#a-constant-word-alphabet-for-deterministic-equality)

## 1. Proof of Lemma 1

The claim holds initially, because the image of memory is contained in H ⊆ U. A skipped write changes nothing. A write M[x] ← f(p) changes only cell x. Its value x was read from M[p], and nothing was written in between, so M[p] = x before the write. By the claim at z = p, either x ∈ U, and then cell x satisfies the claim whatever it holds, or p ∈ U, and then the new content f(p) lies in f(U) ⊆ U. ∎

Corollary (dichotomy): if the read returns x ∉ U, then p ∈ U.

**Checks.** Mode `inv4` covers every map f on Z_4, every initial memory and every adaptive read sequence, by breadth-first search over reachable memories. The control line shows that with U = H (no closure) the dichotomy fails in 33,336 of the 65,536 runs, so the closure hypothesis is needed:

```
inv4: Q=4, all 256 maps x all 256 initial memories, adaptive reads: BFS runs=65536, reachable states=1457605, max per run=144, cell checks=5830420, violations=0
inv4 control: runs in which U=H (no closure) fails the dichotomy at a reachable state=33336
```

Mode `inv8` covers Q = 8, the 32 maps a·p+c with a even, all 7,120 memories with at most two values, and all adaptive reads. Mode `walk` runs random walks on arbitrary, even-affine and small-image maps, with half the reads aimed at cells whose content is outside U:

```
inv8: Q=8, 32 even-affine maps x 7120 memories (<=2 values), adaptive reads: BFS runs=227840, reachable states=70470560, max per run=5569, violations=0
walk: 86000 random adaptive walks (arbitrary, even-affine and small-image maps; w in 3..12), steps=69808000, stores outside U=21913123, violations=0
```

## 2. Proof of Lemma 2 and the orbit table

Write s = v₂(a) ≥ 1 and g^j(h) = a^j h + c(1 + a + … + a^{j−1}). For j ≥ J = ⌈w/s⌉ we have a^j ≡ 0, so g^j(h) = c(1 + … + a^{J−1}) is constant. Hence the orbit is {g^0(h), …, g^J(h)}. ∎

Mode `orbit` computes exact maxima over all parameters and all starts h for w = 1..12; the affine family is exhaustive only for w ≤ 9. The header and the rows for w = 4, 8 and 12:

```
orbit: w | max orbit: mulEven  bound ceil(w/v2(a))+1 viol | affineEven(w<=9) viol | and or xor neg not c-p | shl shr (bound ceil(w/s)+1) viol | rotl (bound w/gcd) viol | square | contrast add1 mul3
orbit:  4 |   5 viol=0 |   5 viol=0 | 2 |   5 viol=0 |   4 viol=0 |   3 |    16     4
orbit:  8 |   9 viol=0 |   9 viol=0 | 2 |   9 viol=0 |   8 viol=0 |   7 |   256    64
orbit: 12 |  13 viol=0 | (skip)  0 viol=0 | 2 |  13 viol=0 |  12 viol=0 |  11 |  4096  1024
orbit sampled: w=64, 200000 even affine maps a*p+c and starts h: max orbit=65, violations of ceil(w/v2(a))+1 and w+1=0
```

Payload maps of one numerical instruction on p and a constant fall into three groups:
- **Orbit ≤ 2:** AND/OR/XOR masks, negation, complement and c−p, all with maximum exactly 2.
- **Orbit ≤ w+1:** even multipliers, even affine maps, shifts (≤ ⌈w/s⌉+1), rotations (≤ w/gcd(w,s)) and squaring (w−1 for w ≥ 4; 3 at w = 3, from 2 → 4 → 0).
- **Unbounded contrasts:** the translation p+1 has orbit Q, and the odd multiplier 3 has orbit Q/4 (the order of 3 mod 2^w).

This confirms the external review's classification of orbits for the instruction maps themselves, with the exact constants above. In the δ = ±1 orders the relevant map is the shifted one; see the generic corollary in Section 4.

The even-multiplier and squaring orbit facts are already in the obtainable-words case split of the bounded-RAM note, where they serve a five-slot program with no scan counter. The new ingredient here is their use as the closed set U of Lemma 1 inside a public scan, where AD enumerates addresses and the obtainable-words argument no longer applies. [Bounded RAM programs](bounded-ram-programs-and-separate-sat-witnesses.md#what-this-eliminates-on-ordinary-explicit-sat-for-every-linear-multiplier)

## 3. Reduction of every member to "payload = f(read address)"

Index iterations from one LD to the next.
- Iteration i reads x_i = M[p_i], with p_i = p_0 + i·d mod Q and p_0 the cursor at the first LD. p_0 is public: it is p_init, or p_init + d if the prologue ran AD.
- x is written only by LD, so ST in iteration i writes to x_i.
- y is written only by MU.

Let κ ∈ {0,1} be the number of AD instructions between LD and MU in the cyclic order. If MU precedes ST in the iteration, the payload is a·p_{i+κ}. Otherwise the payload comes from MU of iteration i−1 and equals a·p_{i−1+κ}, except in iteration 0, where it is the value y_0 of y at the first LD.

So the payload is f(p_i), with f(z) = a(z + δd), where δ is determined by the cyclic order. The last column is the coarse class of the six-instruction class map:

| cyclic order from LD | δ | class |
|---|---|---|
| LD MU ST AD | 0 | `C:ALAS` |
| LD AD ST MU | 0 | `C:ALAS` |
| LD MU AD ST | 0 | `C:AASL` |
| LD AD MU ST | +1 | `C:AASL` |
| LD ST AD MU | 0 | `C:AALS` |
| LD ST MU AD | −1 | `C:AALS` |

The one exception is the first store, whose payload y_0 is public.

**Prologue.** The instructions from the entry to the first LD run at most once, on public registers.
- A branch there has a public outcome. An exit gives a constant verdict, which is wrong on one of the two kinds of equality file.
- At most one ST runs, M[x_init] ← y, with public address and payload. Both parties can apply it without communication.

Define H' = (image of memory at the first LD) ∪ {y_0}. Then |H'| ≤ h + 2 ≤ h' := h_D + 2 for every file of the family, where h ≤ h_D is the image size of the input memory. Lemma 1 applies with f and H'. The first store is covered because y_0 ∈ H' ⊆ U.

By Lemma 2, U = ∪_{j≤w} f^j(H') is closed under f and has |U| ≤ (w+1)h'.

## 4. Protocol and accounting

**Ownership.** Alice owns the word addresses [0, α] (the header and her clause list). Bob owns (α, Q), which includes his list, the padding and all memory outside the file. Each party knows the public layout.

**Phases.** The active party is the owner of the address of the next LD. A handoff happens exactly before an LD whose address belongs to the other party. Let B = {z : z and z+d mod Q have different owners}.
- |B| ≤ 2|d|: a step changes owner only if it starts fewer than |d| positions before one of the two boundary points.
- Let m be the number of LDs, L = Q/gcd(Q,d) the scan period, and P = ⌈m/L⌉. Each address occurs at most P times among p_0..p_{m−1}.
- Hence there are at most 2|d|P handoffs and at most 2|d|P + 1 phases.

**Simulation.** The active party runs every instruction.
- LD reads its own copy.
- ST to an owned address updates the copy. ST to a foreign address overwrites an entry in a buffer.
- At a handoff it sends:
  - a type bit, the 3-bit PC and the registers x, y, p (3w bits);
  - each buffered pair as a continuation bit plus 2w bits;
  - a terminator bit.
- The receiver applies the buffer and continues.
- When the run halts, the active party sends a type bit and the verdict.

By induction over phases, each party's copy is exact at every owned address when it becomes active: during a phase only the active party writes, and the buffer holds the last value written to each foreign cell. So every LD is simulated exactly. The transcript is prefix-free and the speaker is determined by the previous message, so this is a deterministic protocol. It need not know H' or U.

**Records.** Split each phase's set of foreign destinations at U.
- Destinations in U: at most |U| per phase.
- Destinations outside U: by the dichotomy, each such store follows an LD at p_i ∈ U. Stores map injectively to their LDs, and there are at most P|U| LDs at addresses in U.
- So records ≤ (2|d|P+1)|U| + P|U|.

**Bits.**
C(P) ≤ 2|d|P(3w+5) + ((2|d|+1)P+1)(w+1)h'(2w+1) + 2.
For w ≥ 8 and P ≥ 1, this is at most 6(|d|+1)h'w²P, using 3w+5 ≤ w²/2 and (w+1)(2w+1) ≤ 2.5w². The algebra was checked during review.

**Equality.** The files carry k private bits per party and are valid proper ASCII 3-CNF. They are satisfiable exactly when the strings agree, and their initial memory has image size h ≤ h_D = O_D(1) for every pair (the communication note).
- Suppose two diagonal pairs shared a transcript. By the rectangle property the unequal cross pair, also a valid file in the family, would get the same accepting transcript, contradicting correctness.
- So the 2^k satisfiable files have distinct prefix-free transcripts, and one of them has length ≥ k.
- Hence C(P_max) ≥ k, where P_max is the largest pass count on the satisfiable files, so P_max ≥ k/(6(|d|+1)h'w²).

**Time.** That run has m ≥ (P_max − 1)L + 1 LDs. Also L ≥ Q/|d| ≥ (N+2)^D/|d|, and each iteration executes 4 data instructions and at least one branch. This proves the stated T.

Substituting w ≤ D log₂(N+2) + 16 and k = Θ_D(N/log²N) gives Ω_{D,d}(N^{D+1}/log⁴N) for every member that answers correctly on every equality file of length N. The external review's estimate, "roughly Ω(N²/log⁴N)", is the case D = 1.

**Variant with polynomially bounded identifiers (manuscript, not checked).** Use the polynomial-identifier variant of the same note: k = Θ(N/log N), and h ≤ N^{D/(8t)+o(1)} for a fixed spacing t. Since C is linear in h', every member that answers correctly on those files needs T ≥ N^{D+1−D/(8t)−o(1)}. So such members cannot run in time O(N^c) for any c < D+1.

**Why the arbitrary-payload control example of the communication note does not apply.** There, the payloads β_{i+1}, γ_{i+1}, δ_i and A_i are chosen by the controller and include a private bit A_i. Here the payload is f(p_i), a public function of the iteration index. Information moves only through which cell receives a public stamp, and the dichotomy bounds those cells. [The control experiment](communication-bound-for-public-crossed-scans.md#a-control-experiment-when-arbitrary-words-can-be-written)

**Generic corollary.** Let g be the payload instruction's map, so that the effective map is f(z) = g(z + δd). The same proof works whenever all forward orbits of f have size ≤ β(w). It gives C(P) = O_d(P·h'·β·w). Every member that answers correctly on every equality file of length N then needs T = Ω(N^{D+1}/(β(w)·w·log²N)).
- In the four δ = 0 orders, f = g. There the β = 2 maps of Section 2 give Ω(N^{D+1}/log³N), and the β ≤ w+1 maps give Ω(N^{D+1}/log⁴N).
- In all six orders, negation, complement and c−p stay involutions after the shift: for every shift e, g(z+e) = c′−z, so β = 2. Left shifts by a literal s are multiplication by 2^s, an even multiplier, so Lemma 2 applies. a = −1 is the negation case.
- In the two δ = ±1 orders other maps can lose small orbits, which corrects the external review's classification for those orders. For example, (z+1) XOR 1 sends odd z to z+2, and (z+2) AND ~1 sends even z to z+2. Both have orbits of Q/2: at Q = 256 the orbit of 1, respectively 0, has 128 elements.
- An exhaustive table of shifted maps written during review (all w ≤ 9, all shifts e ≠ 0, all constants and starts) gives these maximum orbits:

| shifted map | max orbit at w ≤ 9 | status here |
|---|---|---|
| c−(z+e), ~(z+e), −(z+e) | 2 | covered (involution, proved) |
| (z+e)<<s, a(z+e) with a even | ≤ w+1 | covered (Lemma 2) |
| (z+e)>>1 | 2w−1 | small at w ≤ 9, no proof |
| (z+e)² | ≤ w+1 (3, 4, 5, 5, 6, 7, 7, 8 for w = 2..9) | small at w ≤ 9, no proof |
| rotl1(z+e) | up to Q−1 (244 at w=8, 511 at w=9) | not covered |
| (z+e) AND/OR/XOR m | Q | not covered |

Its rows for w = 8 and 9:

```
w | c-(z+e) | ~(z+e) | -(z+e) | (z+e)<<1 | (z+e)>>1 | rotl1(z+e) | (z+e)^2 | (z+e)&m | (z+e)|m | (z+e)^m | 2(z+e)+c
8 | 2 | 2 | 2 | 9 | 15 | 244 | 7 | 256 | 256 | 256 | 9   (Q=256)
9 | 2 | 2 | 2 | 10 | 17 | 511 | 8 | 512 | 512 | 512 | 10   (Q=512)
```

Even multipliers survive the shift by Lemma 2, which is why the main theorem covers all six orders.

## 5. Checks of the transfer's accounting

**The direct machine against the protocol.** `even_multiplier_scan_checks.cpp` contains a generic interpreter for A(a,d) with any data order, either branch layout and any entry point. It runs the direct machine and the two-party protocol side by side. At every step it checks:
- the invariant at each store;
- the read dichotomy;
- stores outside U ≤ P|U|;
- distinct destinations ≤ (P+1)|U|;
- that each party's LD equals the true memory.

At the end it checks phases − 1 ≤ 2|d|P, records ≤ phases·|U| + P|U|, bits ≤ C(P), and the final memory. Mode `scan8` is exhaustive at Q = 8: all 7,120 memories with at most two values, all 6 data orders, all even a, d = 1..7, all p0, 40 loads. Mode `proto` runs random members on a synthetic equality layout (header, Alice's and Bob's bit words, filler, zeros) at w ∈ {8, 10, 12}, with random branch tests and entries, and caps of up to 6 passes:

```
scan8: runs=9569280 (>=2 passes: 9569280), steps=2296627200, max passes=20, max phases=40
scan8: violations: invariant(store)=0 read-dichotomy=0 final-memory=0 outside-U>P|U|=0 dest>(P+1)|U|=0 sim-mismatch=0 phases=0 records=0 bits=0 verdict=0
scan8: max records/bound=0.6452, max bits/bound=0.8346; labels: C:AALS=3189760 C:AASL=3189760 C:ALAS=3189760; deltas: -1=1594880 0=6379520 1=1594880
proto: runs=24600 (>=2 passes: 11291), steps=106962085, max passes=48, max phases=97
proto: violations: invariant(store)=0 read-dichotomy=0 final-memory=0 outside-U>P|U|=0 dest>(P+1)|U|=0 sim-mismatch=0 phases=0 records=0 bits=0 verdict=0
proto: max records/bound=0.2707, max bits/bound=0.3684; labels: C:AALS=7182 C:AASL=7119 C:ALAS=7044; deltas: -1=3590 0=14173 1=3582
```

In the `proto` run, 3,255 of the 24,600 runs ended in the prologue on a public test, so the label counts sum to 21,345. The class labels use the same minimum-rotation rule as the six-instruction enumerator.

**Independent checks on real equality files.** Code written during review from the note, not from the code above, repeats the checks of Lemmas 1 and 2 and the protocol:
- Lemma 1 by breadth-first search at Q = 4 (every map and memory, matching the numbers above exactly) and at Q = 8 (all 32 even-affine maps and 1,508 memories with any number of distinct values), with the same control, and by adversarial walks;
- Lemma 2 exhaustively for w ≤ 10 (all even a, all c, all h; the maximum w+1 is attained at a = 2) and by sampling at w ∈ {16, 32, 48, 64};
- the two-party simulation on the words of an actual equality file (N = 2^18 bits, w = 24, h = 13, α = 4409): 48 members over all six orders, strides ±1, ±2, ±3, 5 and 7, and both branch layouts.

```
inv4: all maps x all memories: runs=65536 reachable-states=1457605 max-per-run=144 violations=0; control U=H fails in 33336 runs
inv8: 32 even-affine maps x 1508 arbitrary memories: runs=48256 reachable-states=26519405 max-per-run=15751 violations=0; control U=H fails in 28695 runs
orbit sampled w in {16,32,48,64}: tests=200000 max=65 violations=0
proto: file words=10923 alpha=4409 h=13 w=24
proto: runs=48 (>=2 passes: 5, max P=3) violations: sim=0 phases=0 records=0 outsideU>P|U|=0 bits=0 invariant/payload=0 dichotomy=0; worst records/bound=0.1429 bits/C(P)=0.0194
```

**The equality files themselves.** The note takes h_D = O_D(1) from the communication note. An independent generator written during review, `equality_file_generator.py`, builds the actual ASCII files, packs them into little-endian words with zeros outside the file, and reports the image size h. For N = 2^17 … 2^22 bits, h is 13–14 at D = 1, 11–12 at D = 2 and 12 at D = 3, independent of the private strings. Every file is valid DIMACS, and the party boundary falls on a word boundary. CaDiCaL agrees that satisfiable ⇔ equal:

```
N D w W k K | h(image incl. 0) | alpha_word | words | header-words-distinct
1048576 1 32 4 81 7 | 13 [13] | 8109 | 32768 | 5
4194304 1 32 4 270 9 | 14 [14] | 33492 | 131072 | 6
union of images over 20 random pairs at N=2^20, D=1: 13
cadical: sat==equal on 40 of 40 small files (k=16, w=24), mismatches=0
```

**Where the bound becomes positive.** The test at small sizes would look for a member that decides the equality files faster than the bound. At feasible k it is vacuous: C(1) already exceeds k, so no small-size run can contradict the bound. The explicit bound is positive only when k > 6(|d|+1)h'w². Take d = 1, h' = 16 and C_1 = 32, the values of the generated D = 1 table above (h = 13–14 at w = 32, for N up to 2^22). Then the bound first becomes positive near N = 2^33.9 bits, where w = 48 and k first exceeds 6·2·16·48² = 442,368; this threshold is computed here. The constants carry over to w = 48: there the generator gives h = 11–12 with C_1 = 32, and by the communication note's byte count the files with C_1 = 32 still fit at N = 2^33.9. A smaller admissible C_1 would lower the threshold. In an evaluation during review, the bound is negative at N = 2^30 and positive at 2^40, and at D = 1 the ratio T/(N²/log₂⁴N) is 1.1·10⁻⁴, 1.4·10⁻⁴ and 1.1·10⁻⁴ at N = 2^40, 2^60 and 2^80. (At N = 2^80 the width rule gives w = 96; an earlier figure of 1.6·10⁻⁴ there came from rounding log₂(2^80 + 2) to 80 in floating point, found during review of a later note.)

As a weaker probe, mode `eqsearch` tried 200,000 random members on the synthetic layout with w = 8. This is weak evidence that the architecture decides little, not a proof:

```
eqsearch: w=8, k=1: random members tried=200000, halting on all 4 inputs=188782, deciding equality on all inputs=1
eqsearch: w=8, k=2: random members tried=200000, halting on all 16 inputs=188962, deciding equality on all inputs=0
```

## 6. Placement in the six-instruction class map

A(a,d) has opcode mix L1S1A2B2. Its six data orders fall into three coarse classes, as in the table of Section 3: `C:ALAS`, `C:AASL` and `C:AALS`. In the class table `six_slot_control_classes.tsv` all three are OPEN, each with 720 labeled graphs, 14 fine classes and no graph with a prologue branch before a two-verdict cycle.

The proof does not depend on branch positions, so it covers every fine class of the three, including those whose second branch lies on the exit path. It covers only the operand subfamily "MU computes a·p with a even, AD advances p by a fixed literal". The result is a clock-only bound for an operand subfamily, so all three classes stay OPEN and none of the map's totals changes. The two-ahead lock, a translation payload p+2d, is an any-speed member of `C:ALAS`. Under native initialization, the members with an even literal multiplier or a = w and an odd literal stride are now any-speed members of all three classes ([odd strides at every speed](even-multiplier-scans-with-odd-strides-fail-at-every-speed.md)). The classes stay OPEN. Via the generic corollary, the same clock bound covers the payload instructions of orbit ≤ 2 or ≤ w+1 in the four δ = 0 orders, and negation (a = −1), complement, c−p and left shifts in all six orders. [Six-slot two-ahead lock](six-slot-two-ahead-lock.md)

Not covered:
- non-multiplier payloads in the two δ = ±1 orders other than negation, complement, c−p and left shifts. After the shift, masks can reach orbit Q and rotations can come close to it. Right shifts and squaring stay at orbit ≤ 2w−1 for w ≤ 9 but have no proof here.
- odd multipliers other than ±1, and a = +1 in the order LD ST MU AD (payload p_{i−1}); the [odd-multiplier note](odd-multiplier-stores-in-a-six-slot-scan.md) bounds both by Ω(N^{D+1/2}/log²N), clock-only. a = −1 is covered in all six orders, since f(z) = −(z+δd) is an involution. a = +1 in the other five orders gives the payload p_i or p_{i+1}, the crossed scans of the ancestry note and the communication note.
- translations p + c, unless c + δd ≡ jd for a fixed j ≥ 0. In that case the payload is p_{i+j}, the r-lookahead scan of the communication note. Negative offsets (lookbehind payloads), and the other offsets that are not lookahead-aligned, are covered by the translation remark of the [odd-multiplier note](odd-multiplier-stores-in-a-six-slot-scan.md) (manuscript, checked at the index level).
- payloads that read x or y;
- length-dependent strides d ∈ {n, w}. For these the O_d(1) phase count per pass fails as written.

[Ancestry of crossed stores](ancestry-of-crossed-stores.md) · [Two-ahead stores in a six-slot scan](two-ahead-stores-in-a-six-slot-scan.md)

## 7. The three standard tests

- **(a) Fast globally correct solver on the hard family?** Yes. A packed comparison of the two halves decides the equality files in O(N/w) steps on the unrestricted RAM. The bound is specific to the architecture.
- **(b) Same bound for 2-SAT?** Yes. Forcing each literal with (ℓ∨u)∧(ℓ∨¬u) gives a constant-palette 2-CNF equality family, and the proof is unchanged. So the bound reflects the architecture's communication limit, not SAT's hardness.
- **(c) The oracle of the relativized-clock note?** The proof uses exactly that each instruction touches one w-bit word. Simulating one oracle query on a packed string that straddles the party boundary can cost up to k bits of communication, so the per-step accounting fails and the bound does not relativize. This is consistent with the barrier, but only because the model is restricted. It gives nothing toward the unrestricted RAM. [Relativized clock](relativized-clock.md)

## 8. Exact obstruction and next step

- **Any speed.** Done for odd literal d under native initialization, by covered swaps ([odd strides at every speed](even-multiplier-scans-with-odd-strides-fail-at-every-speed.md)). Odd stamp cells outside the palette are never written, and every group of four clauses holds both sign words at odd addresses, so the two stamps are overwritten alike before they are read. It remains open for even d, for a = n at D = 1, at the lengths in the exceptional interval at D = 1, for odd d with gcd(3K+4, |d|) > 1 at the given length, for arbitrary public initial registers, and for the other payloads of the generic corollary. When the scan coset lies inside aZ_Q (e.g. a = d = 2), every scanned cell can be written and the cover argument fails.
- **Odd multiplier, e.g. a = 3 (the sketch below; proved for every odd |a| ≥ 3, with checks, in the [odd-multiplier note](odd-multiplier-stores-in-a-six-slot-scan.md)).** Closure fails: U = ∪_j 3^j H' has size about Q/4. The last-writer map F(u,v) = (v, a·u) has F² = (a·u, a·v), so each two-link group multiplies the scan position by a.
  - With d = 1 and p_0 = 0, group endpoints satisfy u_{s+1} ≡ 3u_s (mod Q). Within one pass the residues can increase only along runs of O(w) steps: expansion away from the repelling points 0 and Q/2. Each non-increase costs a pass.
  - That would give chains of length O(Pw), a set U_P of size O(Pw·h'), records O(P²w·h'), and T = Ω(N^{D+1/2}/log²N) for members that answer correctly on the equality files.
  - This needed a proof of the run-length bound for general odd a, d and p_0, plus a check; the odd-multiplier note gives both (its Lemmas 0 and A).
- **Lookbehind payloads.** These look like an easy variant: two-link groups satisfy v − u ≡ −1 mod L, so v − u ≥ L − 1. This was suggested during review; the [odd-multiplier note](odd-multiplier-stores-in-a-six-slot-scan.md) proves the lookbehind bound through its run-length lemma, with R = 1.
- **Length-dependent stride d ∈ {n, w}.** The phase count per pass is then up to 2|d|. For d = w it costs one more log factor. For d = n it needs the pin placement of the one-accumulator note. [One-accumulator scan](one-accumulator-scan-without-a-clock.md)

## 9. What is not proved

- The proofs of Lemmas 1–2, the reduction in Section 3, the protocol and the equality step are manuscript only. There is no Lean.
- The checks are finite: exhaustive at Q = 4 and 8, sampled up to w = 12, and orbits sampled to w = 64. The protocol checks of `even_multiplier_scan_checks.cpp` use synthetic layouts. The independent run on actual equality-file words reaches two passes in only 5 of its 48 runs, at most 3, and at w = 24 rather than the standard 32; multi-pass accounting rests on the exhaustive Q = 8 scan (up to 20 passes) and the synthetic `proto` run.
- h_D = O_D(1) is taken from the communication note. The generated files confirm it at N = 2^17 … 2^22 bits only.
- The variant with polynomially bounded identifiers rests on the communication note's h ≤ N^{D/(8t)+o(1)}, which was not re-checked; the variant itself is unchecked.
- No member of A(a,d) is shown to decide SAT. For odd literal d under the conditions of the [odd-stride note](even-multiplier-scans-with-odd-strides-fail-at-every-speed.md) none does, so the bound is vacuous there. In the other cases it may be vacuous.
- No class of the six-instruction map changes status.
- Length-dependent strides are open. Odd multipliers other than ±1, a = +1 with lookbehind (order LD ST MU AD), and translations that are not lookahead-aligned with d have clock-only bounds in the [odd-multiplier note](odd-multiplier-stores-in-a-six-slot-scan.md).
- After the shift g(z ± d) of the δ = ±1 orders:
  - negation, complement, c−p and left shifts keep small orbits (proved);
  - masks and rotations do not;
  - right shifts and squaring are small at w ≤ 9 but unproved.
- The bound is a conditional statement about correct members. With the constants above it is positive only from about N = 2^34 bits.
- Nothing here bears on the linear, quadratic or cubic targets for the unrestricted RAM: tests (a) and (b) both come out "yes".

## Reproducing the checks

Run from `audits/`. Nothing is written outside a temporary directory.

```
c++ -O2 -std=c++17 even_multiplier_scan_checks.cpp -o /tmp/even-multiplier-scan-checks
for mode in inv4 inv8 walk orbit scan8 proto eqsearch; do /tmp/even-multiplier-scan-checks $mode; done
python3 even_multiplier_scan_independent_check.py
python3 equality_file_generator.py
```

The seven modes of the first program take under 10 seconds each (scan8 takes about 9). The second script compiles the review's checks, `even_multiplier_scan_independent_checks.cpp` and `shifted_payload_orbits.cpp`, into a temporary directory. It builds the equality file with the generator and runs every check, in about 16 seconds. The generator takes about a second; it finds CaDiCaL via `$CADICAL`, PATH or a Lean toolchain. [Checks](../audits/even_multiplier_scan_checks.cpp) · [Independent checks](../audits/even_multiplier_scan_independent_check.py) · [Independent checks (C++)](../audits/even_multiplier_scan_independent_checks.cpp) · [Shifted maps](../audits/shifted_payload_orbits.cpp) · [Equality-file generator](../audits/equality_file_generator.py)
