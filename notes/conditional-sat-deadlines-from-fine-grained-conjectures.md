# Conditionally on the Triangle, 3SUM and k-SUM conjectures, SAT misses the linear, quadratic and cubic deadlines

Conditional on the Triangle and 3SUM conjectures of Abboud and Vassilevska Williams (AVW14; word RAM, O(log n)-bit words), the k-SUM conjecture read on the same machine (its sources state no model), and the model-matching hypothesis (MM) of Section 2, deterministic SAT on proper DIMACS 3-CNF on the log-word RAM is, for every ε > 0, not in O(N^{1+δ−ε}) time (Triangle), not in O(N^{2−ε}) (3SUM), and not in O(N^{3−ε}) (5-SUM). (MM) holds by inspection for the journal's RAM as defined in the five-instruction loop note. Nothing unconditional is gained: the missing step is the conjectures themselves, and the unconditional linear, quadratic and cubic questions remain open. [RAM definition](five-instruction-loops-on-dimacs-sat.md)

Read against the strict deadlines (no O(N), no O(N^2), no O(N^3)), the conditional exclusions are:
- Triangle and 3SUM each exclude the **linear** deadline.
- 5-SUM excludes the **quadratic** deadline.
- 7-SUM excludes the **cubic** deadline.

N^{2-o(1)} does **not** exclude O(N^2), and N^{3-o(1)} does not exclude O(N^3).

## 1. Statements

**Lemma (transfer).** Let P be a deterministic program for the journal's log-word RAM that decides proper DIMACS 3-SAT within T(N) steps on every N-bit input, with T nondecreasing and T(N) >= N. Then on the standard word RAM with O(log n)-bit words, for every n:

- (i) **Triangle.** Triangle detection in simple m-edge graphs takes O(m log^2 m) + O(T(B_t(m))) steps.
- (ii) **3SUM.** AVW14-form 3SUM on n integers takes O(n log^2 n) + O(T(B_3(n))) steps.
- (iii) **k-SUM.** For each fixed k, normalized ALW14-form k-SUM (range [−n^{2k}, n^{2k}], target 0; see Section 2) takes O_k(n log^2 n) + O(T(B_k(n))) steps.

Here B_x = 8[(8+d_V+d_C) + C(3d_V+8)], with V and C the closed forms of Section 3.1 for that family (for Triangle with n = 2m, the worst case under n ≤ 2m) and d_X the number of decimal digits of X. B_x bounds the exact formula length N(I). Since B_x(n) = Θ(n log^2 n), there is a constant c_x with B_x(n) ≤ c_x n log^2 n for all n ≥ 2. The lemma needs only the existence of such a constant. The numerals in Section 3.2 are finite checks of it, not part of the lemma.

The lemma assumes the model-matching hypothesis (MM) of Section 2, which holds for the journal's RAM definition.

**Corollary (ladder).** For every ε > 0:
- Conjecture 4 of AVW14, with its constant δ, implies T is not O(N^{1+δ-ε}).
- AVW14 Conjecture 1 (3SUM) implies T is not O(N^{2-ε}).
- The k-SUM conjecture at k implies T is not O(N^{⌈k/2⌉-ε}).

Here T(N) ranges over the running times of all deterministic SAT programs as in the lemma.

## 2. The conjectures as used (exact statements, sources, machine model)

**Sources.**
- [AVW14] A. Abboud and V. Vassilevska Williams, *Popular conjectures imply strong lower bounds for dynamic problems*, FOCS 2014, https://arxiv.org/abs/1402.0054v1. **Read in part:** §1 conjecture list (pp. 1-3) and §4 discussion (pp. 16-18), extracted from the arXiv PDF.
- [AL13] A. Abboud and K. Lewi, *Exact weight subgraphs and the k-Sum Conjecture*, ICALP 2013, https://arxiv.org/abs/1304.7558v1. **Read in part:** pp. 1-7 and Appendix A.
- [ALW14] A. Abboud, K. Lewi and R. Williams, *Losing weight by gaining edges*, ESA 2014, https://arxiv.org/abs/1311.3054v2. **Read in part:** pp. 1-3.
- [Pat10] M. Pătraşcu, *Towards polynomial lower bounds for dynamic problems*, STOC 2010. **Not accessed**; it is cited by AVW14 and ALW14 as the origin of the word-RAM 3SUM conjecture.
- [VW-W] Vassilevska Williams and Williams, *Subcubic equivalences between path, matrix and triangle problems*, Theorem 4.2. **Not accessed**; used only as quoted in the journal's APSP note (Section 5).

**Triangle (AVW14, Conjecture 4, verbatim from the PDF text).** "There is a constant δ > 0, such that in the Word RAM model with words of O(log n) bits, any algorithm requires m^{1+δ−o(1)} time in expectation to detect whether an m edge graph contains a triangle."
- Model: word RAM, O(log n)-bit words, expected time of randomized algorithms.
- AVW14 also remarks (p. 16, not a numbered conjecture): "one may even conjecture that O(m^{4/3−ε}) time is not possible". The same transfer turns that into N^{4/3-o(1)}.
- The O(m^{2ω/(ω+1)}) algorithm of Alon, Yuster and Zwick (AVW14's [6]; AVW14 p. 16 state it as O(min{m^{1.41}, n^ω})) caps δ at 2ω/(ω+1) − 1 < 0.41.

**3SUM (AVW14, Conjecture 1, verbatim).** "In the Word RAM model with words of O(log n) bits, any algorithm requires n^{2−o(1)} time in expectation to determine whether a set S ⊂ {−n^3, . . . , n^3} of |S| = n integers contains three distinct elements a, b, c ∈ S with a + b = c."
- Model: word RAM, O(log n)-bit words, expected time.
- AVW14 attribute the conjecture to [72] = Pat10 and to [42] = Gajentaan–Overmars.

**APSP (AVW14, Conjecture 2, verbatim).** "There is a constant c, such that in the Word RAM model with words of O(log n) bits, any algorithm requires n^{3−o(1)} time in expectation to compute the distances between every pair of vertices in an n node graph with edge weights in {1, . . . , n^c}."
- Model: word RAM, O(log n)-bit words, expected time.
- Use: APSP reduces to ⌈log2 n⌉ distance products with entries at most n^{c+1}. VW-W Theorem 4.2 (not re-read) needs T(n)/n nondecreasing, which holds for T = n^{2a} with a ≥ 1/2.

**k-SUM (AL13, Conjecture 1, verbatim).** "There does not exist a k ≥ 2, an ε > 0, and a randomized algorithm that succeeds (with high probability) in solving k-SUM in time O(n^{⌈k/2⌉−ε})."
- AL13's Definition 2 is the k-list form: k lists L_1..L_k of n integers; is there one number from each list with sum 0?
- AL13 measure size as n = (number of integers) × log M for integers in [−M, M] (§2.1 and Appendix A). For M = n^{O(k)} this changes ε only.
- **No machine model is stated** in AL13; a search of the extracted text for "RAM" or "word" finds no model statement.

**k-SUM (ALW14).**
- Definition 1.1: the (k, M)-SUM problem is, given n integers x_1, ..., x_n ∈ [0, M] and a target t ∈ [0, M], to decide whether some S ⊆ [n] with |S| = k has Σ_{i∈S} x_i = t. Footnote 1: without loss of generality the range can be [−M, M] and the target zero. They set k-SUM ≜ (k, n^{2k})-SUM.
- They write: "The k-SUM conjecture [Pat10, AL13] states that k-SUM requires n^{⌈k/2⌉−o(1)} time."
- **No machine model is stated.**

**What this note uses.**
- (a) *Deterministic* algorithms only. This is weaker than the sources' randomized or expected-time forms, which imply it.
- (b) For k-SUM, a model and a problem form that the sources leave open.
  - The model is the word RAM with O(log n)-bit words. This reading is this note's: "on the word RAM with O(log n)-bit words, no deterministic algorithm decides (k, n^{2k})-SUM in O(n^{⌈k/2⌉−ε}) time."
  - The form is ALW14's normalized (k, n^{2k})-SUM with range [−M, M] and target 0 (their footnote 1). ALW14's Definition 1.1 itself has x_i ∈ [0, M] and t ∈ [0, M]. The map x ↦ kx − t reduces it to the normalized form with M' = kM, and the builder absorbs that (L grows by O(log k)).
  - AL13's form (k lists, any M, size = number of integers × log M) is reached in either of two ways: through ALW14's randomized Proposition 1.1 (range reduction), or directly by the k-list builder. The builder accepts any M and gives N = O_k(s log s) for AL13's size s.
  - AL13's conjecture is one statement over all k; only the instances k = 5 and k = 7 are used. The script encodes both the ALW14 one-list form and the AL13 k-list form.

**Model matching.** Two machines are involved.
- The journal's machine is the separate-operation RAM fixed in the first paragraph of the five-instruction loop note. Many notes link to it, and a five-instruction note refers to it as "the model definition". Its terms are: [RAM definition](five-instruction-loops-on-dimacs-sat.md)
  - little-endian words of w = 16⌈log2(N+2)/16⌉ bits;
  - input in consecutive words from address 0, zero elsewhere, and registers zero except an optional length register holding N;
  - modular add, subtract and multiply, bitwise Boolean operations, shifts, rotations, moves and word comparisons, plus binary branches on comparisons;
  - LOAD and STORE with a register or immediate address (so indirect access), with all 2^w words writable.
- The conjectures' machine is the standard word RAM with c'·log n-bit words, for any fixed c'. The conjecture quantifies over every such c'.

The simulation works as follows:
- **Words.** On the formula F(I) we have N <= c n log^2 n, so w = Θ(log N) = Θ(log n). Choose c' with 2^{c' log n} >= N^{c} for the journal's address range. Then each journal word and address fits in O(1) standard words.
- **Instructions.** Each journal instruction is simulated in O(1) standard operations: multiword add, multiply and shift on O(1)-word operands.
- **Input.** The reduction writes F(I) in the journal's layout (packed little-endian w-bit words from address 0, with the optional length register set to N) in O(N) steps.
- **Total.** O(N + T(N)).

**Hypothesis (MM).** Every instruction of the journal's RAM is computable by O(1) standard word-RAM operations on O(1) words. The lemma fails without it.

For the RAM of the five-instruction loop note, (MM) holds by inspection:
- **Words.** w < log2(N+2) + 16, and N ≤ c n log^2 n, so w ≤ 3 log2 n for large n. A journal word therefore fits in one standard word of 3 log2 n bits.
- **Arithmetic.** Modular add, subtract and multiply mod 2^w are the standard operation followed by a mask, since the low w bits of a product are determined by its low w' ≥ w bits.
- **Rotations.** Each is two shifts, an OR and a mask.
- **Everything else.** Moves, comparisons, branches, bitwise operations, LOAD and STORE are single operations.
- **Addresses.** All 2^w < 2^16(N+2) addresses fit in one word.

(MM) remains an assumption only for broader instruction sets.

## 3. The reductions and their lengths

### 3.1 The reductions (one primitive)

Every reduction uses the same pieces. Writing (S_r ⇒ ...) for a clause:

- **Lookup by witness index.** A public table has R records of W bits, and a lookup binds variables Y_1..Y_W. It uses one-hot selector variables s_1..s_R and the R·W binary clauses (¬s_r ∨ ±Y_t), with the sign fixed by bit t of record r.
  - This is the multiplexer. Its cost is exactly one clause per table bit, and it needs no decoder.
  - **No sorting network is needed**, because the table is read-only and public: the data bits are clause signs. The generic route compiles a RAM verifier with private written memory and checks memory consistency with a sorting network (O(t log t) comparators with AKS, O(t log^2 t) with Batcher). That route would give the same exponents with more log factors.
- **At least one, and index order.** A prefix chain uses variables p_1..p_R with (¬p_1 ∨ s_1) and (¬p_r ∨ p_{r−1} ∨ s_r). The unit (p_R) forces some selector true.
  - The order constraint "index of lookup j+1 > index of lookup j" is the clause set (¬s'_1) and (¬s'_b ∨ p_{b−1}) for b >= 2.
  - In any model these give indices i_1 < ... < i_k with every s^j_{i_j} true, by walking the chains backwards.
- **Sum test.** A ripple-carry adder works mod 2^L, LSB first, with carry-in a false anchor. Per bit it uses u = x⊕y and s = u⊕c (4 clauses each) and carry = MAJ(x,y,c) (6 clauses): 3 variables and 14 clauses per bit. The test then requires all bits of the final sum to be 0.
  - L = bitlength(max |sum|), so 2^L exceeds every attainable |sum|, and "≡ 0 mod 2^L" is the same as "= 0".
- **Properness.** As in the journal's proper DIMACS: three anchors F1, F2, F3 are pinned false by the 7 proper clauses on them. Short clauses are padded with positive anchor literals. Every clause has exactly 3 distinct variables, every name 1..V occurs, there are no duplicate clauses, and the header is exact.

**Triangle** (AVW14 Conjecture 4; simple graph). Vertices are relabelled to [0, n) with n ≤ 2m. That takes O(m) time by radix sort when labels are polynomial in m, and otherwise O(m log log m) by deterministic integer sorting, still within the lemma's O(m log^2 m).
- Store each edge as (u, v) with u < v, and put ℓ = bitlength(n−1).
- There are three lookups into the same m-record edge table, binding (A,B), (B,C) and (A,C), where A, B, C are ℓ-bit vertex labels.
- Every model has A < B < C with all three edges present, so it is a triangle. Conversely, a triangle a < b < c gives a model.
- V = 6m + 3ℓ + 3 and C = 6mℓ + 3m + 10.

**3SUM** (AVW14 Conjecture 1, exact form).
- L = bitlength(3n^3). There are three lookups: Y1 = a and Y2 = b from the table x_r, and Y3 = −c from the table (−x_r mod 2^L). Negation is free because the table is public.
- Constraints: index(a) < index(b), which loses nothing since a + b = b + a; index(c) differs from both, using clauses (¬s1_r ∨ ¬s3_r) and (¬s2_r ∨ ¬s3_r); and Y1 + Y2 + Y3 ≡ 0.
- S is a set, so each satisfied lookup has exactly one true selector, and distinct indices mean distinct elements.
- V = 6n + 9L + 3 and C = 3nL + 6n + 29L + 9.

**k-SUM** (ALW14 Definition 1.1, target 0, range [−M, M], M = n^{2k}).
- L = bitlength(kM). There are k lookups into the same table with strictly increasing indices, followed by k−1 adders and the zero test.
- V = 2kn + (4k−3)L + 3 and C = knL + (2k−1)n + (14k−13)L + 8.
- **k lists** (AL13 Definition 2, n entries per list, any range M): k lookups into k tables, at least one per list, then the adders, with L = bitlength(kM). No order constraint is needed.
  - V = 2kn + (4k−3)L + 3 and C = knL + kn + k + (14k−13)L + 7.
  - The script checks this closed form on every k-list instance of Section 3.4.

### 3.2 Encoded length (bits, 8 per ASCII byte)

Each clause line is "a b c 0\n", so the length is exactly

  N = 8·(len("p cnf V C\n") + Σ_clauses (len(a)+len(b)+len(c)) + 5C)
    <= 8·[(8 + d_V + d_C) + C·(3 d_V + 8)],

where d_X is the number of decimal digits of X.

**Leading terms.** With L = Θ(log n) and d_V = log10(V) + O(1), N = Θ(n log^2 n) for each family. In a lookup clause only the selector name is long; the Y and anchor names are O(log log n) digits. So the leading terms are:
- **3SUM:** N ~ 8·(9 n log2 n)·log10 n = (72/log2 10) n log2^2 n ≈ 21.7 n log2^2 n.
- **k-SUM (M = n^{2k}):** N ~ (16k^2/log2 10) n log2^2 n. This is about 120 n log2^2 n for k = 5 and 236 n log2^2 n for k = 7.
- **Triangle (n <= 2m):** N ~ 14.5 m log2^2 m.

**Measured.** Exact N against the closed forms for V and C, from `python3 fine_grained_sat_ladder_reductions.py lengths` (about 20 s):

```
family     size   V          C           N(bits)      N/(n log2^2 n)  bound_ok
tri    m=256     1566       14602       1451216      88.58            True
tri    m=1024    6180       70666       7456208      72.81            True
tri    m=4096    24618      331786      36363000     61.65            True
tri    m=16384   98352      1523722     175018328    54.50            True
tri    m=65536   393270     6881290     829294192    49.43            True
sum3   n=256     1773       22267       2266968      138.36            True  (L=26)
sum3   n=1024    6435       105385      11273520     110.09            True  (L=32)
sum3   n=4096    24921      492631      55041048     93.32            True  (L=38)
sum3   n=16384   98703      2262277     266256144    82.91            True  (L=44)
5sum   n=256     3974       113283      12691648     774.64            True  (L=83)
5sum   n=1024    11994      542455      62103872     606.48            True  (L=103)
5sum   n=4096    43054      2562923     306057992    518.90            True  (L=123)
7sum   n=256     6462       219191      25342480     1546.78            True  (L=115)
7sum   n=1024    17914      1050499     121938328    1190.80            True  (L=143)
7sum   n=4096    61622      4970703     609573440    1033.48            True  (L=171)
```

The ratios fall toward the leading constants.

**Explicit constants.** The upper bound above, evaluated from the closed forms at n = 2^e and 2^e ± 1 for 4 <= e <= 40, gives N/(n log2^2 n) at most 323 for triangle (with n = 2m), 675 for 3SUM, 3379 for 5-SUM and 7844 for 7-SUM. The same command with the mode `constants` also runs a dense check: over every n in [15, 2^18] the maxima are 322.6 (at n = 17) and 674.7, 3378.6 and 7843.5 (at n = 15).

```
bound(N)/(n log2^2 n) from closed forms; max over n = 2^e, 2^e+-1, 4 <= e <= 40
tri(n=2m) max=322.6 2^10:110.4 2^20:74.8 2^30:63.8 2^40:58.5
sum3 max=674.7 2^10:164.7 2^20:111.4 2^30:95.3 2^40:87.4
5sum max=3378.6 2^10:974.7 2^20:655.4 2^30:555.4 2^40:506.0
7sum max=7843.5 2^10:1887.6 2^20:1276.2 2^30:1083.9 2^40:988.5
dense check: max ratio over every n in [15, 2^18], and the ratio at n = 2
tri(n=2m) dense max=322.6 at n=17  n=2: 2288
sum3 dense max=674.7 at n=15  n=2: 11028
5sum dense max=3378.6 at n=15  n=2: 61052
7sum dense max=7843.5 at n=15  n=2: 116816
leading constants of the actual length N: sum3 72/log2(10)=21.67  ksum 16k^2/log2(10): k=5 120.4 k=7 236.0  tri 48/log2(10)=14.45
```

So these numerals bound the ratio on all of [15, 2^18] and at the grid points up to 2^40; an independent dense check over every n in [15, 2^22] also stays within them. They fail below n = 15: at n = 2 the ratios are 2288, 11028, 61052 and 116816. The lemma needs only the existence of a constant, which the Θ(n log^2 n) closed forms give.

**One log factor can be removed.** The journal's bit-once mask bank puts each public table bit once into a low digit bit. It should apply to these public-table lookups and give N = Θ(n log n). It is not implemented or checked here; with several lookups into one table, each data bit appears once per lookup. Only log factors change. [Bit-once mask bank](compact-four-list-orthogonality-in-dimacs.md)

**Reduction time on the log-word RAM: O(N) steps.**
- Precompute the decimal strings of 1..V in O(V d_V) steps.
- Compute each table record x mod 2^L and −x mod 2^L in O(1) word operations, since L = O(log n) is O(1) words. Extract bit t by a shift and a mask.
- Emit each character into the packed output in O(1).
- Total O(C + V d_V + N/8) = O(n log^2 n).

### 3.3 Exponents, with log factors

With T(N) = O(N^a), the lemma gives O(n^a log^{2a} n) for the source problem. The table therefore reads:

| Hypothesis (form used) | SAT bound for every ε > 0 | Strict deadline excluded | Family solver known (test a) |
|---|---|---|---|
| Triangle, AVW14 Conj. 4 (δ) | not O(N^{1+δ−ε}) | O(N), also N polylog N and N^{1+o(1)} | m^{2ω/(ω+1)} < m^{1.41}, so δ < 0.41 |
| Triangle, m^{4/3} form (AVW14 remark) | not O(N^{4/3−ε}) | O(N) | as above |
| APSP, AVW14 Conj. 2, via journal note + VW-W Thm 4.2 | not O(N^{3/2−ε}) | O(N) | faster than n^3/log^c n for every c (Williams, as summarized in AVW14 p. 16) |
| 3SUM, AVW14 Conj. 1 | not O(N^{2−ε}) | O(N); **not** O(N^2) | n^2/polylog n |
| 5-SUM, (5, n^{10})-SUM, word RAM (this note's reading) | not O(N^{3−ε}) | **O(N^2)** | O(n^3) meet in the middle |
| 7-SUM, (7, n^{14})-SUM, word RAM (this note's reading) | not O(N^{4−ε}) | **O(N^3)** | O(n^4) |
| k-SUM for all k (AL13 Conj. 1 in full) | not O(N^c) for any c | every polynomial, so P ≠ NP | n^{⌈k/2⌉} |

**APSP row (derived here, not script-tested).** The journal's APSP note says only that the negative-triangle formula has Õ(n^2) bits. The rest of this construction is new here: three lookups into the n^2-entry weight table followed by a comparator, giving N = Θ(n^2 log^2 n). With T(N) = O(N^a) this gives negative triangle in Õ(n^{2a}). The quoted VW-W Theorem 4.2 then gives distance product in O(n^2 T_NT(n^{1/3}) log W) = Õ(n^{2+2a/3}). That is truly subcubic exactly when a < 3/2. The journal note states only the a = 1 case (n^{8/3}). [APSP from a SAT trace](matrix-products-from-a-sat-trace.md)

**Last row.** If P = NP, SAT has an N^c-time RAM algorithm for some fixed c, and then (2c+1)-SUM is in Õ(n)^c. So AL13's conjecture over all k implies P ≠ NP. No single rung (Triangle, 3SUM, APSP, or one fixed k) is known to imply P ≠ NP. No priority is claimed for this observation or for any of the reductions; the reductions are standard quasi-linear Cook–Levin compilations specialized to public tables.

**Log factors do not help beyond the rungs.** An O(N^2) SAT solver gives 3SUM in O(n^2 log^4 n), which contradicts nothing, since 3SUM is in O(n^2). Strict exclusion of O(N^2) needs exponent above 2 (5-SUM). Strict exclusion of O(N^3) needs exponent above 3 (7-SUM). 5-SUM gives only N^{3−o(1)}.

### 3.4 Finite check against brute force with CaDiCaL

`python3 fine_grained_sat_ladder_reductions.py check` (the default mode; about 13 s) prints:

```
family            instances  satisfiable  closed-form(V,C) matches
tri                     326          149          326
sum3                    508          207          508
ksum k=3                616          292          616
ksum k=4                471          194          471
ksum k=5                453          156          453
ksum k=7                168           37          168
klist k=3               150          128          150
klist k=5               100           88          100
total instances 2792 -- all agree with brute force; every file proper; models decode to valid witnesses
```

What each instance checks:
- The brute force is written from the problem definitions, not from the formulas. Triangle: all a < b < c. 3SUM: all ordered triples of distinct indices. k-SUM: all k-subsets of indices. k lists: the full product.
- Every SAT model is decoded back to indices and verified as a genuine witness: a triangle with A < B < C; distinct i < j and k with S_i + S_j = S_k; strictly increasing k indices summing to 0.
- Every file passes the properness check (exact header; exactly 3 distinct variables per clause; canonical decimal; every name 1..V occurs; no duplicate clause), and its N matches the byte count.

The instance mix:
- Random instances at the conjecture's range, which are almost all UNSAT.
- Small-value instances with many solutions and repeats.
- Planted solutions.
- Traps:
  - 0 in the set, e.g. {0, 5, 7}, where a + 0 = a must not count.
  - a + a = c with reuse only, e.g. {3, 6, 1}.
  - k-SUM solutions that exist only with a reused index.
  - Duplicate values that form a genuine solution.
  - All values at +M or −M, testing wraparound.

One failure mode shows why the range matters. A k-list test that drew values outside [−M, M] at n = 1 made the 2-bit adder accept 3 + 3 − 2 ≡ 0 (mod 4). The builder asserts the range; the conjecture's range is what makes L = bitlength(kM) sound.

## 4. The three standard tests

**(a) Fast globally correct solver on the hard family?**
- Each family has a recognizer: regenerate F(I) from the decoded instance and compare, in O(N). Run the best known algorithm for the source problem, and fall back to a complete SAT solver on any other file.
- This gives globally correct solvers running in about N^{1.41} (Triangle), N^2/polylog (3SUM) and N^{⌈k/2⌉} (k-SUM) on the families.
- No faster solver is known. The claimed bounds sit at the known exponents up to N^{o(1)}, and the hardness is exactly as strong as the conjectures.
- The m^{1.41} triangle algorithm limits δ to below 0.41.

**(b) Same bound for an easy language (2-SAT)?** No, and vacuously so.
- The argument is a reduction only. The encoding needs 3-clauses for the adders and prefix chains.
- A near-linear-size reduction of 3SUM, Triangle or k-SUM to 2-SAT, which is linear-time, would itself refute the conjecture.
- The conjecture does all the work.

**(c) The relativized-clock oracle (p = 1 world).** [Relativized clock](relativized-clock.md)
- In that world plain SAT has an O(n) oracle algorithm. The reductions do not use the oracle, so Triangle, 3SUM and every k-SUM have Õ(n)-time oracle algorithms there. All the relativized hypotheses are false in that world.
- The implication itself relativizes and survives.
- It gives no route around the relativization barrier: any proof of a rung would have to be non-relativizing (it must use that one instruction reads O(w) bits), just as a direct SAT proof would.

## 5. Overlap with the journal

- The APSP case is already in the journal (24 November): near-linear SAT plus VW-W Theorem 4.2 gives distance product in Õ(n^{8/3}). The general exponent 3/2 in Section 3.3 is the same chain with T(N) = N^a. [APSP from a SAT trace](matrix-products-from-a-sat-trace.md)
- The four-list orthogonality note already has a SETH-conditional cubic rung. [Four-list orthogonality](compact-four-list-orthogonality-in-dimacs.md)
  - SETH implies ETH, which implies P ≠ NP. So SETH already excludes every polynomial deadline. Its consequences for the SAT deadlines are stronger than those of any single rung here.
  - But no implication between SETH and the Triangle, 3SUM or APSP conjectures is known: AVW14 (p. 2) list SETH among five conjectures, any subset of which could fail while the rest hold.
  - That note also supplies the bit-once lookup that would shave one log factor here.
- **Li–Tell.** The results index already records a conditional exclusion of the linear deadline from the Li–Tell range-avoidance premise, in the entry "Conditional unrestricted RAM bound from uniform range avoidance". [Uniform avoidance proof](near-linear-sat-and-uniform-low-space-range-avoidance.md)
  - There, the premise of Li and Tell's revised Theorem 1.3 implies that, for some unspecified η > 0, explicit 3-SAT on the log-word RAM with unrestricted workspace is not in O(N^{1+η}).
  - The rungs here give explicit exponents (1+δ, 4/3, 3/2, 2, 3, 4) from standard fine-grained hypotheses.
- The network-ceiling note proves that the O(N^k) deadlines for k = 1, 2, 3 are the same for unbounded-width DIMACS CNF and proper 3-SAT. The ladder therefore applies to both. [Network ceiling](exact-network-ceiling-for-ordinary-sat.md)
- The address-translated histories note mentions 3SUM, as a list-sum chronology, but not as a SAT conditional. [Address-translated histories](sorting-address-translated-ram-histories.md)
- **Triangle overlap.** The section "Freeing the selectors gives actual triangle detection" of the three-lookup note already encodes **dense** tripartite triangle detection as three table reads in a Θ(d^2)-bit DIMACS file. Its model count equals the number of tripartite triangles. It also gives an O(N) solver near the all-zero file, and studies arithmetic size (exponent ω). [Three lookups](three-lookups-and-the-multilinear-sat-verdict.md)
  - The private-table note has the same three-table cycle. [Private table trees](private-table-trees-and-a-small-cycle-core.md)
  - Neither note states a conditional time bound or uses the sparse m-edge form of AVW14 Conjecture 4.
  - A grep for "triangle detection/conjecture", "negative triangle" and "triangle-free" over the notes found nothing else relevant. The other hits are parity, coloring and Turán topics.

New here relative to the journal:
- Exact conjecture statements with their models (Triangle, 3SUM, APSP; k-SUM with the sources' lack of a model noted).
- Explicit proper-3-CNF reductions for Triangle, 3SUM, k-SUM and k lists, with closed-form V and C, an exact length formula and O(N) generation.
- The deadline-to-rung table.
  - Among k-SUM rungs, the smallest k that excludes O(N^2) is 5, and the smallest that excludes O(N^3) is 7.
  - These conjectures ignore polylog factors and every reduction has N ≥ n. So a rung with conjectured exponent e excludes O(N^a) only when e > a, whatever the encoding.
  - SETH, through the four-list note, excludes every polynomial deadline.
- A 2792-instance check against brute force.

## 6. Exact obstruction and next step

**Obstruction.** The chain is "rung conjecture ⇒ SAT deadline". Its premises are open, and they fail relative to the p = 1 oracle. Proving any rung unconditionally on the word RAM is at least as hard as the corresponding SAT deadline, since it implies it. So the ladder relocates the problem and does not shorten it. Among the rungs that exclude the linear deadline, the Triangle rung has the smallest exponent (1+δ). AVW14 (p. 2) say that, as far as they know, any subset of their five conjectures (3SUM, APSP, SETH, Triangle, BMM) could be false while the rest hold. So no implication is known among the Triangle, 3SUM and APSP rungs.

Within the table, some rungs are trivially comparable:
- The m^{4/3} form implies Conjecture 4 with δ = 1/3.
- The all-k k-SUM conjecture implies each fixed-k rung.
- AVW14 (p. 16) also record that triangle detection reduces to 3SUM on O(m) numbers ([57], Jafargholi–Viola, not accessed). So Conjecture 4 implies that 3SUM needs n^{1+δ−o(1)}. That weak-3SUM hypothesis follows from both the Triangle rung and the 3SUM rung, and through a 3SUM reduction it alone excludes the linear deadline. Which 3SUM form [57] produces was not checked; the k-list builder accepts any polynomial range.

**Next lemma, if this line continues.** Under the usual NTIME/DTIME reading, each rung separates linear nondeterministic from deterministic RAM time directly, with no SAT encoding: Triangle, 3SUM and k-SUM are in NTIME_RAM[O(N)] on their own encodings by guessing O(1) indices. For example, the 3SUM conjecture implies NTIME_RAM[N] ⊄ DTIME_RAM[N^{2−ε}].

This was not checked against the journal's own milestone definition. The native unary-clock note is phrased through unary-clock RAM acceptance U_RAM with its own encoding, and the transfer to that encoding is not verified here. [Native unary clock](native-unary-clock-band.md)
- A useful next statement is the converse direction for the journal's milestone: does NTIME_RAM[n] ≠ DTIME_RAM[n], or a polynomial version of it, imply any rung? Probably not, since the rungs are statements about specific problems.
- Separately, the bit-once lookup gives N = Θ(n log n). That matters only for polylog-sensitive transfers (for example from n^2/polylog 3SUM bounds), and those are not conjectures.

## 7. What is not proved

- No unconditional lower bound of any kind. All SAT bounds above are conditional on the stated conjectures.
- The conjectures themselves. The word-RAM reading of k-SUM is this note's; AL13 and ALW14 state no model.
- Hypothesis (MM) beyond the journal's stated RAM. For the separate-operation RAM of the five-instruction loop note it holds by inspection (Section 2). If the milestone model allows instructions beyond that list, (MM) needs a separate check.
- That the rungs give the journal's native milestone in the encoding of the native unary-clock note. Only the usual NTIME/DTIME reading is claimed.
- That N^{2−o(1)} or N^{3−o(1)} excludes O(N^2) or O(N^3). They do not; only the 5-SUM and 7-SUM rungs exclude those deadlines.
- The APSP exponent 3/2 relies on VW-W Theorem 4.2 as quoted in the journal (not re-read here). The negative-triangle encoding was not script-tested.
- **What is checked only at finite size:**
  - the closed forms for V and C (every generated instance);
  - correctness against brute force (2792 instances, n <= 9, m <= 28);
  - the explicit numerals 323, 675, 3379 and 7844. These are checked at grid points up to 2^40 and at every n in [15, 2^18]; they fail below n = 15. The lemma uses only the existence of constants.
- The soundness and completeness of the encodings and the O(N) generation time are manuscript proofs (Sections 3.1 and 3.2).
- No priority is claimed for any reduction or for the observation that all-k k-SUM implies P ≠ NP.

## Reproducing the checks

Run from `audits/`; CaDiCaL must be on PATH or in a Lean toolchain under `~/.elan/toolchains`.

```
python3 fine_grained_sat_ladder_reductions.py check
python3 fine_grained_sat_ladder_reductions.py lengths
python3 fine_grained_sat_ladder_reductions.py constants
```

[fine_grained_sat_ladder_reductions.py](../audits/fine_grained_sat_ladder_reductions.py)
