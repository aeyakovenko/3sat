# Six-slot scans that store an odd multiple of the cursor need Ω(N^{3/2}/log²N) steps to answer every equality file correctly

Consider the six-stored-instruction programs of the form x = M[p]; M[x] ← a·p; p += d with two branches, where a is an odd literal with |a| ≥ 3 and d is a fixed nonzero literal, in any of the six data orders. Let N be the bit length and let the word width be w = 16⌈D·log₂(N+2)/16⌉. Every such program that answers every equality file of length N correctly needs Ω_{D,d,a}(N^{D+1/2}/log²N) steps on some satisfiable equality file, and Ω_{D,d,a}(N^{D+1/2}/log^{3/2}N) when a ≤ −3; the second bound also holds for the lookbehind payload (a = 1 in the order LD ST MU AD, which stores the previous cursor). At standard width (D = 1) the first bound is Ω(N^{3/2}/log²N). The key lemma bounds every increasing run of i ↦ a·i + c mod L by (a+1)(⌊log_a(L−1)⌋+1) for a ≥ 3, and by |a|+1, independent of w, for a ≤ −3, so last-writer chains advance O(R) links per pass. With the [even-multiplier note](even-multiplier-stores-in-a-six-slot-scan.md) and the [communication note](communication-bound-for-public-crossed-scans.md), every literal or public-word multiplier with a literal stride, in every data order, now has such a bound. The even-multiplier note's §8 sketched this route; what is new here is the proofs and the checks, including an independent machine simulation during review (11.3 million reads, 0 violations). The bound is clock-only and conditional on correctness, so it may be vacuous; with explicit constants it is positive only from about N = 2^36 bits (a = 3). No class of the six-instruction map changes status, and nothing here concerns the unrestricted RAM; the linear, quadratic and cubic questions remain open. [Ancestry of crossed stores](ancestry-of-crossed-stores.md) · [Six-instruction control classes](six-instruction-control-classes-in-the-five-slot-machine.md)

## The architecture and the setting

**Architecture.** A(a,d) is the architecture of the even-multiplier note: four data instructions on one recurrent cycle, `LD` x ← M[p], `MU` y ← a·p mod Q, `ST` M[x] ← y and `AD` p ← p + d mod Q, in any of the six cyclic orders, and two comparison branches with fixed targets, with Q = 2^w and d a fixed nonzero literal. Here a is an odd literal with |a| ≥ 3, or a = 1 in the order LD ST MU AD (the lookbehind). The note's reduction (its Section 3) applies unchanged. After the public prologue, iteration i ≥ 0
- reads x_i = M[p_i], where p_i = p₀ + i·d mod Q;
- stores f(p_i) at x_i, where f(z) = a(z + δd) mod Q and δ ∈ {−1, 0, 1} is fixed by the data order;
- except that the store of iteration 0 may carry the public value y₀.

**Notation.**
- H′ is the image of memory at the first LD together with y₀, and |H′| ≤ h′.
- C = p₀ + 2^v·Z_Q is the scanned coset, with v = v₂(d) and L = |C| = Q/2^v.
- The index map is ι(p₀ + i·d) = i mod L, so ι(p_i) = i mod L.
- Pass π is the block of iterations [πL, (π+1)L).
- R(a, L) is the largest r with an ascent run x₀ < g(x₀) < … < g^r(x₀) of some g(x) = (a·x + c) mod L on {0, …, L−1}, compared as integers, over all c and x₀.

## 1. Lemma 0 (index form)

If (a−1)p₀ ≢ 0 mod 2^v, then f(C) ∩ C = ∅. Otherwise f(C) ⊆ C, with equality when a is odd, and ι(f(z)) = a·ι(z) + c mod L, with c = ι(f(p₀)).

*Proof.* f(p₀ + i·d) = a·p₀ + aδd + a·i·d, which is ≡ a·p₀ (mod 2^v) because 2^v divides d. This equals p₀ mod 2^v exactly when (a−1)p₀ ≡ 0. In that case f(p₀ + i·d) = f(p₀) + a·i·d, so its index is c + a·i. ∎

The address-level check covers every p₀ ∈ Z_Q and δ ∈ {−1, 0, 1}, the strides d ∈ {±1, ±2, ±3, ±4, 5, ±6, 7, 8, ±12, 16}, w = 3..11 and a ∈ {3, 5, −3, 1}. It compares the coset split, the affine form, and the ascent maximum walked at the address level against the index table; every row has 0 violations:
```
addr: a=3 w=11 cases=98304 coset-kept=76032 max-run=9 viol(coset)=0 viol(affine)=0 viol(run)=0
addr: a=-3 w=11 cases=98304 coset-kept=90624 max-run=4 viol(coset)=0 viol(affine)=0 viol(run)=0
```

## 2. Lemma A (ascent runs)

**Lemma A.** Let L ≥ 2, let a and c be integers, and let g(x) = (a·x + c) mod L on {0, …, L−1}. Every ascent run x₀ < g(x₀) < … < g^r(x₀) satisfies
- r ≤ (a+1)(⌊log_a(L−1)⌋ + 1) if a ≥ 2;
- r ≤ |a| + 1 if a ≤ −2;
- r ≤ ⌊(L−1)/t⌋ if a = 1 and c ≡ t ∈ [1, L−1]. So r ≤ 1 when t ≥ L/2, and the lookbehind has t = L−1.

*Proof.* Put k_t = ⌊(a·x_t + c)/L⌋ and D_t = x_{t+1} − x_t = (a−1)x_t + c − k_t·L. In an ascent run D_t ∈ [1, L−1], and D_{t+1} = a·D_t − (k_{t+1} − k_t)·L. For 0 ≤ x ≤ L−1 the reals (a·x + c)/L lie in an interval of length |a|(L−1)/L < |a|, so k takes at most |a|+1 values.
- **a ≥ 2.** k is nondecreasing in x, so it is nondecreasing along the run. On a maximal block of steps with constant k, D is multiplied by a at each step and stays in [1, L−1], so the block has at most ⌊log_a(L−1)⌋ + 1 steps. There are at most a+1 blocks.
- **a ≤ −2.** k is nonincreasing in x. If k_{t+1} ≥ k_t, then D_{t+1} ≤ a·D_t < 0, which is impossible. So k strictly decreases at every step and r ≤ |a| + 1.
- **a = 1, c = t ∈ [0, L).** D_t = t − k_t·L ≥ 1 forces k_t = 0 and D_t = t. Hence x₀ + r·t ≤ L−1. ∎

**Lower bound.** Let a = 2^j + 1 and L = 2^ℓ with ℓ ≥ 2j, and take c = 0. Then x_t = 2^{ℓ−2j} + t·2^{ℓ−j} for t = 0, …, a−2 is an ascent run: a·x_t = x_t + 2^{ℓ−j} + t·2^ℓ ≡ x_{t+1}, and x_{a−2} < L. So R(a, L) ≥ a − 2, and the factor linear in a cannot be removed; for a fixed literal a it is a constant.

**Chain length per pass.** By Lemmas 0, B and C below, a chain of last-writer links inside one pass has at most 2(R+1) links. With L ≤ 2^w this is at most c_a·w + O_a(1) links, with c_a = 2(a+1)/log₂a for a ≥ 3 (c_3 = 8/log₂3 ≈ 5.05, since R ≤ 4(⌊0.631·w⌋ + 1)), and at most 2(|a|+2), independent of w, for a ≤ −3.

**Exhaustive check.** Every c ∈ [0, L) and every start, with L = 2^ℓ, for a ∈ {3, 5, −3} up to ℓ = 16 and for a ∈ {7, 9, 11, 17, 33, −5, −7, −9, −17} up to ℓ = 13; the bound is never violated. Columns: a | ℓ | L | R | an extremal c, x | proved bound | violations | log_|a| L.
```
runs:   3 | 12 |   4096 |   9 | c=0 x=1 | 32 | 0 | 7.57
runs:   3 | 16 |  65536 |  14 | c=0 x=5 | 44 | 0 | 10.09
runs:   5 | 12 |   4096 |   8 | c=1 x=82 | 36 | 0 | 5.17
runs:   5 | 16 |  65536 |  10 | c=2 x=31 | 42 | 0 | 6.89
runs:  -3 | 12 |   4096 |   4 | c=1025 x=0 | 4 | 0 | 7.57
runs:  -3 | 16 |  65536 |   4 | c=16385 x=0 | 4 | 0 | 10.09
runs:  17 | 13 |   8192 |  15 | c=0 x=32 | 72 | 0 | 3.18
runs:  33 | 13 |   8192 |  31 | c=0 x=8 | 102 | 0 | 2.58
runs:  -7 | 13 |   8192 |   7 | c=0 x=896 | 8 | 0 | 4.63
```
- **a ≤ −3 costs no factor w.** R(−3, 2^ℓ) = 4 for every ℓ from 7 to 16, equal to the bound |a|+1. This is checked at finite size; the bound itself is proved.
- **The lower bound is attained at finite size.** For a = 9, 17, 33, R = a − 2 exactly at every ℓ from j to 13, and the extremal starts x = 32 (a = 17) and x = 8 (a = 33) at ℓ = 13 are those of the construction.
- **a = 3 is above log₃L but far below the bound.** R is 14 against log₃L = 10.09 at ℓ = 16, and the bound is 44. No sharper bound is proved.

For a = 1 the largest run over c ∈ [L/2, L) is 1 at every ℓ ≤ 14, with 0 violations; the run at c = 1 (the lookahead) is L−1. Interleaved chains, increasing sequences s < h < g(s) < g(h) < … that interleave two orbits, have at most 2(R_c+1) elements for every c and ℓ ≤ 10, with 0 violations; for a = 3 at ℓ = 10 the maximum is 14 elements, with R = 8.

During review, R(a, L) was recomputed by forward walking for every L in [2, 200], not only powers of two, for 15 multipliers including the even 2, 4 and −2, with 0 violations; for a = 1, R = ⌊(L−1)/t⌋ holds exactly for every L ≤ 200 and every t. The explicit run of the lower bound holds in all 36 cases j ≤ 6, 2j ≤ ℓ ≤ 12.

## 3. Chains, depth per pass and the dichotomy

**Lemma B (chains).** This is the last-writer device of the [ancestry note](ancestry-of-crossed-stores.md), with pairs e_i = (p_i, x_i) and F(a,b) = (b, S^δ(a)), applied to the payload map f. Let W(i) be the iteration whose store last wrote cell p_i before read i; W(i) = ⊥ if the cell holds its content from the first LD, or was last written by iteration 0 with payload y₀ ≠ f(p₀). The depth K(i) is 0 if W(i) = ⊥, and K(W(i)) + 1 otherwise. Unwind the chain as i_K = i and i_{k−1} = W(i_k), and put s = p_{i₀} and h = x_{i₀} ∈ H′. Then p_{i_{k+1}} = x_{i_k}, and x_{i_k} = f(p_{i_{k−1}}) for k ≥ 1. By induction,

p_{i_{2m}} = f^m(s), p_{i_{2m+1}} = f^m(h), x_{i_{2m}} = f^m(h), x_{i_{2m+1}} = f^{m+1}(s).

So p_i = f(p_{W(W(i))}) and x_i = f(x_{W(W(i))}) whenever K ≥ 2.

**Lemma C (depth per pass).** If read i lies in pass π, then ⌈K(i)/2⌉ ≤ (π+1)(R+1), where R is the maximal ascent run of the index map of Lemma 0. If f(C) ∩ C = ∅, then ⌈K/2⌉ ≤ 1.

*Proof.* The odd links i₁ < i₃ < … have the addresses f^m(h) for m = 0, …, ⌈K/2⌉−1, and all of them lie on C. Inside pass π, ι(p_j) = j − πL increases with j. Consecutive odd links satisfy ι(next) = g(ι(prev)) by Lemma 0, so the odd links inside one pass form an ascent run of g, and there are at most R+1 of them. They lie in passes 0 to π. If f leaves C, then f(h) is never read, so there is at most one odd link. ∎

The same argument applies to the even links (the s-orbit), which gives the 2(R+1) links per pass of Section 2. Compared with the ancestry note, its step "v − u ≥ L+1" (one two-link group per pass) becomes "at most R+1 groups per pass". The lookbehind has R = 1, so at most two odd links per pass; the even-multiplier note's §8 remark (v − u ≡ −1 mod L, hence v − u ≥ L−1) gives the slightly sharper count of about one two-link group per pass. Either suffices here.

**Lemma D (pass-dependent dichotomy).** Let V_M = {f^j(u) : u ∈ H′, 0 ≤ j ≤ M}, so that |V_M| ≤ h′(M+1). For every read i in pass π, with M = (π+1)(R+1), either x_i ∈ V_M or p_i ∈ V_M.

*Proof.* If K = 2m, then x_i = f^m(h) with m ≤ M. If K = 2m+1, then p_i = f^m(h) with m < ⌈K/2⌉ ≤ M. ∎

## 4. Transfer and the theorem

Use the even-multiplier note's protocol (its Section 4) unchanged, with its set U replaced by V = V_{P(R+1)}, where P = ⌈m/L⌉ is the number of passes. Stores whose destination lies in V give at most |V| records per phase. A store whose destination lies outside V follows a read at an address in V (Lemma D), and there are at most P·|V| such reads. So records ≤ (phases + P)·|V|, and

C(P) ≤ 2|d|P(3w+5) + ((2|d|+1)P+1)·h′(P(R+1)+1)·(2w+1) + 2 ≤ 8(|d|+1)·h′·(R+2)·w·P²  for w ≥ 8 and P ≥ 1.

The last inequality reduces to 3w+5 ≤ h′(R+2)(2w−1), which holds for w ≥ 7. A grid of 138,880 cases gives 0 violations, with maximum ratio 0.9586, and a random grid of 300,000 cases (w ≥ 8, R up to 2,000, P up to 10⁶), run during review, gives 0 violations with maximum ratio 0.9634. The review's script also evaluates the inequality at h′ = 1, R = 0, P = 1 and d = 1 for w = 1..9; it fails only at w = 1, outside the range w ≥ 8 used here.

**Theorem.** Fix D ≥ 1 and a nonzero literal d. Let a be an odd literal with |a| ≥ 3 (any of the six data orders), or a = 1 in the order LD ST MU AD. Let N be sufficiently large and byte-aligned, and w = 16⌈D·log₂(N+2)/16⌉. If Π ∈ A(a,d) answers correctly on every equality file of the communication note at length N, then on some satisfiable such file Π runs at least

T ≥ ( √( k / (8(|d|+1)·h′·(R_a+2)·w) ) − 1 ) · (N+2)^D / |d|

steps. Here k = ⌊N/(C_D·log₂²N)⌋ is the number of private bits, h′ = h_D + 2 with h_D the communication note's palette bound, and

R_a = (a+1)(⌊log_a(2^w−1)⌋+1) for a ≥ 3, R_a = |a|+1 for a ≤ −3, and R_a = 1 for the lookbehind.

The equality step is the even-multiplier note's: 2^k distinct prefix-free transcripts force C(P_max) ≥ k, and m ≥ (P_max−1)L+1 with L ≥ (N+2)^D/|d|. Hence T = Ω_{D,d,a}(N^{D+1/2}/log²N) for a ≥ 3, and T = Ω_{D,d,a}(N^{D+1/2}/log^{3/2}N) for a ≤ −3 and for the lookbehind, the shape of the communication note's lookahead bound.

Where the bound becomes positive (d = 1, h′ = 16, C₁ = 32, as in the even-multiplier note); the last line is the a = 3 row at N = 2^80, with w computed in integers as the least multiple of 16 with 2^w ≥ (N+2)^D:
```
a=3: bound first positive at N = 2^35.9 bits (w=48, k=1554669, R<=124, P_max>=1.002)
a=-3: bound first positive at N = 2^30.5 bits (w=32, k=51011, R<=4, P_max>=1.019)
a=lb: bound first positive at N = 2^29.4 bits (w=32, k=25611, R<=1, P_max>=1.021)
   N=2^80: w=96 R<=244 P_max>=988124.57 T>=1.195e+30  T/(N^1.5/log2^2 N)=5.752e-03  T/(N^1.5/log2^1.5 N)=6.431e-04
```
During review the thresholds were recomputed with exact widths, and the bound stays positive at every tenth of an exponent from each threshold to 2^100.

## 5. Every literal multiplier

**Corollary (assembled from three notes; checked case by case during review).** The cases not covered by the Theorem are covered elsewhere:
- even a, and the public words 0, n, w (all even): the even-multiplier note;
- a = −1 (an involution after the shift) and a = 1 with δ = 0 (the identity, orbit 1): the even-multiplier note's generic corollary;
- a = 1 with δ = +1 (payload p_{i+1}): the communication note with r = 1. Its theorem says "correct controller", but its proof (the section "A constant word alphabet for deterministic equality") uses only the equality files and the rectangle argument. Its bit cost O_d((r+1)(P+1)²(h+1)w) is per run, at that run's own P. The 2^k diagonal inputs have distinct prefix-free accepting transcripts, so one of them has length ≥ k. The long run is therefore on a satisfiable file, as in the even-multiplier note's Section 4.

So every member of A(a,d) with a literal or public-word multiplier and a literal stride, in any data order, that answers correctly on every equality file needs Ω_{D,d,a}(N^{D+1/2}/log²N) steps on some satisfiable equality file.

| case | covered by | bound |
|---|---|---|
| even literals and the public words 0, n, w (all even) | the even-multiplier note's theorem | N^{D+1}/log⁴N |
| a = −1, any δ | its generic corollary, β = 2 | N^{D+1}/log³N |
| a = 1, δ = 0 (four orders) | its generic corollary, β = 1 (or the communication note with r = 0) | N^{D+1}/log³N |
| a = 1, δ = +1 (LD AD MU ST) | the communication note, r = 1 | N^{D+1/2}/log^{3/2}N |
| a = 1, δ = −1 (LD ST MU AD) | the Theorem (lookbehind) | N^{D+1/2}/log^{3/2}N |
| odd a with \|a\| ≥ 3 | the Theorem | N^{D+1/2}/log²N (log^{3/2}N for a ≤ −3) |

**Remark (literal translation payloads y ← p + c; manuscript, checked at the index level).** Put e = c + δd and e′ = e/2^v, and let d′ be the odd part of d.
- If 2^v ∤ e, then f leaves C, so ⌈K/2⌉ ≤ 1 and the transfer applies with R = 0.
- Otherwise the index offset t satisfies t·d′ ≡ e′ (mod L). If t < (L−|e′|)/|d′|, then t·d′ = e′ exactly, so e = t·d with t ≥ 0: the communication note's lookahead p_{i+t}. If not, then R ≤ ⌊(L−1)/t⌋ ≤ 2|d′| once L ≥ 2|e′|, and the proof of the Theorem applies verbatim, with R = 2|d′|, to the six-slot scan whose payload instruction is y ← p + c (an architecture outside A(a,d)).

So every literal translation payload is either a lookahead of the communication note or is covered by this proof. The index-level check written during review (w = 3..10, 11 strides, e ∈ [−24, 24]) finds 0 failures of the case split in 4,312 cases:
```
translation remark: cases=4312 leaves-C=1344 lookahead(e=t*d,t>=0)=731 R<=2|d'|=1577 failures=0
```
The machine checks below cover only e = −d, that is c = 0 with δ = −1.

## 6. Machine checks

`odd_multiplier_scan_machine.cpp` reuses the interpreter of the even-multiplier checks. On direct runs and on the two-party protocol it checks (R) the reduction; (S) p_i = f(p_gp) and x_i = f(x_gp), where gp is the writer of the writer; (A) ascent runs ≤ the exact R of that machine; (D) ⌈K/2⌉ ≤ (π+1)(R+1); (V) the dichotomy and |V| ≤ h′(M+1); and simulation exactness, phases, records ≤ (phases+P)|V| and bits ≤ C(P). As a control, the same dichotomy with M/4 in place of M should fail when chains are deep. Results are reported per (a, δ). The modes:
- `small`: exhaustive at Q = 8 over all 7,120 memories with at most two values, all six orders, a ∈ {1, 3, 5, 7}, d = 1..7 and every p₀, with 48 loads; and 200,000 random three-value memories at Q = 16;
- `deep`: w ∈ {12, 14}, d = 1, p₀ = 0, small palette words chosen so that orbits ascend, 8 passes, no exits;
- `proto`: w ∈ {12, 14}, random members over all orders, both branch layouts and any entry, with a ∈ {±3, ±5, ±7, 9, 11} plus the lookbehind member, d ∈ {±1, ±2, ±3, ±4, ±5}, and three layouts (the even-multiplier checks' synthetic equality layout, a random palette, small palette words);
- `eqwords`: the words of an actual equality file built by `equality_file_generator.py` (N = 2^18 bits, w = 24, k = 50, 10,923 words, α = 4409, h = 13), with 19 runs for a ∈ {3, 5, −3, 7} and the lookbehind, up to 2.2 passes.

```
small8: runs=9569280 (>=2 passes: 9569280) steps=2755952640 maxP=24 maxPhases=48 maxR(exact, this machine)=7
small8: violations: reduction=0 structure=0 ascent=0 depth=0 dichotomy=0 |V|>h'(M+1)=0 sim=0 phases=0 records=0 bits=0
small8: max depth K seen=47, max ascent run seen=1, max ceil(K/2)/((pi+1)(R+1))=1.0000, max records/bound=0.6528, max bits/bound=0.8383, max |V_P|/Q=1.0000
small8: control (dichotomy with M/4): failing reads=1520576 in 900024 runs; deltas: -1=1594880 0=6379520 1=1594880
small16: runs=200000 (>=2 passes: 200000) steps=153600000 maxP=64 maxPhases=128 maxR(exact, this machine)=15
small16: violations: reduction=0 structure=0 ascent=0 depth=0 dichotomy=0 |V|>h'(M+1)=0 sim=0 phases=0 records=0 bits=0
small16: control (dichotomy with M/4): failing reads=109723 in 31092 runs; deltas: -1=33374 0=133149 1=33477
deep[a=3,delta=0]: violations: reduction=0 structure=0 ascent=0 depth=0 dichotomy=0 |V|>h'(M+1)=0 sim=0 phases=0 records=0 bits=0
deep[a=3,delta=0]: max depth K seen=30, max ascent run seen=8, max ceil(K/2)/((pi+1)(R+1))=0.9000, max records/bound=0.0381, max bits/bound=0.0480, max |V_P|/Q=0.0398
deep[a=3,delta=0]: control (dichotomy with M/4): failing reads=3140 in 176 runs; deltas: 0=216
deep[a=1,delta=-1]: violations: reduction=0 structure=0 ascent=0 depth=0 dichotomy=0 |V|>h'(M+1)=0 sim=0 phases=0 records=0 bits=0
deep[a=1,delta=-1]: control (dichotomy with M/4): failing reads=1380 in 54 runs; deltas: -1=54
proto0: runs=1800 (>=2 passes: 870) steps=132777048 maxP=32 maxPhases=81 maxR(exact, this machine)=10
proto0: violations: reduction=0 structure=0 ascent=0 depth=0 dichotomy=0 |V|>h'(M+1)=0 sim=0 phases=0 records=0 bits=0
proto0: max depth K seen=71, max ascent run seen=8, max ceil(K/2)/((pi+1)(R+1))=1.0000, max records/bound=0.1425, max bits/bound=0.1551, max |V_P|/Q=0.3494
proto0: control (dichotomy with M/4): failing reads=7839 in 221 runs; deltas: -1=388 0=926 1=248
proto0[a=3,delta=0]: max depth K seen=71, max ascent run seen=6, max ceil(K/2)/((pi+1)(R+1))=1.0000, max records/bound=0.0833, max bits/bound=0.0553, max |V_P|/Q=0.3494
proto0[a=1,delta=-1]: runs=158 (>=2 passes: 90) steps=11350870 maxP=31 maxPhases=77 maxR(exact, this machine)=1
proto0[a=1,delta=-1]: control (dichotomy with M/4): failing reads=7121 in 72 runs; deltas: -1=158
eqwords: file words=10923 alpha=4409 w=24 image size h (incl. 0)=13
eqwords: runs=19 (>=2 passes: 14) steps=2738041614 maxP=3 maxPhases=23 maxR(exact, this machine)=16
eqwords: violations: reduction=0 structure=0 ascent=0 depth=0 dichotomy=0 |V|>h'(M+1)=0 sim=0 phases=0 records=0 bits=0
eqwords: max depth K seen=9, max ascent run seen=2, max ceil(K/2)/((pi+1)(R+1))=0.5000, max records/bound=0.0627, max bits/bound=0.0650, max |V_P|/Q=0.0000
eqwords: control (dichotomy with M/4): failing reads=34 in 3 runs; deltas: -1=8 0=7 1=4
```
- The depth ratio reaches 1.0 in `proto` for a ∈ {3, 7, 11, −5}, and in `deep` for the identity (R = 0, where Lemma C reduces to the ancestry note's count). Lemma C's bound is attained at small sizes: during review the ratio 1.0 was found with R ≥ 1 and π ≥ 1 at w = 4, 5 and 6. The checks do not show whether it is attained with R ≥ 1 at w ≥ 12.
- The control fails in every mode, so the checks are able to fail.
- On real equality-file words, chains stay shallow (depth at most 9 in 3 passes).

**Independent simulation, written during review from this note.** It covers w ∈ {4, 5, 6, 8}, a ∈ {3, 5, 7, −3, −5, −7, 9, 17} plus the lookbehind, all six orders, random entry, public initial registers and party cut, strides ±1, ±2, ±3, 4, 5 and ±6, and up to 32 passes: 11.3 million reads in 36 (w, a) categories. It checks the reduction; the chain formulas, by full unwinding to the root rather than only the grandparent; per-pass odd and even link counts ≤ exact R + 1; ⌈K/2⌉ ≤ (π+1)(R+1), with both the exact R and the closed form; the dichotomy and |V| ≤ h′(M+1); phases − 1 ≤ 2|d|P and records ≤ (phases+P)|V|; bits ≤ C(P); and simulation exactness. There are 0 violations, and up to 8 odd links fall in one pass (a = 17, w = 8), so the per-pass bound is exercised. In the control run the dichotomy with M/4 fails in all eight odd-multiplier categories; its a = 1 row, which under the control setting runs the lookahead order LD AD MU ST although it is still printed as "(lookbehind)", has no failures. At w = 8 the depth ratio with R ≥ 1 and π ≥ 1 reaches at most 0.967 (a = 17), 0.750 for the lookbehind and 0.556 for the other multipliers.

## 7. The three standard tests

- **(a) Fast globally correct solver on the hard family?** Yes. A packed comparison decides the equality files in O(N/w) steps on the unrestricted RAM. The bound concerns this architecture only.
- **(b) Same bound for 2-SAT?** Yes. The even-multiplier note's constant-palette 2-CNF equality family works unchanged, because the argument never uses the hardness of SAT.
- **(c) The oracle of the relativized-clock note?** The accounting uses that one LD returns one word and one ST changes one cell. An oracle query on a packed string that straddles the party cut can cost up to k bits, so the bound does not relativize. This is consistent with the barrier only because the model is restricted. [Relativized clock](relativized-clock.md)

## 8. Exact obstruction and next step

- **Vacuity.** The bound holds only for correct members, and no member is shown to decide anything. The any-speed question for odd a is open; an argument through cells that are never written does not apply directly, since for odd a, f is a bijection on the scanned coset.
- **P² against P.** The pass-dependent set V forces P² records. The ancestry note shows that P² distinct cells do occur with optional writes. With forced stores and a multiplier payload, whether P records suffice is open; if they do, the bound rises to N^{D+1}/polylog.
- **Remaining payload maps (open).**
  - Rotations after the ±1 shift. For d = ±1, rotl₁ is piecewise affine with multiplier 2 on Z_{Q−1}, so Lemma A's increment argument should give R = O(w); for general odd d the scan order scrambles this.
  - Right shifts and squaring after the shift: small orbits at w ≤ 9, no proof.
  - Masks after the shift: orbit Q, and runs of length Q/2 in scan order, so this method fails.
  - Payloads that read x or y.
  - The strides d ∈ {n, w}.

## 9. What is not proved

- All proofs are manuscript, with no Lean. Lemmas 0, A, B, C and D and the lower bound for a = 2^j+1 are complete as written; the transfer is the even-multiplier note's with one set changed.
- The checks are finite. Lemma A is exhaustive for ℓ ≤ 16 (a ∈ {3, 5, −3}) and for ℓ ≤ 13 (nine further a). Lemma 0 is exhaustive for w ≤ 11 over the 16 listed strides and a ∈ {3, 5, −3, 1}. The machine is exhaustive at Q = 8 over memories with at most two values (entry at LD, x = y = 0, cut α = 3, no exits), random at Q = 16, w = 12 and w = 14, and run on one actual equality file at w = 24 (19 runs, at most 3 passes). Pass counts reach at most 32 at w = 12 and 14, 64 at Q = 16 and 24 at Q = 8.
- h_D = O_D(1) is taken from the communication note, via the even-multiplier note; generated files confirm it only up to N = 2^22.
- The Corollary is assembled from three notes; it was checked as one statement during review, case by case over (a, δ). The translation Remark is checked only at the index level, not on the machine.
- The bound is conditional on correctness and may be vacuous. It is positive only from about N = 2^36 bits (a = 3), 2^30.5 (a = −3) and 2^29.4 (lookbehind).
- No class of the six-instruction map changes status, since non-multiplier payloads remain in all three classes.
- Nothing here bears on the linear, quadratic or cubic targets: tests (a) and (b) both come out "yes".
- Overlap: the chain device and the P² accounting are the journal's own (the ancestry note, and "Read pairs" in the communication note). The route, and the bound Ω(N^{D+1/2}/log²N) for a = 3, were proposed without proof in §8 of the even-multiplier note ("Odd multiplier, e.g. a = 3" and "Lookbehind payloads"). New here: the proof of the run-length bound for every odd a, stride and start (Lemma 0 with Lemma A), its lower bound, R = O(1) for negative multipliers, the checks, and the resulting coverage of odd multipliers and the lookbehind.

## Reproducing the checks

Run from `audits/`. Nothing is written outside a temporary directory.
```
python3 -B odd_multiplier_scan_checks.py
python3 -B odd_multiplier_scan_checks.py all
python3 -B odd_multiplier_bound_arithmetic.py
python3 -B odd_multiplier_scan_independent_check.py
python3 -B odd_multiplier_bound_independent_arithmetic.py
python3 -B translation_payload_case_split_check.py
```
The first script compiles `odd_multiplier_ascent_runs.cpp` and `odd_multiplier_scan_machine.cpp` into a temporary directory and runs every mode except two in about 30 seconds; with `all` it adds Lemma A up to ℓ = 16 and the run on equality-file words, which it builds with `equality_file_generator.py`, in about 75 seconds and 1.9 GB. The arithmetic script takes under a second. The review's checks are the next three: the driver compiles `odd_multiplier_scan_independent_checks.cpp` and runs its Lemma A, lower-bound, Lemma 0 and machine modes, with the M/4 control, in about 5 seconds; the other two take under a second. [Checks](../audits/odd_multiplier_scan_checks.py) · [Bound arithmetic](../audits/odd_multiplier_bound_arithmetic.py) · [Independent checks](../audits/odd_multiplier_scan_independent_check.py) · [Independent arithmetic](../audits/odd_multiplier_bound_independent_arithmetic.py) · [Translation check](../audits/translation_payload_case_split_check.py) · [Ascent runs (C++)](../audits/odd_multiplier_ascent_runs.cpp) · [Machine (C++)](../audits/odd_multiplier_scan_machine.cpp) · [Independent checks (C++)](../audits/odd_multiplier_scan_independent_checks.cpp)
