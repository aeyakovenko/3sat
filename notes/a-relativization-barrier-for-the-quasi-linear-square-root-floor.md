# An oracle with quasi-linear SAT where a linear-space parity needs time 2^{κ√(a·n·log₂n)}, for every κ < 1/√2

Fix an integer a ≥ 1 and replace the padding of the square-root-floor note's oracle by M·⌈log₂(M+1)⌉^a, where M is a wrapper's one-bit budget plus its body length plus one. The resulting recursive oracle A, in the same packed-query interface, gives NTIME^A[t] ⊆ DTIME^A[O(t(log t)^a)], so SAT and CircuitSAT run in quasi-linear time relative to A. Parity of the oracle's raw slice is still not in DTIME^A[2^{κ√(a·n·log₂n)}] for any κ < 1/√2: every machine within that time, at the journal's word width Θ(log T), errs at infinitely many n. So the √(n log n) floor that the counting route meets under a quasi-linear collapse cannot be lowered by an argument that relativizes to this interface. Merging adjacent quantifier blocks, together with a variable block schedule, narrows the gap between the upper and lower exponents to about 1.44 in the cost model, and from 3.09 to 1.56 in the earlier oracle's world, without closing it. The padding and the merge were proposed in Section 7 of the square-root-floor note; what is new here is the proofs, the exact merge identity and the variable-block computation. The proofs are at manuscript level and were checked during review. Nothing here concerns the unrelativized target; the linear, quadratic and cubic questions remain open. [Square-root floor](a-relativization-barrier-for-the-square-root-floor.md) · [Counting under quasi-linear SAT](counting-sat-under-a-quasi-linear-sat-solver.md)

## The machine, the oracle and the theorem

**Notation.**
- a is the padding exponent here. It is not the counting note's a = 3 + c.
- c_w is the instruction set's write constant: words written per step, guessed words and query replies included.
- κ is the constant in the stated lower bound.
- g(u) := ⌈log₂(u+1)⌉^a = bitlen(u)^a.
- M is the wrapper parameter B + |body| + 1, and M′ that of a queried wrapper. Where a deterministic machine is meant, as in (iii) and Sections 2 and 3, it is called "the machine M", and |M| is its code length.

**Machine.** As in the square-root-floor note:
- the machine is the packed oracle RAM;
- a query names a contiguous packed bit string and returns one membership bit at unit cost;
- each step writes at most c_w words of w bits, and a nondeterministic step guesses at most one word;
- memory starts at zero, and the input sits in a readable bank;
- for the diagonal, the width family is w_C(n) = ⌈C(√(a·n·log₂(n+2)) + log₂(n+2))⌉, so that w = Θ(log T).

**Oracle A_a(R).**
- **Raw strings:** 0y ∈ A ⇔ y ∈ R.
- **Wrapper strings:** a wrapper is 1·body·1^P.
  - body is a self-delimiting code of (N, x, t, w), with N a nondeterministic packed oracle program.
  - B = |x| + |N| + c_w(t+2)w is the set-bit budget of any single branch.
  - M = B + |body| + 1 and **P = M·g(M)**.
  - The wrapper is a member iff some branch of N^A on x, at width w, accepts within t steps.
- Every other string is a non-member.

The only change from the earlier oracle is the padding, as proposed in Section 7 of the square-root-floor note: there P = 4M, here P = M·⌈log₂(M+1)⌉^a. That section predicted the threshold √((a/2)·n·log₂n) and checked only the leading-term arithmetic; it carried out neither this step nor the merge.

**Theorem.** Fix an integer a ≥ 1, and let PAR_R = {1^n : |R ∩ {0,1}^n| is odd}.
- **(0) Well defined, for every R.** A branch of a wrapper with parameter M can query only wrapper-format strings with M′·g(M′) ≤ M − 3, so M′ < M. Induction on M defines A_a(R), and A_a(R) is recursive in R.
- **(i) Collapse, for every R.**
  - Hypotheses: N is nondeterministic; its clock t(n) ≥ n is time-constructible; its width is w_N = Θ(log t).
  - Conclusion: relative to A_a(R), N has a deterministic equivalent running in O(t·(log₂t)^a) steps. It writes one wrapper and asks one query. Hence CircuitSAT^A and DIMACS SAT run in O(N(log N)^a).
- **(ii) Upper bound, for every R.** PAR_R ∈ DTIME^A[2^{O(√(a·n·log n))}].
- **(iii) Inequality.**
  - Hypotheses: fix n and all raw bits outside length n. Let the machine M be deterministic. On input 1^n, M never holds more than B₀ one-bits and makes at most B₀ queries. For every r ∈ {0,1}^{2^n}, the run with R^{=n} = r outputs parity(r); a timeout counts as 0.
  - Conclusion: n < Φ_a(B₀). Here Φ_a is defined in Section 2, and Φ_a(2^x) = (1+o(1))·x²/(a·log₂x) as x → ∞.
- **(iv) Construction.**
  - There is a recursive R with the following property, for every program M, every C ∈ ℕ and every rational κ < 1/√2: M at width w_C fails to decide PAR_R within ⌊2^{κ√(a n log₂n)}⌋ steps for infinitely many n.
  - Hence PAR_R ∉ DTIME^{A}[2^{κ√(a·n·log₂n)}] for every κ < 1/√2, at widths ≤ w_C(n).
  - (i) and (ii) hold for this R.

As in the earlier note, PAR_R ∈ DSPACE^A(O(n)): query 0y for every y ∈ {0,1}^n, counting the query tape in space.

**The first scales are safe.** One might fear that the union bound fails at the first scales, where the shrink factor could be small. It does not. Index the scales by M = B+|body|+1 instead of by length, and count class-i strings by their bodies; the failure probability at scale i is then below 2^{−i−2}, whatever the shrink. The shrink is also never below 2, for all parameters:
- In M, Fact 0′.2 gives M′ ≤ (M−3)/2^a, and υ_i/υ_{i−1} ≥ g(υ_{i−1}+1) ≥ 2^a.
- In length, a queried string has L′ ≤ (1+2^{−a})(B−1). A querier that can query anything has B ≥ 5, so L ≥ 3^a(B+2). Hence L/L′ ≥ 3^a/(1+2^{−a}) ≥ 2.

The finite search of Part A finds a minimum L/L′ of 3.833 at a = 1.

## 1. Fact 0′ (syntactic, so usable while A is being defined)

1. **The padding is a function of the body.** Every wrapper-format string has at least P + 1 = M·g(M) + 1 one-bits. P is a function of the body, because the body determines (N, x, t, w) and hence B and M. Also |body| = M − B − 1 ≤ M − 1. So there are fewer than 2^υ wrapper-format strings with M ≤ υ.
2. **What a branch can query.** A branch of a wrapper with parameter M holds at most B ≤ M − 2 one-bits, since |body| ≥ 1.
   - A query names a contiguous string in readable memory. So a queried wrapper-format string with parameter M′ satisfies M′g(M′) + 1 ≤ B, which gives M′g(M′) ≤ M − 3.
   - Since M′ ≥ 2 (because B′ ≥ 0 and |body′| ≥ 1), we have g(M′) ≥ 2^a. So M′ ≤ (M−3)/2^a < M.
   - A deterministic machine with at most B₀ one-bits can query only strings with M′g(M′) ≤ B₀ − 1.
3. **Step budget.** The budget satisfies t ≤ B − 2 < M, because B ≥ c_w(t+2)w ≥ t + 2.

## 2. Proof of (iii): induction on scales indexed by M

**Scales.**
- Put υ₀ = 1 and υ_i = (υ_{i−1}+1)·g(υ_{i−1}+1) + 2.
- Class i (i ≥ 1) is the set of wrapper-format strings with M ∈ (υ_{i−1}, υ_i].
- **Containment.** If M ≤ υ_i and M′g(M′) ≤ M − 3 ≤ (υ_{i−1}+1)g(υ_{i−1}+1) − 1, then M′ ≤ υ_{i−1}, because u ↦ u·g(u) is strictly increasing. So class-i wrappers query only classes ≤ i−1. Class-1 wrappers query no wrapper-format string, since M′ ≥ 2 > υ₀.
- Fewer than 2^{υ_i} strings lie in class ≤ i (Fact 0′.1).

**Induction.**
- Put D₀ = 1. For i ≥ 1, put W_i = υ_i·D_{i−1}, p_i = 1/(10W_i), σ_i = υ_i + i + 2 and D_i = σ_i − 1.
- Step i. Take a class-i wrapper Q.
  1. On a fixed branch, Q's run is an adaptive tree of at most t < υ_i queries.
  2. Substitute the trees of depth ≤ D_{i−1} for the lower answers. Then Q is an OR, over branches and accepting paths, of terms of width ≤ W_i.
  3. Restrict by ρ_i ∈ R_{p_i}, independent of the earlier restrictions.
  4. Håstad's Lemma 3.3 with F = all restrictions gives Pr[depth(Q⌈ρ_i) ≥ σ_i] ≤ (5p_iW_i)^{σ_i} = 2^{−σ_i}.
  5. The union bound over fewer than 2^{υ_i} strings fails with probability < 2^{−i−2}.
  6. Lower classes keep depth ≤ D_{i−1} ≤ D_i under further restriction.
- Summed over all i, the failure probability is < 1/4. Neither the shrink factor nor the number of scales enters this sum.

[Håstad, SIAM J. Comput. 43(5), 2014](https://www.csc.kth.se/~johanh/paritycorr.pdf)

**Top.**
- Let m be the least i with υ_i ≥ Mq(B₀) := max{M′ : M′g(M′) ≤ B₀ − 1}.
- The machine M's run is a tree of depth ≤ B₀·D_m over the live variables.
- The number of live variables is V ~ Bin(2^n, ∏p_i).
- If 2^n∏p_i ≥ max(8, 2(B₀D_m+1)), then Chernoff gives Pr[V ≤ B₀D_m] ≤ e^{−1}. With probability ≥ 1 − 1/4 − e^{−1} > 0, every switching succeeds and parity keeps more live variables than M's depth. Some completion r then makes the machine's output differ from parity(r).
- Hence n < Φ_a(B₀) := Σ_{i=1}^m log₂(10W_i) + log₂max(8, 2(B₀D_m+1)).
- **Φ_a is nondecreasing in B₀.** Mq(B₀), and hence m, are nondecreasing in B₀. Every summand log₂(10W_i) is positive. D_m is nondecreasing in m. So log₂B₀ ≤ x\*_a(n) implies Φ_a(B₀) ≤ n, which is what (iv) uses.

This is Section 2 of the earlier note, with two changes:
- the classes are cut by M instead of by length;
- the union bound counts bodies (2^{υ_i}) instead of all strings up to the class's maximal length.

With the length count, σ_i would be about υ_i·g(υ_i) instead of υ_i. That adds about a·log₂y per scale, which is lower order: about x in total, against x²/(a log₂x).

**Asymptotics of Φ_a.** Write y_i = log₂υ_i and x = log₂B₀.
- **Gap bounds.** Since υ_i ≥ υ_{i−1}·(log₂υ_{i−1})^a, the gaps satisfy y_i − y_{i−1} ≥ a·log₂y_{i−1}. Also y_i − y_{i−1} ≤ a·log₂(y_{i−1}+2) + 2.
- **Per-scale cost.** log₂(10W_i) = log₂10 + y_i + log₂D_{i−1}, which lies between y_i + y_{i−1} and 2y_i + O(1).
- **Riemann sum.** For y_i ≥ e: u/log₂u is increasing and y_{i+1} − y_i ≥ a log₂y_i, so y_i ≤ ∫_{y_i}^{y_{i+1}} u/(a log₂u) du. Hence Σ_{i<m} y_i ≤ O(1) + (1+o(1))·y_m²/(2a log₂y_m).
- **Top scale.** y_{m−1} < log₂Mq(B₀) ≤ x and y_m ≤ x + O(log x). Also m = O(x/log x), and the top term is O(x).
- **Upper bound on Φ_a:** Φ_a(2^x) ≤ (1+o(1))·x²/(a log₂x).
- **Lower bound on Φ_a:** the reverse gap bound and log₂(10W_i) ≥ y_i + y_{i−1} give Φ_a(2^x) ≥ (1−o(1))·x²/(a log₂x). So this accounting, with W_i = υ_i·D_{i−1}, can give no more; Section 9 names a different switching step that might.
- **Threshold.** Let x\*_a(n) = max{x : Φ_a(2^x) ≤ n}. Then x\*_a(n)² = (1+o(1))·a·n·log₂x\*_a(n), and since log₂x\* = (1/2+o(1))·log₂n,

  x\*_a(n) = (1/√2 + o(1))·√(a·n·log₂n).

  **Rate.** The o(1) is O(log log n/log n), for three reasons:
  - The two gap bounds differ by O(1) per scale, a relative O(1/log x). Also ∫_e^U u/ln u du = (U²/(2 ln U))(1 + O(1/log U)), and the remaining terms are O(x). So Φ_a(2^x) = (x²/(a log₂x))(1 + O(1/log x)).
  - Hence x\*² = a·n·log₂x\*·(1 + O(1/log n)).
  - Also log₂x\* = (1/2)log₂n + (1/2)log₂(a·log₂x\*) + o(1).

  Part C shows the deviation from 1/√2 falling slowly, from 0.032 at n = 10⁶ to 0.026 at n = 10¹² (a = 1).
- **Time.** B₀ ≤ n + |M| + c_w(T+2)w and log₂(c_w w) = O(log n). So a parity machine must satisfy log₂T ≥ x\*_a(n) − O(log n).

## 3. Proof of (iv)

This is Section 3 of the earlier note, with x\* replaced by x\*_a.
- Enumerate triples (M, C, κ_j), each infinitely often. The κ_j are rationals below 1/√2 that tend to 1/√2, for example κ_j = ⌊2^j(1/√2 − 1/j)⌋/2^j.
- A machine defeated within ⌊2^{κ_j√(a n log₂n)}⌋ steps is also defeated within ⌊2^{κ√(a n log₂n)}⌋ steps for every κ ≤ κ_j.
- At the stage for a triple, take the least n > h such that log₂(n + |M| + c_w(⌊2^{κ_j√(a n log₂n)}⌋ + 2)·w_C(n)) < x\*_a(n), where h is the frontier of settled raw lengths. This also gives q ≤ c_w T ≤ B₀.
- Such n exist: the left side is κ_j√(a n log₂n) + O(log n), and x\*_a(n) = (1/√2 − o(1))√(a n log₂n).
- The rest is unchanged:
  1. Settle the raw lengths in (h, n) to 0.
  2. Use temporary zeros above n.
  3. Find r with f(r) ≠ parity(r) by exhaustive evaluation; (iii) guarantees one exists.
  4. Settle every raw length touched, up to h′, to 0, and set h := h′.
- R is recursive, and each triple is defeated at infinitely many n.
- A machine of width w(n) ≤ w_C(n) runs at width w_C with O(1) overhead, as in the earlier note's (iv).

## 4. Proof of (i)

- Compute t(n), and write the wrapper for (N, x, t, w_N).
- Its length is L = 1 + |body| + M·g(M) with M = O(n + |N| + t·w_N). So L = O(t·w_N·(log₂(t w_N))^a).
- At width w′ = Θ(w_N) = Θ(log t), writing it takes O(L/w′) = O(t·(log₂t)^a) steps, followed by one query.
- Addresses up to L fit in O(log t) bits.
- CircuitSAT^A: nondeterministic verification takes O(N) steps, exactly as in the earlier note (pins are explicit, so Σ arity ≤ N), and then the collapse applies. The same holds for DIMACS SAT.

## 5. Proof of (ii)

- Use the earlier note's fixed program U unchanged (its Section 4: two wrappers per level, with the level carried as data). Only the padding is new.
- A wrapper with budget τ and an X-bit input now costs O(c_w·(τ+2)·g + X·g/w) steps, with g = O((log₂(τw))^a).
- Take fixed blocks of size s = √(a n log₂n) and k = ⌈n/s⌉ levels. Then log₂T ≤ s + 2k·(a·log₂log₂T + O(1)) + O(log n) = O(√(a n log n)).
- The merged game of Section 6 improves only the constant (Part D). Its depth-uniform program is not needed for the O-form.

## 6. The merged game

- Let P_i(ρ,b) mean "the parity of R over the extensions of the prefix ρ ∈ {0,1}^{S_i} is b". Exactly one of P_i(ρ,0) and P_i(ρ,1) holds.
- For 1 ≤ i ≤ k, let E_i(ρ,v) := ∃y ¬P_i(ρy, v_y), with v ∈ {0,1}^{2^{s_i}}.
- Complementarity gives ¬P_i(ρy,v_y) ⇔ P_i(ρy, 1−v_y). Exact splitting then gives:
  - E_i(ρ,v) ⇔ ∃y∃v′ [⊕v′ = 1−v_y ∧ ¬E_{i+1}(ρy,v′)] for i < k;
  - E_k(ρ,v) ⇔ ∃y R(ρy) ≠ v_y;
  - parity(R) = 1 ⇔ ∃v [⊕v = 1 ∧ ¬E_1(∅,v)].
- So k levels need k+1 nested existential wrappers instead of 2k, with a free negation between neighbours. Part E checks this by brute force, and the independent check of the review compares E_i(ρ,v) with "v differs from the true child-parity vector".
- With block sizes s_{i+1} ≈ log₂(w·τ_{i+1}), each level gains about log₂τ variables.

**Upper exponents in the cost model.** All upper-bound numbers are cost-model values measured at one n; the limits are expected, not proved.
- **Quasi-linear world (a = 1, n = 10⁹), in units of √(a n log₂n).** The earlier two-wrapper game gives 2.1999. Merging alone, with fixed blocks, gives 1.5333. Merging with variable blocks gives 1.0589. The expected limits are 2, √2 and 1, so each change is expected (not proved) to contribute about √2. Against the proved lower exponent (1/√2 − o(1)), the measured ratio log₂T/x\* is 1.439, with expected limit √2.
- **The earlier oracle's world (π = 4, c_w = 1, n = 10⁸).** The earlier two-wrapper game with fixed blocks gives 3.9985√n. Merging alone, with fixed blocks, gives 2.8272√n (Part G), the 2√(n·log₂(πc)) = 2.83√n that the earlier note's Section 7 predicted. The earlier note's Section 5 records an estimate of 2.83√n for a variable schedule without merging. Both changes together give 2.0243√n. The ratio log₂T/x\* is 3.088 for the earlier game, 2.183 with merging alone, and 1.563 with both changes. The quotient of the two limit constants, 2.0000/1.2954, is 1.544; as π → ∞ the expected limit is √2.
- These ratios divide log₂ of steps by log₂ of one-bits. The two differ by log₂(c_w w) = O(log n).

## 7. Computation

`python3 quasi_linear_oracle_scales.py` runs Parts A to G in about 70 seconds. No line reports a conflict, a violation or a mismatch.

**Part A: exhaustive containment and length shrink.** Querier ranges B < 400 and |body| < 120; queried strings: every (M′, |body′|) with M′g(M′) + 1 ≤ B.

```
A a=1: querier B<400, |body|<120; queried (M',|body'|) exhaustive: cases=34562241 class violations=0 length violations=0; min L/L' = 3.833 at (B,|body|,M',|body'|)=(5, 1, 2, 1)
A a=2: querier B<400, |body|<120; queried (M',|body'|) exhaustive: cases=2951081 class violations=0 length violations=0; min L/L' = 16.133 at (B,|body|,M',|body'|)=(13, 1, 3, 2)
A a=3: querier B<400, |body|<120; queried (M',|body'|) exhaustive: cases=655333 class violations=0 length violations=0; min L/L' = 125.074 at (B,|body|,M',|body'|)=(25, 1, 3, 2)
```

**Part B: the first scales, exact integers.** The failure bound is (2^{υ_i} − 2)·2^{−σ_i}, from the exact body count. The cumulative failure at i = 15 is 0.2461 (a = 1), 0.2497 (a = 2) and 0.2500 (a = 3), and the total over all scales is ≤ 1/4. The smallest M-shrink is 3.833, at a = 1, i = 2; for a = 2 and a = 3 every shrink is at least 10 and at least 18. The rows below are for a = 1.

```
B   i            ups_i   ups_i/ups_{i-1}  len_i/len_{i-1}   log2 W_i  -log2 p_i   sigma_i  fail_i<=   cum
B   1                6          6.000              nan       2.58       5.91         9  1.21e-01 0.1211
B   2               23          3.833            5.750       7.52      10.85        27  6.25e-02 0.1836
B   3              122          5.304            7.072      11.63      14.95       127  3.12e-02 0.2148
B   4              863          7.074            9.726      16.73      20.05       869  1.56e-02 0.2305
B   5             8642         10.014           13.655      22.84      26.16      8649  7.81e-03 0.2383
```

**Part C: the threshold x\*_a(n)** (every machine with log₂B₀ ≤ x\* fails). x\*/√(a n log₂n) decreases slowly towards 1/√2 = 0.7071 from above for n ≥ 10⁶, and x\*²/(a n log₂x\*) increases towards 1. Monotonicity of Φ_a, proved in Section 2, was also checked on log₂B₀ = 0.05 … 2000 in steps of 0.05.

```
C a            n         x*   m(x*)   x*/sqrt(a n log2 n)   x*^2/(a n log2 x*)   Phi monotone
C 1      1000000     3299.5     332                0.7391               0.9315   True
C 1   1000000000   127277.5    8299                0.7361               0.9553   True
C 1 1000000000000  4625294.6  224777                0.7326               0.9662   True
C 2   1000000000   182878.5    5763                0.7479               0.9566   True
C 3   1000000000   225994.2    4657                0.7546               0.9572   True
```

**Part D: the upper bound in the cost model, a = 1, c_w = 1, n = 10⁹.** The last column is the consistency check: the algorithm's own B₀ must satisfy Φ_a(B₀) > n. Every row for a ∈ {1, 2} and n ∈ {10³, 10⁵, 10⁷, 10⁹} is consistent.

```
D a cw            n   mode        log2T   s/smax     k   log2T/sqrt(a n log2 n)   log2T/x*   consistent
D 1  1   1000000000   unmerged   380384.9   188558  5304                   2.1999      2.989   ok
D 1  1   1000000000   merged     265122.6   133331  7501                   1.5333      2.083   ok
D 1  1   1000000000   variable   183099.3   183059 11506                   1.0589      1.439   ok
```

**Part E: exactness of the merged game.** Every v, every v′ and every y is enumerated, for 12 block schedules with n ≤ 6; all rows show 0 mismatches, for example:

```
E n=5 blocks=[2, 1, 2]: instances=8 top mismatches=0; E_i(rho,v) checked=1280 mismatches=0
E n=6 blocks=[2, 2, 2]: instances=4 top mismatches=0; E_i(rho,v) checked=1344 mismatches=0
```

**Part F: the stage condition of (iv),** searched on a geometric grid from n = 1000 with ratio 1.02. The triples are (n, left side, x\*). For κ ≤ 0.65 the first grid point where the condition holds lies between 1000 and 6070, over a ∈ {1, 2} and both parameter sets. The construction needs only infinitely many such n, which the asymptotics of Section 2 guarantee for every κ < 1/√2; the grid search is a sanity check.

```
F a=1 kappa=0.68 c_w=1 C=1 |M|=0: first n = (3618, 148.4, 148.65)
F a=1 kappa=0.68 c_w=64 C=64 |M|=1000000000: first n = (12660, 303.19, 303.82)
F a=2 kappa=0.68 c_w=64 C=64 |M|=1000000000: first n = (3918, 228.27, 229.47)
```

**Part G: the earlier oracle (P = 4M), merged game with variable blocks, and merging alone.**

```
G  1    100000000             20242.7    9867         2.0243                                12950.0    1.563
G  1    100000000   merged, fixed s=14142, k=7072: log2T = 28272.3 = 2.8272 sqrt(n); log2T/x* = 2.183
G   asymptotic cost-model value sqrt(2 log2(pi c_w)) = 2.0000 for pi=4, c_w=1; earlier lower sqrt(log2 3.2) = 1.2954
```

**Independent check.** `quasi_linear_oracle_independent_check.py` was written during review without reusing the code above, in about 75 seconds:
- R1 checks the containment and both shrink factors, worst case per querier, for B up to 2·10⁵;
- R2 recomputes the first scales exactly and the union-bound sum;
- R3 is its own Φ_a, with exact integers up to 2^4096 and then a 256-bit mantissa;
- R4 checks the merged game exhaustively over all R for n ≤ 3 and on random R for n = 4 to 6;
- R5 re-implements the cost model;
- R6 recomputes the stage condition.

It reproduces Parts A to D, F and G where they overlap, and R4 checks the merged-game identity of Part E by a different enumeration:

```
R1 a=1 B<200000: violations=0; min L/L' = 3.8333 at (B,M')=(5, 2); min M/M' = 3.0000 at (7, 3); proved bound 3^a/(1+2^-a)=2.000
R2 a=1 cum at i=15: 0.2461; min ups ratio over i<=15: 3.833
R3 a=1 n= 1000000000000 x*=  4625294.6 m= 224777 x*/sqrt(a n log2 n)=0.7326 x*^2/(a n log2 x*)=0.9662
R4 n=3 blocks=[1, 2] all 256 R: checked=9216 mismatches=0
R5 a=1 n=1000000000 variable(5 thetas): log2T=183099.3 ratio=1.0589 levels=11506 | finer theta grid: 1.0582 (theta=0.00391) | fixed merged: 1.5332
R5 earlier world pi=4 cw=1 n=100000000: merged variable log2T=20242.7 (2.0243 sqrt n), levels=9867; merged fixed 2.8272 sqrt n
R6 a=1 kappa=0.68 c_w=64 C=64 |M|=1000000000: (12660, 303.19, 303.82)
```

A finer θ grid lowers 1.0589 only to 1.0582. The fixed merged value 1.5332 against Part D's 1.5333 is a rounding difference between the two implementations, noted during review.

## 8. The three standard tests

- **(a) A fast solver for the hard family?**
  - Relative to A_a, PAR_R has a 2^{O(√(a n log n))} solver; this is proved. In the cost model its exponent is 1.0589·√(a n log₂n) at n = 10⁹ (expected limit 1, not proved).
  - Nothing below 2^{(1/√2 − o(1))√(a n log₂n)} works.
  - No unrelativized lower bound is claimed.
- **(b) A trivial language?**
  - OR_R = {1^n : R^{=n} ≠ ∅} is in NTIME^A[n] ⊆ DTIME^A[O(n log^a n)], and the argument gives nothing for it: the last step needs a function whose restrictions keep full decision-tree depth, and a restriction makes OR constant.
  - 2-SAT-type problems are quasi-linear relative to A.
  - Passed.
- **(c) The oracle of the relativized-clock note.**
  - The result is itself an oracle world of that kind: packed queries, dense padding, and a hard raw slice settled by stages.
  - What it says is that "quasi-linear SAT (or the full collapse NTIME[t] ⊆ DTIME[t log^a t]) ⇒ DSPACE(n) ⊆ DTIME(2^{o(√(n log n))})" fails relative to A_a. So any proof of that implication must be non-relativizing.
  - The same holds for ⊕CircuitSAT or #CircuitSAT on n variables: PAR_R is the parity of a circuit with n inputs and one oracle gate.
  - Algebrization was not checked, because A has no extension queries.

[Relativized clock](relativized-clock.md)

## 9. Exact obstruction and next step

**What closes.**
- The quasi-linear route of the counting note has the floor 2^{Θ(√(n log n))}. That floor is intrinsic to relativizing alternation-trading in this interface, not an artefact of the count-splitting game.
- Quantitatively, for oracles in this packed-query interface: no relativizing argument proves that SAT ∈ DTIME[O(N(log N)^a)], or even NTIME[t] ⊆ DTIME[O(t(log t)^a)], implies DSPACE(n) ⊆ DTIME[2^{κ√(a n log₂n)}] for any κ < 1/√2. The same holds for that conclusion stated for ⊕CircuitSAT or #CircuitSAT on n variables.
- The journal's transfer gives 2^{(2+o(1))√((3+a)n log₂n)} (the counting note, with its c = a). The ratio of the two constants is 2√2·√((3+a)/a), which tends to 2√2 as a → ∞.
- Since √(a/2) → ∞, a relativizing transfer from quasi-linear SAT gives at best 2^{O_a(√(n log n))}, with a constant that grows like √a.

**Exact obstruction to closing the remaining √2.**
- The switching step pays log₂W_i = y_i + log₂D_{i−1} ≈ 2y_i per scale.
- That is because the sub-wrapper trees must have depth D_{i−1} ≈ υ_{i−1}. This depth is forced by the union bound over 2^{υ_{i−1}} strings of the class below.
- The algorithm gains only s ≈ y_i variables per level.

**Next lemma.** Find a per-scale switching step of cost (1+o(1))·y_i, or show that none exists. One option is a multi-switching lemma, for example that of Impagliazzo, Matthews and Paturi (not checked here), applied to all class-(i−1) wrappers at once. It would give a common partial decision tree of depth about υ_{i−1} whose leaves have polylogarithmic depth, so that W_i = t·polylog instead of t·υ_{i−1}. The other route is an algorithm in this world that gains about 2 log₂τ variables per level. Neither has been tried.

## 10. What is not proved

- **Nothing about the target.** This is one relativized world per a: a barrier for relativizing transfers only.
- **Manuscript level.**
  - Håstad's Lemma 3.3 was not re-read at source for this note; its wording was confirmed during review against the text extraction used for the square-root-floor note.
  - Its use uniformly in depth, over unbounded ORs, is the derivation of the square-root-floor note, checked during that note's review and reused here.
  - The budget B and the constant c_w come from the multilinear-oracle note and were not re-derived. [Multilinear oracle](multilinear-oracle-clock.md)
- **Asymptotics.** The Riemann-sum bounds in Section 2 are hand proofs. The numbers cover n ≤ 10¹² only (Part C), and the convergence to 1/√2 is slow: x\*/√(a n log₂n) = 0.7326 at n = 10¹², a = 1.
- **Upper-bound constants.** The values 1.0589·√(a n log₂n) (n = 10⁹) and 2.0243√n (the earlier world, n = 10⁸) are cost-model measurements. The wrapper-writing cost is estimated, not proved, and the limits 1, √2 and 2 are extrapolated even inside the model. Only 2^{O(√(a n log n))} is claimed.
- **Merged game.** Exactness is checked by brute force only for n ≤ 6; the identity itself is proved above. The O-form of (ii) does not depend on the merged game (Section 5). Its depth-uniform fixed-program implementation, needed only for the constants, is asserted by analogy with the earlier note's (ii), not written out.
- **Infinitely often, and widths.** The lower bound holds infinitely often. The diagonal covers widths ≤ w_C(n) = Θ(√(n log n)). The inequality (iii) does not depend on the width.
- **Integer a only.** Real a, or other polylogarithmic paddings, were not treated.
- **Part A is finite.** The exhaustive containment check covers small parameters only; the general case is the monotonicity argument in Section 2.
- **The √2 gap is not closed.**
- **Priority.** The polynomial-scale analogue (P = NP together with ⊕P ⊄ P, from self-referential padded NP wrappers plus switching) is plausibly classical, as the square-root-floor note says. The literature was not searched.

## Reproducing the checks

Run from `audits/`; neither script writes files.

```
python3 quasi_linear_oracle_scales.py
python3 quasi_linear_oracle_independent_check.py
```

The first runs Parts A to G in about 70 seconds (a string of part letters as an argument runs a subset); the second runs R1 to R6 in about 75 seconds (a string of digits runs a subset). [Scales](../audits/quasi_linear_oracle_scales.py) · [Independent check](../audits/quasi_linear_oracle_independent_check.py)
