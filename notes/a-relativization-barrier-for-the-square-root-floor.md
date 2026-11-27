# An oracle where SAT runs in linear time and a linear-space parity needs time 2^{1.29√n}

Consider a recursive oracle in the journal's packed-query interface, built with existential-only wrappers and padding factor 4. Relative to it, NTIME[t] ⊆ DTIME[O(t)], so SAT and CircuitSAT run in linear time. Parity of the oracle's raw slice is a linear-space language and lies in DTIME[2^{O(√n)}] ∩ DSPACE(n). But every machine that runs within 2^{1.29√n} steps, at the journal's word width Θ(log T), errs on it for infinitely many n. So the 2^{Θ(√n)} floor that the counting and linear-space routes meet under a constant-factor collapse cannot be lowered by an argument that relativizes to this interface. The √(n log n) form of that floor, under quasi-linear SAT, is only sketched. The proof is at manuscript level and was checked step by step during review. It is an induction over wrapper length scales, with Håstad's switching lemma (SICOMP 2014, Lemma 3.3) and a fresh restriction per scale. The polynomial analogue, an oracle with P = NP and ⊕P ⊄ P, is plausibly classical; the literature was not searched for it. Nothing here concerns the unrelativized target; the linear, quadratic and cubic questions remain open. [Counting under quasi-linear SAT](counting-sat-under-a-quasi-linear-sat-solver.md) · [Linear quantifiers](linear-quantifiers.md) · [Multilinear oracle](multilinear-oracle-clock.md) · [Relativized clock](relativized-clock.md)

## The machine, the oracle and the theorem

**Machine.** The machine is the packed oracle RAM of the relativized-clock and multilinear-oracle notes:
- A query names a contiguous packed bit string by start and bit length, and returns one membership bit at unit cost.
- Each step writes at most c words of w bits. A nondeterministic step guesses at most one word.
- Memory starts at zero. The input bits sit in a readable bank.
- For super-polynomial clocks, the word width is w = Θ(log(n+T)), the "w = Θ(log T)" convention of the counting note.
- For the diagonalization, put w_C(n) = ⌈C(√n + log₂(n+2))⌉ for C ∈ ℕ.

**Oracle A(R), for any R ⊆ {0,1}\*.** A string belongs to A(R) in exactly two cases:
- **Raw:** 0y ∈ A ⇔ y ∈ R.
- **Wrapper:** 1·body·1^P, where body is a self-delimiting code of (N, x, t, w) and N is a **nondeterministic** packed oracle program.
  - P = π(B + |body| + 1) with π = 4.
  - B = |x| + |N| + c(t+2)w is the budget of the multilinear note: the total number of set bits in all readable memory on any single branch.
  - The wrapper is a member iff some branch of N^{A(R)} on x, at width w, accepts within t steps (timeouts reject).

Every other string is a non-member. The only changes from the multilinear note are OR-trees instead of OR/AND trees, and no extension queries. The padding rule is the same, with "4(B+|body|+1) ones".

**Fact 0 (nesting shrinks; A(R) is well defined).**
- A wrapper-format string (whatever its membership) of length j has at least P ≥ πj/(π+1) = 4j/5 ones, because P ≥ π(|body|+1) gives (π+1)P ≥ π·j. The count is syntactic: it uses only the padding, so it is available while A(R) is still being defined.
- A branch of a wrapper of length L holds at most B < L/π set bits. So every wrapper-format string (whatever its membership) it can query has length ≤ (π+1)B/π < (π+1)L/π² = 5L/16. Input bits and persistent query memory are counted in B.
- Likewise, a deterministic machine that never holds more than B₀ one-bits can only query wrapper-format strings (whatever their membership) of length ≤ 5B₀/4.
- Induction on length then defines A(R) for every R, and A(R) is recursive in R.

Write ρ = π²/(π+1) = 3.2 for the shrink factor and K = (πc)².

**Theorem.**
- **(i) Collapse, for every R.** Let N be a nondeterministic packed oracle RAM with a time-constructible clock t(n) ≥ n. Relative to A(R), N has a deterministic equivalent that runs in O(t(n)) steps: it writes one wrapper and asks one query.
- **(ii) Relative upper bound, for every R.** PAR_R = {1^n : |R ∩ {0,1}^n| odd} is in DTIME^{A(R)}[2^{O(√n)}], at width Θ(√n). In the cost model of Section 4 and the script, the exponent is (2√(log₂K)+o(1))√n, which is 4√n for c = 1. That constant is model arithmetic: c is taken from the multilinear note, and the recursion's additive terms are estimated, not proved.
- **(iii) The inequality.** Fix n and all raw bits outside length n. Let M be a deterministic packed oracle RAM that, on input 1^n, never holds more than B₀ one-bits and makes at most q ≤ B₀ queries. Suppose that for every r ∈ {0,1}^{2^n} the run with R^{=n} = r outputs parity(r), counting a timeout as output 0. Then n < Φ(B₀), where Φ is defined in Section 2 and Φ(B₀) = (log₂B₀)²/log₂ρ + O(log B₀).
- **(iv) Construction.** There is a recursive R such that for every program M and every C ∈ ℕ, the machine M at width w_C fails to decide PAR_R within ⌊2^{1.29√n}⌋ steps for infinitely many n. Hence PAR_R ∉ DTIME^{A(R)}[2^{ε√n}] for every ε < 1.29, at word width Θ(√n). A machine of width w(n) ≤ w_C(n) runs at width w_C with O(1) overhead per step and O(1) extra one-bits per step (straddling writes are masked), so the diagonal covers it. (i) and (ii) hold for this R.

PAR_R ∈ DSPACE^A(O(n)), by querying 0y for every y ∈ {0,1}^n with the query tape counted in space. The method's threshold, in log₂ of the machine's one-bit budget, is √(log₂ 3.2)·√n ≈ 1.2954√n.

**No conflict with the multilinear-oracle world,** where parity is easy. The oracle of the multilinear note makes parity easy because its wrappers evaluate *alternating* trees, so unbounded alternation costs a single query. With *existential-only* wrappers, each alternation costs one level of nesting, and that is exactly what forces 2^{Θ(√n)}.

## 1. Håstad's lemma, checked at source

**Source, read in full:** J. Håstad, "On the correlation of parity and small-depth circuits", SIAM J. Comput. 43(5):1699–1708, 2014, https://www.csc.kth.se/~johanh/paritycorr.pdf (the copy the journal already cites). The quotations below were checked against the text again during review.

- **Corollary 3.2.** "the correlation of f with parity is bounded by 2^{−c_d n/(log S)^{d−1}}, where c_d is a positive constant depending only on d". This **cannot be quoted here**. The depth below grows like √n, and c_d is unspecified. The proof restricts with p = 1/(48t) at each induction step, so its c_d shrinks geometrically in d.
- **Lemma 3.3 (used).** "Let f be computed by a depth-2 circuit of bottom fanin t. Let F be a downward closed set of restrictions and ρ a random restriction from R_p. … Then Pr[depth(f⌈ρ) ≥ s | ρ ∈ F] ≤ (5pt)^s."
  - It is used with F equal to all restrictions and p = 1/(10t), which gives the bound 2^{−s}.
  - Here R_p keeps each variable with probability p and otherwise sets it to 0 or 1 uniformly.
  - Its proof (pp. 1702–1704) is an induction on the number of clauses and does not depend on the number of terms or variables. So the lemma applies to an OR over all guess strings, as checked during review.

Håstad's STOC 1986 paper and Ko's oracle constructions were not consulted, and neither is used.

## 2. Proof of (iii): induction on length scales

The induction is on wrapper length, not on alternation levels. Truncating at k levels would leave wide ORs below the cut, so the size would be dominated by the top level, not by 2^{O(2^T/c^k)}; the circuit is also not layered. Decision trees handle negated answers without De Morgan.

**Scales.**
- Put λ_i = (π+1)ρ^i, so λ₀ = 5 and λ_i = 5·3.2^i.
- Class i (i ≥ 1) is the set of wrapper strings of length in (λ_{i−1}, λ_i].
- By Fact 0, a class-i wrapper queries only wrapper-format strings (whatever their membership) of length < λ_i/ρ = λ_{i−1}, that is, of class ≤ i−1. Class-1 wrappers query none, since every wrapper-format string (whatever its membership) is longer than π+1 = 5.
- Let m be the least i with λ_i ≥ 5B₀/4. M's wrapper-format queries (whatever their membership) are then of class ≤ m.

**Variables.**
- The variables are the 2^n bits of R^{=n}. Every other raw query is a constant.
- Compose independent restrictions ρ₁, …, ρ_m with ρ_i ∈ R_{p_i}.

**Invariant after step i:** every wrapper of class ≤ i, as a function of the live variables, is computed by a decision tree of depth ≤ D_i. Here D₀ = 1 (a raw bit is a tree of depth 1) and D_i = ⌊λ_i⌋ + i + 2.

**Step i.** Take a class-i wrapper Q with budget t. Since t < B < λ_i/π, we have t < λ_i/π.
1. On a fixed branch β, Q's run is an adaptive tree of at most t queries.
2. Replace each answer by its tree: depth 1 for a raw bit, depth ≤ D_{i−1} for a lower wrapper. This gives a tree of depth ≤ t·D_{i−1} over the live variables.
3. So Q is an OR over β of such trees, which is a DNF of width ≤ W_i := (λ_i/π)·D_{i−1}.
4. Restrict with p_i = 1/(10W_i). By Lemma 3.3, Pr[depth(Q⌈ρ_i) ≥ σ_i] ≤ 2^{−σ_i}, with σ_i = ⌊λ_i⌋ + i + 3.
5. There are at most 2^{⌊λ_i⌋+1} strings of length ≤ λ_i, so a union bound fails with probability ≤ 2^{−i−2}.
6. Lower classes keep depth ≤ D_{i−1} under further restriction.

Summed over all scales, the probability that some step fails is ≤ 1/4.

**Top.**
- M's run is an adaptive tree of at most q queries.
- Substituting the trees gives a tree of depth ≤ q·D_m.
- Parity of V live variables needs depth V.
- The number of live variables is V ~ Bin(2^n, P) with P = ∏_{i≤m} p_i.

**Conclusion.**
- If 2^n·P ≥ max(8, 2(q·D_m + 1)), then by Chernoff Pr[V ≤ q·D_m] ≤ Pr[V < 2^nP/2] ≤ e^{−2^nP/8} ≤ e^{−1}.
- So with probability ≥ 1 − 1/4 − e^{−1} > 0, all switchings succeed and V > q·D_m.
- Some completion r of that restriction then has M's output ≠ parity(r).
- Hence computing parity forces n < Φ(B₀) := Σ_{i=1}^m log₂(10W_i) + log₂ max(8, 2(qD_m + 1)), with q ≤ B₀.

**Size of Φ.** Since log₂ W_i ≈ 2log₂λ_i ≈ 2i·log₂ρ and m ≈ log_ρ B₀, we get Φ(B₀) = (log₂B₀)²/log₂ρ + O(log B₀). Part A of the script evaluates Φ exactly (Section 5).

**Meaning for time.** Here B₀ ≤ n + |M| + c(T+2)w, with c the ISA write constant. So a machine with log₂(T·w) ≤ √(n·log₂ρ) − O(1) cannot compute parity. A heuristic count predicts twice this constant: k collapsed levels at factor c give depth-(k+1) circuits of size 2^{O(2^T/c^k)}, and Håstad's bound then asks T ≥ k log₂ c + n/k ≥ 2√(n log₂ c). The proof above replaces that count, with the shrink factor ρ in the role of c, and loses the factor 2: per scale, the restriction must cut the variables by the DNF width ≈ λ_i·λ_{i−1}, which is about 2log₂λ_i bits. Whether a finer accounting, or a better algorithm, closes this factor is not determined.

## 3. Proof of (iv): the stages

Enumerate the pairs (M, C), each infinitely often. Keep a frontier h, with every raw bit of length ≤ h settled; start with h = 0.

At the stage for (M, C):
1. **Choose n.** Let n be the least length > h such that log₂(n + |M| + c(⌊2^{1.29√n}⌋ + 2)·w_C(n)) < x\*(n), where c is the ISA write constant (guessed words and query replies included), so that also q ≤ cT ≤ B₀. Here x\*(n) is the largest x with n ≥ Φ(2^x) (Part A). Such n exist, because the left side is 1.29√n + O(log n) and x\*(n) = 1.2954√n − O(1). As computed during review, the condition first holds near n ≈ 7.9·10⁶ for c = C = 1 and |M| = 0, and near n ≈ 2.6·10⁷ for c = C = 64 and |M| = 10⁹.
2. **Settle below n.** Settle every raw bit with length in (h, n) to 0.
3. **Set up the run.** Use temporary zeros at every raw length above n, and leave R^{=n} free.
4. **Find a defeating r.** Let f(r) be the output of M on 1^n within ⌊2^{1.29√n}⌋ steps, with timeout giving 0. By (iii), f ≠ parity. Find r with f(r) ≠ parity(r) by exhaustive search; each f(r) is a finite clocked run with exhaustive wrapper evaluation. Set R^{=n} = r.
5. **Settle what the run touched.** Let h' be the larger of n and the largest raw length touched in that evaluation, including sparse long raw buffers anywhere in the address ranges of nested wrappers. Settle every raw bit with length in (n, h'] to 0, and set h := h'.

Later stages change only lengths > h'. So the evaluation at this stage, and with it M's error or timeout on 1^n, is permanent. There is no conflict between the stages and the oracle's definition: A(R) is a function of R, f(r) is evaluated with every wrapper computed under R^{=n} = r, and (iii) guarantees an r with f(r) ≠ parity(r).

Every raw bit is settled at some finite stage, so R and A(R) are recursive. Every (M, C) is defeated at infinitely many n; for a machine within time O(2^{ε√n}) with ε < 1.29, a timeout is impossible at large n, so the machine errs.

The diagonal handles the w = Θ(log T) width family. The inequality (iii) does not depend on the width, so any countable family of width functions computable from n can be added to the enumeration.

## 4. Proofs of (i) and (ii)

**(i).**
1. Compute t(n). Write the wrapper for (N, x, t, w_N) with all-ones padding words. Its length is L = O(t·w_N + n), so writing it takes O(L/w) = O(t) word steps at width w ≥ w_N + O(1).
2. Ask one query.

Nested queries, and machines that query the oracle themselves (including long sparse raw buffers), are answered inside the oracle's definition. A machine cannot query its own wrapper, because a branch holds fewer than L/π one-bits.

For CircuitSAT^A in the encoding of the relativized-clock note, nondeterministic verification takes O(N) steps:
- Guess the inputs.
- Evaluate the gates in order.
- For an oracle gate of arity a, write its query bit by bit in O(a) steps. Σa ≤ N, because the pins are listed explicitly.

Then apply (i). The same holds for DIMACS SAT.

**(ii).** Let P_i(ρ,b) say "the parity of R over the extensions of the i·s-bit prefix ρ to length n is b". The game is the mod-2 form of the journal's count-splitting game:
- P_k(ρ,b) ⇔ R(ρ) = b.
- P_{i−1}(ρ,b) ⇔ ∃v ∈ {0,1}^{2^s} (⊕v = b ∧ ∀y P_i(ρy, v_y)).

Exactness:
- The honest v is the only one whose children all hold.
- Part C of the script checks this by brute force (Section 5).

Construction with one fixed nondeterministic program U, which carries a mode bit and gets ⟨U⟩, the level, and its data as input:
- D(i−1, ρ, b) writes a wrapper for U in mode 1 and asks it.
- Mode 1 guesses v (2^s/w words), checks ⊕v = b, writes a wrapper for U in mode 2 on (ρ, v), and accepts iff that wrapper's answer is 0.
- Mode 2 guesses y, runs D(i, ρy, 1−v_y), and accepts iff it accepts.

The universal quantifier through a negated existential wrapper is correct, because P_i(ρ′,0) and P_i(ρ′,1) are complementary.

Costs:
- Writing a wrapper with budget t and an X-bit input costs πc(t+2) + (2π+1)X/w + O(1) steps.
- So D(i−1) = (πc)²·D(i) + O(πc·2^s/w + (πc)²(s + n/w)). The mode-2 additive term passes through both wrapper factors, as in the script's a·(s + n/w + 6) with a = (πc)².
- Over k = ⌈n/s⌉ levels, log₂ T ≈ k·log₂K + s, which is minimised at s ≈ √(n·log₂K). This gives T = 2^{(2√(log₂K)+o(1))√n}; Part B of the script checks it.

This is the relativized form of the counting note's transfer with constant-factor stripping. It is not new.

## 5. Computation

`python3 existential_wrapper_oracle_parity_bounds.py` (about 8 s).

**Part A.** x\*(n) is the largest log₂B₀ with Φ(B₀) ≤ n. It is a failure threshold: every machine whose one-bit budget satisfies log₂B₀ ≤ x\*(n) fails to compute parity. It approaches √(n·log₂ρ):
```
Part A: failure threshold x*(n) = max log2(B0) with Phi(B0) <= n; every machine with log2(B0) <= x*(n) fails (pi = padding factor)
A   pi      n        x*(n)   sqrt(n log2 rho)   x*/sqrt(n)   sqrt(log2 rho)
A    4      1000       37.2           41.0         1.1776         1.2954
A    4   1000000     1292.4         1295.4         1.2924         1.2954
A    4 100000000    12950.0        12954.0         1.2950         1.2954
A   16 100000000    19774.1        19780.1         1.9774         1.9780
```

**Part B.** The relative upper bound, compared with the lower bound:
```
B   pi  c      n     log2 T   s*    k*   log2T/sqrt(n)   2sqrt(log2 K)   log2T(upper)/x*(n)
B    4  1      1000     120.6    63    16       3.8126         4.0000        3.238
B    4  1 100000000   39985.3 20000  5000       3.9985         4.0000        3.088
B   16  1 100000000   56553.3 28177  3549       5.6553         5.6569        2.860
```
At π = 4 and c = 1, the exponents are 1.295√n (lower, proved, in log₂ of one-bits) and 4√n (upper, in the script's cost model). Both are Θ(√n); in that model log₂T(upper)/x\*(n) tends to 2√(2log₂(πc)/log₂ρ) ≈ 3.09 (the two differ in units by log₂(cw) = O(log n)).

**Part C.** XOR-splitting game, checked by brute force over all messages:
```
C n=4 s in (1, 2, 3, 4): instances=80 mismatches=0
C n=6 s in (1, 2, 3): instances=30 mismatches=0
C n=8 s in (2, 3): instances=6 mismatches=0
```

**Independent check.** `existential_wrapper_oracle_independent_check.py` was written during review, independently of the first script. It takes ⌊λ_i⌋ exactly with rationals and reproduces Part A to every printed digit for π = 4 and π = 16. Extended to n = 10¹², the deficit √(n log₂ρ) − x\*(n) stays in [2.8, 4.1] for π = 4 and in [3.8, 7.3] for π = 16, as Φ = x²/log₂ρ + O(x) predicts; Φ is nondecreasing on the tested grid. For example:
```
   4 1000000000000   1295401.35       1295404.15      2.79 771957     1.29540
  16 1000000000000   1978006.72       1978013.44      6.71 505555     1.97801
  Phi nondecreasing on log2 B0 = 0.05..10000 step 0.05: True
```
It also checks the union bound and the final margin of Section 2, the stage condition of Section 3, that the algorithm of (ii) is never excluded by (iii) (with the uniform block schedule and with a variable one), and the arithmetic of Fact 0 on a grid:
```
  sum_i 2^{floor(lam_i)+1} 2^{-sigma_i} (i<120) = 0.25   1 - 1/4 - e^-1 = 0.3821
  c=1 C=1 |M|=0: first n = (7931874, 3644.57, 3645.09)
  c=64 C=64 |M|=1000000000: first n = (26024780, 6605.19, 6605.21)
  cases=57362 violations=0
```
The consistency check prints "ok" in all 15 rows: at n = 10⁸, π = 4 and c = 1, the variable-block schedule (log₂T ≈ 2√(n log₂(πc)) = 2.83√n) still stays above x\*.

## 6. The three standard tests

- **(a) A fast solver for the hard family?**
  - Relative to A, PAR_R has the 2^{O(√n)} solver of (ii), and (iv) shows that nothing below 2^{1.29√n} works.
  - The upper and lower bounds are both Θ(√n) in the exponent. In the script's cost model the constant factor between them is about 3.1.
  - No unrelativized lower bound is claimed.
- **(b) A trivial language?**
  - Run the same argument on OR_R = {1^n : R^{=n} ≠ ∅}. That language is in NTIME^A[n] ⊆ DTIME^A[O(n)], and the argument gives nothing for it.
  - The final step needs a function whose restrictions keep full decision-tree depth. Restrictions turn OR into a constant.
  - 2-SAT-type problems are trivially linear relative to A. Passed.
- **(c) The oracle of the relativized-clock note.**
  - The result is itself an oracle world of the same kind: packed queries and dense padding, with the hard bit on a raw slice settled by stages.
  - Its p = 1 world has linear CircuitSAT^A by a circuit wrapper, and so does A, through (i).
  - What the result says is that "H ⇒ DSPACE(n) ⊆ DTIME(2^{o(√n)})" fails relative to A, where H is linear SAT or the full collapse. So any proof of that implication must be non-relativizing.
  - Algebrization was not checked: A has no extension queries.

The barrier note records the relativization barrier for the uniform route in general; this result is an instance of it for one transfer. [Relativization](what-any-proof-of-superlinear-sat-time-must-get-past.md#b-relativization)

## 7. Exact obstruction and next step

**What closes.** Every relativizing improvement of the counting and linear-space transfer below 2^{Θ(√n)} is ruled out: better stripping, cleverer games, more alternations per level. The barrier is stronger than a fixed constant:
- With padding factor π, the same proof gives a world where H holds and parity needs 2^{(√(log₂ρ_π) − o(1))√n}, with ρ_π = π²/(π+1).
- Since √(log₂ρ_π) → ∞ as π → ∞, for every δ there is a relativized world where linear SAT holds and parity needs 2^{δ√n}.
- So a relativizing transfer from linear SAT can give at best 2^{O_H(√n)}, with a constant that depends on the SAT algorithm. That is the form the route already has: 2√(2n·log₂K).
- So a relativizing argument can never trade the hypothesis "some linear-space language needs 2^{ω(√n)}" for a weaker hardness assumption. The 2^{Θ(√n)} floor under constant-factor stripping is intrinsic to relativizing alternation-trading in this packed-query interface, not an artefact of the counting note's game. The √(n log n) form under quasi-linear SAT is covered only by the sketch below.

**Next step, named and not done: the quasi-linear form.** Use padding P = (B+|body|+1)·⌈log₂(B+|body|+2)⌉^a. Then:
- The collapse becomes NTIME^A[t] ⊆ DTIME^A[t·polylog t], and SAT^A is quasi-linear.
- The shrink becomes ρ_ℓ ≈ (log ℓ)^a, so m ≈ log B₀/(a·log log B₀) scales.
- The same induction should give n ≲ (log₂B₀)²/(a·log₂log₂B₀), that is, log₂T ≳ √((a/2)·n·log₂n).
- The relative upper bound becomes 2^{O(√(a·n·log n))}.

That would make the √(n log n) of the quasi-linear route a relativization barrier as well. The step to check is the union bound at scales where ρ varies with ℓ; during review only the leading-term arithmetic was checked.

**Not addressed.** Closing the constant gap between √(log₂ρ) and 2√(log₂K) is a different question. The first thing to try: two wrappers per XOR level is probably not optimal in this world. Write alternate levels in the ∀v∃y form so that adjacent quantifier blocks merge, giving about k+1 blocks for k levels. That would bring the upper bound to about 2√(n·log₂(πc)), the heuristic 2√(n log c) read as an upper bound.

## 8. What is not proved

- **Nothing about the target.** The theorem is about one relativized world. It is a barrier for relativizing arguments only.
- **Manuscript level.** The proof is a manuscript argument and is not machine-checked.
  - The uniform-in-depth use of Lemma 3.3 is derived here by Håstad's restriction method; it is not a statement in the paper.
  - The set-bit budget B and the ISA constant c are taken from the multilinear note and not re-derived.
- **Width family.** The diagonal is stated for the width family w_C. By the width sentence in (iv), it also covers every machine of width w(n) ≤ w_C(n). Machines of larger width are covered by (iii) only through the stated inequality, which does not depend on the width.
- **Infinitely often.** The lower bound holds infinitely often, which is the standard sense of ∉ DTIME. It is not proved for almost every n.
- **Constants.** The lower exponent 1.295√n (in one-bits) is proved. The upper exponent 4√n (for c = 1) is cost-model arithmetic; only 2^{O(√n)} is claimed. The two are not matched.
- **Quasi-linear case.** Section 7 gives a sketch only.
- **Priority.** The polynomial-scale analogue, an oracle with P = NP and ⊕P ⊄ P built from self-referential padded NP wrappers plus a switching lemma, is plausibly classical. The literature was not searched for it or for the form given here. No journal note contains this oracle (a search of the notes during review found none), so the time-calibrated √ form with packed queries is new to the journal; its priority outside the journal is not established.
- **Finite checks.** Part C checks game exactness only for n ≤ 8. Parts A and B are arithmetic in the cost model stated in the script.

## Reproducing the checks

Run from `audits/`; neither script takes arguments or writes files.

```
python3 existential_wrapper_oracle_parity_bounds.py
python3 existential_wrapper_oracle_independent_check.py
```

[Parity bounds](../audits/existential_wrapper_oracle_parity_bounds.py) · [Independent check](../audits/existential_wrapper_oracle_independent_check.py)
