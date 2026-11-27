# Under a quasi-linear SAT solver, #CNF-SAT runs in 2^{(2+o(1))√((3+c) n log n)}: an explicit constant for a transfer the journal already implies

This note re-derives, with an explicit leading constant, a transfer that bound (1) of the linear-quantifiers note already implies in O-form. If SAT has a deterministic O(N log^c N) log-word RAM algorithm, then #CNF-SAT on n variables (formula length ℓ ≤ 2^{√n}) runs in time ℓ·2^{(2+o(1))·√((3+c)·n·log₂n)}; for 3-CNF with m clauses that is 2^{O(√(m log m))}. Read as a route to the target, it needs a deterministic lower bound for #3SAT: for some fixed δ > 0, no algorithm computes #3SAT on n variables with O(n) clauses within 2^{(2+δ)√(3 n log₂ n)} for all large n, on the RAM with w = Θ(log T). That counting bound is stronger than the target: by the transfer it implies that SAT has no linear-time algorithm, and it also implies P ≠ PP (which P ≠ NP implies as well; the bound is not known to follow from P ≠ NP). It fails relative to a PSPACE-complete oracle with its multilinear extension (Aaronson–Wigderson), and also relative to the journal's linear-clock oracle, so its proof can neither relativize nor algebrize. No lower bound is proved, and the linear, quadratic and cubic questions remain open. [Linear quantifiers](linear-quantifiers.md)

Two refinements of the block sum-check mechanism that was proposed for this route:
1. No sum-check, field or bounded occurrence is needed, because the plain integer count-splitting game is already an exact Σ_{2k} form with smaller messages.
2. The alternating form needs no field-size condition. A false claim that passes the sum check already disagrees with the honest table at a Boolean point, so the universal player can restrict to {0,1}^s, and the algebraic game becomes the integer game mod q. The Schwartz–Zippel condition q > d·n is needed only for the randomized protocol.

The finite checks verify the games exactly on toy formulas (Section 2e).

## 1. Statements

**Lemma (transfer).** Suppose there are a fixed deterministic log-word RAM program S and constants C and c ≥ 0 such that, for every N ≥ 2, S decides every N-bit DIMACS CNF in at most C·N·(log₂N)^c steps. Then there is a deterministic algorithm that, given any CNF φ with n variables and DIMACS length ℓ ≤ 2^{√n}, outputs #φ within ℓ·2^{(2+o(1))√(a·n·log₂ n)} steps, where a = 3 + c. Here o(1) → 0 as n → ∞, with S fixed. The model has to be pinned down, because a 2^{Θ(√(n log n))}-step computation cannot run with words of Θ(log ℓ) bits: such a machine addresses only poly(ℓ) cells. The conclusion holds on the log-word RAM run on the padded input φ#1^P with P = 2^{⌈E⌉}, where E is the exponent above, so the words have Θ(E) bits. Equivalently, it holds on a multitape Turing machine in time 2^{O(√(n log n))}·poly(ℓ), since polynomial overhead in T only changes the constant in the exponent. Any 3-CNF with m clauses has at most 3m occurring variables (unused declared variables only contribute a factor 2^{#unused}). So bounded occurrence is not needed, and the bound becomes 2^{(2+o(1))√(3a·m·log₂ m)}.

**Credit.** The O-form of this lemma already follows from bound (1) of the linear-quantifiers note (24 November), A·2^{O(√(L log₂H)+log₂H)}. Apply it to the deterministic enumeration machine for each bit of #φ, which uses space O(n + log ℓ) and time 2^n·poly(ℓ), so that L = n + O(log ℓ) and H = O(n). The checkpoint-pullback note already applies (1) bit by bit to a unique output, giving (s+n)·2^{O(√(n log n))}. New here: the explicit leading constant 2√(3+c), obtained from the packed reduction and DIMACS writing; the exact count-splitting presentation; and the oracle remarks. [Linear quantifiers](linear-quantifiers.md) · [Checkpoint pullbacks](checkpoint-pullbacks.md)

**Contrapositive ("what would suffice").** Suppose that for some fixed δ > 0, no deterministic algorithm computes #3SAT on formulas with n variables and O(n) clauses within 2^{(2+δ)√(3 n log₂ n)} steps for all large n. As phrased, this is already an infinitely-often lower bound: every algorithm exceeds the bound for infinitely many n. Then SAT has no O(N)-time log-word RAM algorithm. The o(1) in the lemma depends on the fixed solver S through K^{2k}, which is why δ is fixed in advance. The constant 2√3 has meaning only on the RAM with w = Θ(log T) (the padded form); on a multitape TM only the O(·) form survives. If instead #3SAT is not in 2^{O(√(n log n))}, for example if it needs 2^{n^{1/2+ε}}, then SAT has no O(N polylog N) algorithm. In particular, the counting form of the Weak ETH (#3SAT ∉ O(2^{n^{1−ε}}) for every ε > 0) implies that SAT is not quasi-linear. No implication from that hypothesis to P ≠ NP is known.

## 2. The proof

### 2a. The exact alternating form: integer count-splitting, no randomness, no field

Split the variables into consecutive blocks of sizes s₁,…,s_k with Σsᵢ = n, and put nᵢ = n − s₁ − … − sᵢ. For a prefix ρ ∈ {0,1}^{s₁+…+sᵢ}, let Qᵢ(ρ,c) mean "c = #φ|_ρ". Then:

- Q_k(ρ,c) ⇔ c = φ(ρ);
- Q_{i−1}(ρ,c) ⇔ ∃v ∈ [0,2^{nᵢ}]^{{0,1}^{sᵢ}} ( Σ_y v_y = c ∧ ∀y ∈ {0,1}^{sᵢ} Qᵢ(ρy, v_y) ).

Unrolled into prenex form, c = #φ ⇔ ∃v₁∀y₁∃v₂∀y₂…∃v_k∀y_k V, where V = ⋀ᵢ[Σ_y v_{i,y} = v_{i−1,y_{i−1}}] ∧ [v_{k,y_k} = φ(y₁…y_k)] and v_{0,·} := c.

*Proof of exactness (induction on k−i).* (⇐) The honest message v_y = #φ|_{ρy} sums to c, and every child is true by the induction hypothesis. (⇒) If all children are true, the induction hypothesis forces v_y = #φ|_{ρy}, so c = Σ_y #φ|_{ρy} = #φ|_ρ. Equivalently: whenever the claim is false, every message that passes the sum check has a child y with a false claim, and the universal player picks that child. Nothing is probabilistic, so no soundness-error argument is needed. This is the s = 1 game of the succinct-prover note ("Reply-dependent strategies and exact counting") with block size s. The exponentially long messages are what make the number of blocks small. [Succinct prover](succinct-prover.md)

*Costs per round* (w = word width): the message has 2^{sᵢ}(nᵢ+1) bits; the universal choice has sᵢ bits; the verifier does O(2^{sᵢ}⌈(n+1)/w⌉) word operations for the multi-word sum, O(⌈n/w⌉) for the comparison, and one indirect load to select v_{y}. The leaf check evaluates φ on the assignment in O(ℓ). To recover the count, binary search over t ∈ [0,2^n] using G_t ≡ ∃c (c ≥ t ∧ Q₀(∅,c)). That is n+1 calls, each still Σ_{2k}, because c joins v₁'s block.

### 2b. The algebraic block sum-check, and why it adds nothing

Arithmetise φ as P(x) = Π_j (1 − Π_{ℓ∈C_j}(1 − ℓ(x))). The individual degree of xᵢ is at most its number of occurrences, so it is at most d = B under bounded occurrence B. Round i sends a table g on {0..d}^{s} over F_q, interpreted as the unique polynomial of individual degree ≤ d with those values.

- **Field size.** The alternating form needs no field-size condition. If the claim is false but Σ_{Y∈{0,1}^s} g(Y) matches it, then Σ_{Y∈{0,1}^s}(g−h)(Y) ≠ 0 for the honest table h, so g and h already differ at a *Boolean* point. The universal player can therefore be restricted to {0,1}^s. Under that restriction the algebraic game is the integer game mod q: it uses no polynomial structure, and exactness mod q holds for every q ≥ 2. The condition q > d is needed only to read the table as a polynomial of individual degree ≤ d. Schwartz–Zippel's q > d·n is needed only for the *randomized* protocol.
- **Characteristic.** Computing over F_q gives #φ mod q. Recover #φ by CRT over the primes in (d, X] with product > 2^n. By Chebyshev's bound X = O(n), there are O(n/log n) primes, each found by a sieve, and each fits in one word, so a field operation is O(1) word operations (multiply, then divide). Each prime is a separate Σ_{2k} computation.
- **Message and verifier cost.** (d+1)^s field elements per round. The Boolean sum takes 2^s additions. Evaluation is a lookup at a Boolean or grid challenge, or O((d+1)^s) operations by successive Lagrange interpolation at a general point of F_q^s.
- **Net effect.** The exponent per round becomes s·log₂(d+1) instead of s. With d = 3, which is what the parsimonious occurrence-3 reduction gives (n' ≤ 3m variables), the final exponent is at least √2 worse: exactly √2 at equal variable counts, and more when the occurrence-3 reduction raises n to the number of occurrences. The integer game also works for every CNF, for circuits, and for #2SAT. The field was only simulating, with random points, the coverage of all children that the universal quantifier already provides.

### 2c. Stripping each quantifier block through DIMACS

Given a deterministic algorithm for Qᵢ with time Dᵢ, define two levels per round:

- Fᵢ(ρ,v) ≡ ∃y ¬Qᵢ(ρy,v_y). This is a nondeterministic computation of time O(s + n/w + Dᵢ) on input (φ,ρ,v) of length ℓ + n + 2^{s}(n+1) bits.
- Q_{i−1}(ρ,c) ≡ ∃v [Σv = c ∧ ¬Fᵢ(ρ,v)]: guess v, check the sum, run the deterministic algorithm for Fᵢ.

Each level is compiled by the journal's packed reduction. A nondeterministic RAM run with clock h on m_in input words, H = max(h, m_in, 2) and L = ⌈log₂(H+2)⌉, becomes a 3-CNF with O(HL²) clauses and O(HL³) bits, all variable indices of O(L) bits, and the input fixed by unit clauses. For literal DIMACS, choose variable numbers with exactly D = O(L) decimal digits, which gives fixed strides. Write row and offset strides as powers of ten, and take router wire numbers from a decimal table of O(H) entries filled by a decimal counter. Writing the file then takes O(1) words per literal, so O(HL²) steps, and the length is O(HL³) bits up to a constant factor. Running S costs O(HL³·L^c) = O(H·L^a). [Packed band transfer](packed-band-transfer.md)

The per-level constant has to be independent of the depth. The linear-quantifiers note ("Removing quantifier blocks uniformly") proves this for a growing number of blocks: one fixed program generates each new matrix, and its constants depend only on the SAT program and the encoding. The same holds for the native fixed verifier of the alternating-speedup note ("One fixed verifier", with the depth as data) once all operand lengths lie in one polynomial band. That note proves it only for k = O(log log n), and the extension is made here. Only a = 3 + c is taken from the packed-band transfer. Hence [Alternating speedup](alternating-native-speedup.md)

  D(Q_{i−1}) ≤ (K·L^a)²·(D(Qᵢ) + 2^{s+1}(n+1) + ℓ),  D(Q_k) = O(ℓ),
  so D(Q₀) ≤ (K L^a)^{2k}·O(k(2^s n + ℓ)), where L is the log of the largest formula.

Pad n to a multiple of k with dummy variables, which multiplies #φ by a known power of two. All instance lengths then lie between 2^s and P^{1+o(1)}, so the logarithms of all instance lengths are within a factor 2+o(1) of each other, and the solver's word widths agree with the padded outer width up to constant factors. (Without padding, a short last block only makes an instance shorter, and a narrower guest width costs O(1) per instruction on a wider host by masking.) That is the condition the journal's simulation uses: constant limbs, and a radix trie for sparse guest addresses. The extension to k = Θ(√(n/log n)) and exponential-size instances is a manuscript argument, not machine-checked.

### 2d. Optimising k

log₂ D(Q₀) ≈ s + 2k(a log₂L + log₂K) + O(log(nℓ)) with s = ⌈n/k⌉ and L ≈ 2s. Setting k = α√(n/log₂n) gives √(n log₂ n)·(1/α + aα)(1+o(1)), which is minimised at α = a^{−1/2}. So k* ≈ √(n/(a log₂ n)), s* ≈ √(a n log₂ n), and **E = (2+o(1))√(a n log₂ n)**. The factors K^{2k} = 2^{O(√(n/log n))}, n+1 (binary search) and ℓ are lower order for ℓ ≤ 2^{√n}. For linear-time SAT (a = 3) this is 2^{(3.46+o(1))√(n log₂ n)}.

Numerical check, with lower-order terms kept: Part D of `python3 count_splitting_game_check.py` prints, for a = 3 (abridged to three rows):
```
      1000    3      4     250        484            346            317
   1000000    3    107    9346      18692          15465         223990
 100000000    3    965  103627     207868         178579       19398131
```
The columns are n, a, k*, s*, E(k*), 2√(a n log₂ n), and n/√log₂ n. For a = 3, E(k*)/(2√(a n log₂ n)) falls from 1.40 at n = 10³ to 1.16 at n = 10⁸, and E(k*) < n from n ≈ 10³. This is in a model with log₂K = 1 and all hidden constants set to 1; the true K depends on S and is unknown. This says nothing practical, because the hypothesis is presumably false. By an independent computation during review, the checkpoint route of the linear-quantifiers note gives the same leading constant (2+o(1))√(a n log₂ n), using two blocks per level, 2^k·O(n)-bit messages and L/k levels. The integer game is therefore a presentation choice, needed neither for the O-form nor for the constant.

### 2e. Toy-formula evidence (all exact, no sampling)

`python3 count_splitting_game_check.py` takes about 7 s; `python3 count_splitting_algebraic_extra_cases.py` takes about 8 s. [count_splitting_game_check.py](../audits/count_splitting_game_check.py) · [count_splitting_algebraic_extra_cases.py](../audits/count_splitting_algebraic_extra_cases.py)
- Part A: literal enumeration of *every* prover message (n=4, k=2, s=2), for 6 formulas. Output lines such as `seed 2: brute #phi=10  accepted claims=[10]  OK`: in each case the only accepted root claim is the brute-force count.
- Part B: exact game value by sumsets, for bounded-occurrence (≤3) 3-CNF with n ∈ {6,8,10,12}, s ∈ {1,2,3,4}, 3 formulas each. Every line reads `winning root claims == {brute count}: OK`.
- Part C and the extra cases: algebraic block sum-check with *every* table and *every* challenge in F_q^s enumerated, at the smallest prime q > d (q = 3 for d = 2; q = 5, and also 7, for d = 3). Challenges range over all of F_q^s, not only Boolean points. F_4 is never tested, because the script handles prime fields only. Examples: `n=4 s=2 d=2 q=3 m=4 seed=1002: #phi=8, mod q=2, accepted=[2] OK` (extra cases) and `n=4 s=1 d=3 q=5 seed=2: #phi= 3, #phi mod q=3, accepted=[3]  OK` (Part C). 21 cases, all OK. In every case exactly one residue is accepted, and it is #φ mod q.

The scripts check only the games. They do not run the stripping recursion, which needs the hypothetical solver.

### 2f. A side remark (proved here, not script-checked)

The same block trick works for TQBF. In each block of s variables, the existential player commits to a strategy table: each of its variables as a function of the earlier universal variables in the block, at most s·2^s bits. The universal player then sets all of its block variables. The game value equals the QBF value. For the converse, the universal player replays its QBF strategy sequentially inside the block. So under quasi-linear SAT, TQBF on n variables is also in 2^{O(√(n log n))}·poly, and "TQBF needs 2^{n^{1/2+ε}}" also suffices. This O-form also follows from bound (1) of the linear-quantifiers note, because TQBF on n variables is decided in space O(n + log ℓ) and time 2^n·poly(ℓ).

## 3. Comparison with known #3SAT algorithms (sources)

- OpenAI, "The Exponential Time Hypothesis is False", dated 17 Oct 2026, revised 25 Oct 2026, https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf. **Read: the abstract and the statement of Theorem 1.1 and its corollaries only, not the proofs.** It claims a deterministic count of #F for k-CNF in (n+m)^{O_k(1)}·2^{O_k(n log log n/√log n)} bit operations and polynomial space, and (n+m)^{O_{k,D}(1)}·2^{O_{k,D}(n/√log n)} when m ≤ Dn. The abstract states 2^{n/(log n)^{1/2+o(1)}}. Unrefereed.
- Anthropic, "A 2^{o(n)} Time Algorithm for 3-SAT" (26 or 27 Oct 2026): **not accessed**; known only through secondary sources. Majdoddin, https://arxiv.org/abs/2610.41622 (abstract read), makes its #3-SAT recursion explicit. The abstract states 2^{O(m/√log m)} for counting, for every j, the assignments that satisfy exactly j clauses, which includes #3-SAT at j = m. Its crossover point is about 2^{420} clauses at clause density one for the bound in m, and about 2^{8.6·10⁹} variables for general 3-SAT in n.
- Dias–Lima, https://arxiv.org/abs/2611.00517 (abstract read): the OpenAI bound beats 2^n only for astronomically large n. MIT Hardness Group, https://arxiv.org/abs/2611.02650 (abstract read): ETH is false, but SH is equivalent to the Weak ETH (no 2^{n^{1−ε}}), and the counting analogues are equivalent too. Wu–Wang, https://arxiv.org/abs/2611.02560 (abstract read): circuit lower bounds derived from the subexponential counting.
- Classical: Kutzkov 2007, #3SAT in O(1.6423^n) (cited secondhand; paper not accessed). Kutzkov, "Complementary Branching for #SAT: Bounded-Degree Bounds and Faster #3-SAT", IJCAI 2026, pp. 2282–2290, https://doi.org/10.24963/ijcai.2026/254 (**abstract read** on ijcai.org): "improve the best known deterministic upper bound for #3-SAT to O*(1.637^n)", and O*(2^{αn}) with α < 1 for sparse CNF.

So the best claimed exact #3SAT time is 2^{n/(log n)^{1/2+o(1)}} (unrefereed) and 2^{Θ(n)} published. The hypothesis this route needs, no 2^{(2+δ)√(3 n log₂ n)} algorithm for a fixed δ > 0, is far below all of these, and no known algorithm contradicts it. Quasi-linear SAT would give much more than the October algorithms: 2^{O(√(n log n))} against 2^{n/√log n}.

## 4. The three standard tests

(a) **Fast solver for the hard family?** None is known for #3SAT below 2^{n^{1−o(1)}} (Section 3). This note claims no lower bound; it is an upper-bound transfer.

(b) **2-SAT?** The argument needs a solver for a problem that is NP-complete under quasi-linear reductions, because the verifier runs are compiled into 3-CNF. A linear-time 2-SAT solver strips nothing, so the argument cannot "show" that 2-SAT is not quasi-linear. Passed. (#2SAT is #P-complete, and the integer game works for it, so a #2SAT lower bound of 2^{n^{1/2+ε}} would also suffice.)

(c) **Journal oracle.** The implication is consistent with the oracle worlds. Its conclusion holds in the multilinear-clock world below, because the alternating collapse there already gives it. A relativized version of the stripping proof itself, for example with CircuitSAT^A in the p = 1 world of the relativized-clock note, was not checked. The *hypothesis* fails relative to a PSPACE-complete oracle with its multilinear extension. That is the Aaronson–Wigderson collapse cited in the multilinear-oracle note, and it already suffices for any superpolynomial counting bound, since #P^{Ã} ⊆ FPSPACE ⊆ FP^A. It also fails relative to the journal's linear-clock oracle of the multilinear-oracle note. There, alternating linear time with unbounded alternation, even with extension queries, sits inside DTIME^A[O(n)]. The s = 1 game is a polynomial-time alternating computation for each bit of #3SAT, so after padding #3SAT ∈ FP^A. Any proof of the needed counting lower bound must therefore be non-relativizing, and non-algebrizing in the Aaronson–Wigderson sense. It also implies FP ≠ #P, hence P ≠ PP and P ≠ PSPACE. (P ≠ NP already implies these three consequences. The needed bound follows from the same lower bound for deciding 3SAT, and is not known to follow from P ≠ NP.) [Relativized clock](relativized-clock.md) · [Multilinear oracle](multilinear-oracle-clock.md)

## 5. Exact obstruction and next step

The chain stops at a missing statement: for some fixed δ > 0, #3SAT on n variables with O(n) clauses is not computable within 2^{(2+δ)√(3n log₂ n)} for all large n, on the RAM with w = Θ(log T). For the quasi-linear target the statement is #3SAT ∉ 2^{O(√(n log n))}. It is an exponential-type deterministic lower bound for a counting problem. It is non-relativizing and non-algebrizing, it implies P ≠ PP, and it is not known to be implied by P ≠ NP. The route trades the target for a stronger open lower bound. By the lemma it implies the target, and it also implies P ≠ PP, which the target is not known to imply. It does not shorten the distance, and it gets past none of the recorded barriers. The stronger counting Weak ETH (no 2^{n^{1−ε}} for any ε > 0) already suffices. [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)

The route has a floor: it can never require hardness below 2^{Θ(√n)}. Even if each block were stripped at a constant factor K instead of a polylog factor, the exponent would be n/k + 2k·log₂K, which is minimised at 2√(2n log₂K) = Θ(√n). Constant-factor stripping would remove only the √(log n), so no hypothesis weaker than "#3SAT needs 2^{ω(√n)}" can come out of this route. Constant-factor stripping through SAT compilation would need t-step runs compiled into O(t)-bit DIMACS. With local access, that is the journal's compiler criterion, which already excludes linear SAT on its own. Constant-factor stripping could also come directly from NTIME_RAM[t] ⊆ DTIME_RAM[O(t)], with no DIMACS step. [Compiler criterion](compact-compilers-and-linear-sat-time.md)

Concrete next lemma: decide whether the per-block factor can drop from L^{3+c} to L^{c+o(1)}. One candidate is to feed the level-i instance to S as a *succinct* formula that S reads virtually. That would only improve the constant (a = 3+c → c+ε). Otherwise the route reduces to the clean implication "counting Weak ETH ⇒ no quasi-linear SAT", which belongs among the statements that would suffice.

## 6. What is not proved

- No lower bound of any kind.
- Overlap: the O-form of the lemma, its contrapositive and Section 2f follow directly from bound (1) of the linear-quantifiers note, applied to the O(n + log ℓ)-space enumeration algorithm for each bit of #φ (compare the checkpoint-pullback note). New here: the explicit leading constant 2√(3+c), obtained from the packed reduction and DIMACS writing; the exact count-splitting presentation; and the oracle remarks. Priority outside the journal is not established.
- Depth-uniform constants at k = Θ(√(n/log n)) and exponential instance sizes are supported by the formula-level elimination of the linear-quantifiers note, which is stated for a growing number of blocks. The native-verifier version is an extension of the alternating-speedup note made here. Both are checked by reading, not formally.
- The October 2026 claims are unverified. Only the OpenAI abstract and theorem statement were read, and the Anthropic paper was not accessed.
- The scripts check game exactness only for n ≤ 12 and q ≤ 7.

## Reproducing the checks

Run from `audits/`:

```
python3 count_splitting_game_check.py
python3 count_splitting_algebraic_extra_cases.py
```
