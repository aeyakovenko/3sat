# Inside the linear-SAT reductio, description-first games fail on one hard-table opponent

Inside the proof by contradiction from linear SAT, every game whose first block is a description of memory with a deterministic word decoder fails on one fixed opponent built from the hard-table note: E·L⁴ + d·L⁶ ≥ εt for first-block length E and maximum lookup time d. This violates the two-block budget (n+s+b)·L⁶ = o(t) of the alternation note, exactly in d against s and with margin L² in E against b. Built directly from a native solver the bound is E + d ≥ t/C. So description-first games are dead inside the reductio. This excludes nothing that the criterion's contrapositive does not already exclude on each game's own cylinder: what is new is a single opponent that does not depend on the game, and a bound on descriptions that needs no game. Four corners stay open: one-block games, bit decoders that never fetch a word, first blocks that are not descriptions, and decoders that are not deterministic. The proofs are at manuscript level and only the exponent arithmetic is scripted; this is not progress on the target, and the linear, quadratic and cubic questions remain open. [Hard tables](output-linear-hard-tables.md) · [Alternation criterion](alternating-native-speedup.md)

## Notation and the compiler facts used

- k is the SAT time exponent (H_SAT^k: SAT ∈ DTIME_RAM(O(N^k))), j the number of blocks, t the diagonal J's clock (t = n² in the journal's statements), and L = Θ(log t). Constants depend on the solver, the universal evaluator and the fixed verifier, never on the game.
- **(C1)** A nondeterministic RAM run with clock H has a virtual explicit 3-CNF of O(H·L³) bits. [Packed band transfer](packed-band-transfer.md)
- **(C2)** A run with R native steps and m public read-only words has a materialized 3-CNF of O(R·L³ + m·L²) bits, that is, L bits per public bit, written in the same time plus poly(L). [Materialized input census](materialized-input-census.md)
- **(C3)** Touch-predecessor authentication: constantly many trace rows witness any defect of a claimed trace (hard-table note, first section; its rank induction is Lean-checked). [Lean: touch predecessors](../lean/TouchPredecessors.lean)

## 1. Description-first games

Fix a deterministic decoder program Dec. Let M be a j-block alternating procedure for J, and let x be an input whose prefix is an opponent p. M is *description-first* on x if:
- **(D1)** the first block is existential, and its choices include a string C consumed before the first switch;
- **(D2)** if M accepts x, then for some string C that the existential player can consume as its first block, Dec(x, C, a) returns the word at address a of the simulated opponent's memory at one fixed time τ₀ of the opponent's scan phase, for every address a of the table region; write E = |C| and d = max_a (steps of Dec(x, C, a));
- **(D3)** each such lookup is executed on some path.

Then (D1) gives b ≥ E when j ≥ 2, since b is a maximum over all paths, and (D3) gives s ≥ ρ_path·d, with ρ_path = 1 for word lookups.

Condition (D2) is weak. A store-log code, a snapshot description and a seed chart each give it, because no table word changes during the scan. The address-sorted store-log certificate of the round-two access-log entry satisfies (D1)–(D3), with E at most its cap and d = O(d_rec·log T), the predecessor search its own branches also pay. [Round-two attempts](parallel-proof-attempts-of-27-november-and-why-each-stopped.md) More generally, a two-block game whose universal branch names a scan step and then deterministically computes a word from (x, first block), and which accepts only when every such word is the true loaded word, is description-first, with d at most its branch length.

## 2. The opponent p\*

p\* exists under H_SAT^k. It is built from the solver S, a fixed universal code-and-data evaluator Ev_U and the fixed verifier V of the hard-table proof, and it does not depend on the game. On any input of length n:
1. Compute t from n. Take n₀ maximal with c_opp·T(n₀^D) ≤ t and set h = n₀^D, with D > k. Here T(h) = ⌈C·N^k⌉, and N = Θ(h·L³) is the length of the source formula F for V on x_V (V's code padded to n₀ bits), by (C1). Then T(h) = Θ(t), because T((n₀+1)^D)/T(n₀^D) → 1.
2. Simulate S on F and write its touch-annotated trace into a fresh bank: T+1 rows of r = O(1) words each.
3. Scan the bank once in address order, XOR-accumulating every word, and compare with the XOR accumulated while writing. Reject on equality, which always holds; accept otherwise.

The total is at most t simulated steps, so J(x) = 1 on every long extension of p\*. This is essentially the constant-verdict program of the hard-table note's section "Testing the predictor even when the last writer is given for free", with three changes: the touch-annotated trace replaces the packed table, the verdict is "reject", and the program is placed as an opponent prefix of J. An opponent that outputs a bit at an index taken from the padding would force nothing: a strongly sound description game is automatically right wherever that bit makes J(x) = 0, and the criterion lets the game choose its good extensions.

**Hosting S.** T = Θ(t) needs constant overhead per step of S. p\* runs at J's width 12⌈log₂(n+2)⌉, while S runs on N ≤ t = n² bits, so its width is at most twice that and its addresses are sparse. The fixed-depth radix trie of the native band note (digits of ⌊(log₂ n)/4⌋ bits, constant depth because the widths differ by a bounded factor) holds S's memory and the last-touch index of each address, and arithmetic uses O(1) limbs. [Native band](native-unary-clock-band.md)

**Native opponent (under H_U, a linear-time solver A for the native language).** The same program with A in place of S. The source is the native instance F = (V, x_V, 1^h), with n₀ = ⌈h^{1/2}⌉ and h maximal such that the opponent fits in t steps; A's trace on F is padded with idle halts to T = ⌈κ|F|⌉ rows, as the hard-table note pads to its clock, so T = Θ(h) = Θ(t).

## 3. The lemmas

- **Lemma 2 (extraction).** If Dec(x, C, ·) answers every table lookup within d steps, then z = (code of Dec, C, x, τ₀, base, r) is an Ev_U-evaluator of the trace with |C| + n + |Dec| + O(log t) bits and c_U·d + O(|Dec|) steps, where c_U depends only on Ev_U. Ev_U interprets Dec step by step with a uniform constant, holding its sparse memory in the fixed-depth trie, so adaptive decoders cost nothing extra. The added terms are constants of the game and of lower order.
- **Lemma 1 (SAT form).** Under H_SAT^k, every Ev_U-evaluator (z, q) of the genuine trace, with z of s bits, satisfies s·L + ρ·q·L³ ≥ ε·h^{1/k} − n₀·L, with ρ = 1 for word queries and ρ = Θ(L) for bit queries. With T = Θ(t): s ≥ ε′·t^{1/k²}/L^{1+3/k} or q ≥ ε′·t^{1/k²}/(ρ·L^{3+3/k}).
- **Lemma 1′ (native form).** Under H_U, s + ρ·q ≥ h/C − n₀; with h = Θ(t), s ≥ t/C′ or ρ·q ≥ t/C′.
- **Lemma 3 (refined driver charge).** Under H_SAT^1, a j-block game for J with s·L^{3j} + (b+n)·L^{3j−2} = o(t) on good extensions of every prefix contradicts the diagonal. The alternation note's form (n+s+b)·L^{3j} = o(t) implies it.
- **Theorem (exclusion).** Under H_SAT^1, every description-first game with a word decoder that is correct on a long extension of p\* has E·L⁴ + d·L⁶ ≥ ε·t there. This violates the refined budget, and hence the journal's, at j = 2: against the journal's form it is exact in d versus s, with margin L² in E versus b, and at j ≥ 3 the margin is L^{3j−6} against both forms. Under H_U, E + d ≥ t/C, which violates the journal's native form s + b = O(t/log^ε t), and also the o(t) form for a fixed number of blocks and the t/K form, neither of which is a journal statement.

**Proof of Lemma 1, with every power of L.** Start from the hard-table note's "One SAT call for an error in an indexed table"; the only change is that the defect computation reads each of its O(1) rows by r word queries to Ev_U, not by O(log h) bit queries.
- The defect computation has public input x_V and z, that is m = (n₀ + s)/L + O(1) words, and clock R = O(q + poly(L)), covering the evaluator calls, the instruction check against F (whose words come in O(1) after poly(L) setup), the endpoint checks and the predecessor check. By (C2) the defect formula has ℓ = O(q·L³ + (n₀ + s)·L + poly(L)) bits and is written in that time.
- No power of L hides in the decoder: the defect run is compiled at a width W = Θ(L) that covers Dec's width, and the decoder's addresses are data in routed records, so each decoder step costs O(L³) bits whatever its address, and ρ = O(1) for word lookups.
- The honest branch guesses z in O(s/L) word steps, writes the formula in O(ℓ) and makes one SAT call in O(ℓ^k). If q·L³ + s·L ≤ ε·h^{1/k} for small ε, the branch would signal inside the source clock h, which the note's diagonal forbids: F is unsatisfiable and V never signals in time. So q·L³ + s·L > ε·h^{1/k} − O(n₀·L).
- With bit queries R = O(L·q), and the q term becomes q·L⁴. The source has N = Θ(h·L³) bits by (C1), so T = Θ((h·L³)^k) = Θ(t) and h^{1/k} = Θ(t^{1/k²}/L^{3/k}).

The hard-table note leaves its exponents free ("L^{O(1)}"); (C2) fixes them. The circuit-model exponents, 2 + 3/k + 1/k², are already in the tight-lookup note, and the script below re-derives them as a check. A circuit route for the decoder is not used: a d-step decoder with adaptive reads into a hardwired E-bit string becomes O(d·(E + L²)) gates by multiplexers, a product rather than (E + d)·polylog, and no known simulation gives (E + d)·polylog for adaptive decoders. The RAM-evaluator form makes it unnecessary. [Tight lookup](tight-hard-table-lookup.md)

**Quantifier order.** The criterion needs one prefix per game. The hard-table construction may depend on the evaluator, and here Ev_U is fixed, so p\* does not even depend on the game; the bound holds at every large h, so on every long extension. At k ≥ 2, J runs at clock t = n^c with c > k² for the hard table and c > k^j for the derived criterion, and x is folded into the advice.

**Lemma 1′** repeats the argument with native instances: the source is F = (V, x_V, 1^h), the defect query is G = (Def, (x_V, z, params), 1^τ) with τ = O(q + L), A on G takes κ|G| steps, and V runs A at A's wider width with O(1) limbs and the fixed-depth trie. So s + q > h/C − n₀, with no logarithm anywhere. It is a routine instance of the native band note's template "Where a further speedup would have to enter" (a first message of o(H) bits, then o(H) native steps), applied to the hard-table diagonal. Routing H_U through H_SAT instead pays L³ twice, which is where a native window would appear; it is an artefact.

**Lemma 3.** Run the alternation note's driver but compile each child query by (C2). The innermost child (clock O(s), public n + b bits) costs O(s·L³ + (n + b)·L); each outer level multiplies by L³ and adds its own public bits at L each. The total is O(s·L^{3j} + (n + b)·L^{3j−2}), at j = 2 s·L⁶ + b·L⁴ + n·L⁴. Only the cost is re-derived, not the full driver with its two caps and the two-default test. [Lean: driver cutoffs](../lean/AlternatingNativeCutoffs.lean)

## 4. The exponent table

`description_first_exponent_table.py` tracks exponents of t and L, symbolically (sympy) for the structural identity and with fractions for the table. "Refined" is Lemma 3's budget and "crude" the alternation note's (n+s+b)·L^{3j}; "c0" is in M-notation (bound M^{1/k²}/m^{c₀}, with M = t·L table bits). Key lines (blocks B for the native and k = 2, 3 rows are omitted; they give the same five verdicts):

```
symbolic check (r = 0):
  d* - s_budget = 0
  s* - b_budget = 0
  d* - s_budget (general r) = -logL*r
setting    advice s*          word d*            bit d*             c0(s)  c0(q,word)  c0(q,bit)  c0(circuit, tight note)
native k=1 t^1 / L^0          t^1 / L^0          t^1 / L^1          1      1           2          -
SAT k=1    t^1 / L^4          t^1 / L^6          t^1 / L^7          5      7           8          6
SAT k=2    t^1/4 / L^5/2      t^1/4 / L^9/2      t^1/4 / L^11/2     11/4   19/4        23/4       15/4
SAT k=3    t^1/9 / L^2        t^1/9 / L^4        t^1/9 / L^5        19/9   37/9        46/9       28/9
SAT k=1: refined budget b = o(t^1 / L^4), s = o(t^1 / L^6); crude s+b = o(t^1 / L^6)
   advice  E vs b-budget        : excluded
   word d  vs s-budget          : excluded
   bit d, path pays one bit     : NOT excluded (window L^1)
   bit d, path pays a full word : excluded
   min(E*,d*) vs crude s+b      : excluded
  j=1: s-budget o(t^1 / L^3); path >= min(E/L, d) >= t^1 / L^6: NOT excluded (window L^3)
  j=2: b o(t^1 / L^4) -> excluded;  s o(t^1 / L^6) -> excluded;  crude s+b o(t^1 / L^6) -> excluded
  j=3: b o(t^1 / L^7) -> excluded (margin L^3);  s o(t^1 / L^9) -> excluded (margin L^3);  crude s+b o(t^1 / L^9) -> excluded (margin L^3)
  hard table (word): E + d >= t^1 / L^0  -> excluded for every fixed j >= 2 and every eps > 0
```

| SAT exponent | c₀ (advice / word lookup / bit lookup) | bound on the opponent | native criterion: journal form O(t/log^ε t); also the o(t) and t/K forms (not journal statements) | SAT criterion: journal form (n+s+b)L^{3j} = o(t); refined form of Lemma 3 |
|---|---|---|---|---|
| native (H_U) | 1 / 1 / 2 | E + d ≥ t/C | **excluded**, all three forms (C independent of the game) | n/a |
| 1 | 5 / 7 / 8 | E·L⁴ + d·L⁶ ≥ εt | n/a: under H_U the native row applies | **excluded** at j = 2: refined form exact in both coordinates; journal form exact in d versus s, margin L² in E versus b; margin L^{3j−6} at j ≥ 3; bit decoders keep a one-L window unless the path fetches a word |
| 2 | 11/4 / 19/4 / 23/4 | E·L^{5/2} + d·L^{9/2} ≥ ε·t^{1/4} | n/a | the journal's linear criterion excludes nothing; a derived SAT² criterion is matched exactly |
| 3 | 19/9 / 37/9 / 46/9 | E·L² + d·L⁴ ≥ ε·t^{1/9} | n/a | the journal's linear criterion excludes nothing; a derived SAT³ criterion is matched exactly |

**Why the match is exact.** The hard table's trace is S's run on a source of clock h, which costs one L³ and one power k; the defect call costs a second L³ and a second power k. The refined two-block driver's two levels are the same two compilations, so the decoder threshold equals the refined s-budget and the advice threshold equals the refined b-budget, for all compiler exponents and every k (the symbolic check). The alternation note's cruder charge puts b at L⁶ instead of L⁴, which is the margin L². Improving the compiler moves both sides equally.

## 5. What the exclusion adds

Inside the reductio it excludes nothing new: the alternation criterion's contrapositive already defeats every game within the journal's budget on its driver's own cylinder, and Lemma 3's contrapositive does the same for the refined budget. The exclusion is not derived from that contrapositive; it uses V's diagonal, through the hard-table note, and Lemma 3 enters only to compare budgets. What it adds:
1. **One cylinder for every game.** A single cylinder p\*, depending only on S, Ev_U and V, defeats every description-first game with every decoder, on every long extension. The uniformity is the hard-table theorem's own quantifier order: one table against every evaluator of a fixed universal Ev_U.
2. **A bound that needs no game.** It bounds descriptions of p\*'s run. A description with E·L⁴ + d·L⁶ = o(t) contradicts H_SAT^1 by itself, through the hard-table note, so for this class the game and the criterion add nothing to the hard-table route. This is obstacle 5 of the barrier note (the hypothesis turns against you) at exact precision. [Barriers](what-any-proof-of-superlinear-sat-time-must-get-past.md)
3. **Exactness.** Against the refined budget the exponents leave no slack at j = 2; against the journal's budget the slack is L² in E versus b and none in d versus s; at j ≥ 3 the margin is L^{3j−6}.

## 6. Where one power of L could hide

Three places could each cost an extra power of L. All three were checked during review at manuscript level, each resting on journal mechanisms proved on paper, so the claim that there is no window at k = 1 with two blocks survives.
- **Hosting S inside p\*** at O(1) cost per step. The width ratio is at most 2 at k = 1, because n² + 2 ≤ (n+2)², and S's sparse addresses go through the native band note's fixed-depth radix trie, whose depth is a constant (about a hundred levels of ⌊(log₂ n)/4⌋-bit digits), with fresh rows needing no initialization and the last-touch index stored at the leaf.
- **ρ = O(1) for the decoder inside the compiled defect run.** (C2) lets the compiler choose W = Θ(L) large enough to cover the decoder's width, and memory consistency inside the formula comes from routing records whose addresses are data, so no trie is needed there.
- **Hosting S inside V during the honest branch,** which the accounting above assumes: the SAT call must take O(ℓ^k) of V's own steps inside the source clock. It holds by the width headroom of the packed-band note, or by the same trie at width ratio D/k.

What would break it: a binary trie, a balanced search tree, or the trie "with polylogarithmic overhead" offered in the hard-table note costs Θ(L) per access and opens the one-L window at two blocks; bit-serial decoding is the bit form, corner 2 below. The construction uses none of them. The margins at j ≥ 3 would survive any of these losses.

## 7. The three standard tests

- **(a) Does the hard family have a fast globally correct solver?** Yes: J is constantly 1 on the cylinder of p\*. The result bounds descriptions of one conditional run and games of one syntactic class; it is not a time lower bound.
- **(b) The same bound for 2-SAT?** No. Linear-time 2-SAT, which is true, yields no hard table: the source and defect formulas encode nondeterministic RAM runs and are not 2-CNF.
- **(c) Does it survive the oracle of the relativized-clock note?** No, and no false relativized statement results. The proof uses that one instruction reads O(w) bits in the same two places the criterion uses: in (C1) and (C2) an oracle step does not compile into O(L³) bits, and in (C3) a Θ(n log n)-bit oracle read is not authenticated by O(1) rows. [Relativized clock](relativized-clock.md)

## 8. The open corners

1. **One-block games.** The window is [t/L⁶, t/L³]. These games have no universal check of the description, and p\* is built against two levels of elimination, so a one-level opponent would be needed.
2. **Bit decoders whose paths never fetch a whole word through the decoder.** One power of L remains. By the tight-lookup note's "elementary obstacle", a generic touch test must probe Θ(L) address bits, so closing this window needs a different test, not a sharper count.
3. **First blocks that are not descriptions.** Games that commit less than a description in block 1 (recursive or Dymond–Tompa-type games); the margin L^{3j−6} at j ≥ 3 says such games must commit strictly less than a description per block.
4. **Decoders that are not deterministic programs.** A description decodable only with a guessed witness (for single-valued nondeterministic decoders, Lemma 1 seems to extend by guessing the witness inside the defect formula; a sketch made during review, not checked), or a lookup resolved by later quantifier blocks, which would need another SAT call in the argument and with it another L³ and another power k (also a sketch).

No further lemma is recommended on this line: games that commit to memory and then replay it (store-log certificates, snapshot descriptions, seed charts used as a first block) are excluded inside the reductio.

## 9. What is not proved

- **Inherited without re-verification:** the source, diagonal and padding of the hard-table note; the O(R·L³ + m·L²) count of (C2) and its construction time; the O(H·L³) count and width headroom of the packed-band note; the width and trie simulation of the native band note; the access-log certificate's soundness. The two Lean files cover only the rank induction of (C3) and the two-default cutoff identity of the driver.
- **On paper only:** the word-query form of Lemma 1, Lemma 1′, the refined driver charge (cost only), the k = 2, 3 criteria, the class definition (D1)–(D3), and the claim that the access-log certificate and commit-then-replay games satisfy it. The three places of Section 6 were checked during review at manuscript level, not formally.
- **Scope of "exact" and "excluded".** "Exact" means equal exponents of t and L; "excluded" means the bound's Ω(·) against the criterion's o(·), with constants depending on the solver, Ev_U and V.
- **Not addressed:** the four corners of Section 8.

## Reproducing the check

Run from `audits/`: `python3 description_first_exponent_table.py` (under a second; it needs sympy).
