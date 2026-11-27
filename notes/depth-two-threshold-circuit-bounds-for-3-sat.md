# Depth-two threshold circuits for proper 3-SAT need about N^{3/2} gates and N^{5/2} wires

At infinitely many lengths N, roughly squared apart, every depth-two threshold circuit (LTF∘LTF) that decides satisfiability on all proper ASCII DIMACS 3-CNF files of N bits has Ω(N^{3/2}/log³N) gates and Ω(N^{5/2}/log^{7/2}N) wires. This follows from Kane and Williams' published theorem for Andreev's function and the journal's copy projection of Andreev's function into 3-SAT, with explicit length ratios. The same bounds hold at every sufficiently large length via a rerun of Kane and Williams' proof that is checked against their text but not published; their published statement alone gives only exponents 3/4 and 5/4 at every length. This is a circuit bound only and has no RAM-time content: all three standard tests below come out against it as a RAM argument, and Andreev's function is itself computable in linear time. Priority for the SAT corollary is not established. The linear, quadratic and cubic questions remain open.

**Statements obtained.** Throughout, c_g, c_w > 0 are absolute constants, as in (KW), §1. In statements 1 and 3 they come from Kane–Williams' unspecified Ω-constants; in statement 2 they are the constants of the rerun of KW's proof (§2, step K). Only the length ratios are explicit. "Circuit" means LTF∘LTF: one hidden layer of arbitrary-weight threshold gates, a threshold output, and input-to-output wires allowed. It must decide satisfiability on all proper ASCII DIMACS 3-CNF files of N bits.
1. **From the published theorem, no padding (the safe statement).** Take any r = 2^j ≥ max(8, k₀) and the single byte-aligned length N = N_r. These lengths satisfy 32·2^r ≤ N_r ≤ 1859.06·2^r; for example N₈ = 354,312 and N₁₆ = 63,357,408. Every circuit has at least c_g·(N/1859.06)^{3/2}/log₂³N gates and at least c_w·(N/1859.06)^{5/2}/log₂^{7/2}N wires. At these lengths the source is exactly KW's A_n with n = n_src = 2^{r+1}. The lengths occur infinitely often but are roughly squared apart.
2. **For every sufficiently large byte-aligned N, from a rerun of KW's proof (not their published statement).** Rerun the proof with blocks of ⌊2^k/k⌋ (§2, step K; checked against the text, not published), and pad with spaces inside the last clause line (finite check in §2). Then every circuit has at least c_g·(N/3718.12)^{3/2}/log₂³N gates and at least c_w·(N/3718.12)^{5/2}/log₂^{7/2}N wires.
3. **From the published theorem plus padding only.** Let r₀ be the least power of two ≥ max(8, k₀). For every byte-aligned N ≥ N_{r₀}, pad from the largest power of two r with N_r ≤ N. This gives only c_g·(N/1859.06)^{3/4}/log₂³N gates and c_w·(N/1859.06)^{5/4}/log₂^{7/2}N wires, because N < N_{2r} ≤ 1859.06·4^r.

The same bounds hold for MAJ∘MAJ.

## Sources

- D. M. Kane, R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits*, arXiv:1511.07860v1 (24 Nov 2015; the only arXiv version), https://arxiv.org/abs/1511.07860. **Read in full** (text pp. 1–17, extracted with pypdf; reference list skimmed). STOC 2016 version **not accessed**. Page numbers below are the printed ones (PDF page minus one).
- R. Williams, *Some Open Problems Regarding Lower Bounds For NP*, https://www.cs.umd.edu/~gasarch/open/lbfornp.pdf (4 pages; cited by the journal's formula note). **Read**: p. 2 (the "Boolean Formulas" and "TC0 Circuits" paragraphs, Problems 2–3) and its [KW16] reference entry. The rest was **not read**.
- Journal, read: [Formula and branching-program size](formula-and-branching-program-size-of-sat.md) · [andreev_dimacs_projection_audit.py](../audits/andreev_dimacs_projection_audit.py) · [dense_ascii_chunk_circuit_audit.py](../audits/dense_ascii_chunk_circuit_audit.py) · [Relativized clock](relativized-clock.md)
- No search for later improvements of the KW bounds was made.
- **Priority** for the SAT corollary is not established.
  - KW do not state it. Their only lower-bound statement about SAT is Allender–Koucký's uniform result (p. 7). Their §7 also asks about SAT algorithms for LTF∘LTF circuits, which is a different question.
  - Williams' open-problems column puts KW16 next to its Problem 3 on p. 2: "Prove that SAT requires LOGTIME-uniform depth-three MAJORITY/NOT circuits of n^{2.5+ε} wires, for some ε > 0". In the preceding paragraph it derives the formula bound for SAT "by tight reductions". Both quotes were checked against the PDF.
  - The column does not state the depth-two SAT corollary. A reading, not the column's statement: a threshold of n^{2.5+ε}, just above KW's wire exponent, suggests the author treats about n^{2.5−o(1)} as what tight reductions already give for SAT.
  - What is new here is at most the explicit physical-length constants and log factors.

## 1. The lemma chain

Lemma chain, with quantifiers:
- (KW: published for k a power of two, where b = 2^k/k; for other k, by rerunning KW's proof, §2 step K) There are absolute c_g, c_w > 0 and k₀ such that for every k ≥ k₀, every LTF∘LTF circuit computing Andreev's function A^{(k)} exactly has ≥ c_g·2^{3k/2}/k³ gates and ≥ c_w·2^{5k/2}/k^{7/2} wires. Here A^{(k)} has a table of 2^k bits and k blocks of b = ⌊2^k/k⌋ bits, and its address bit i is the parity of block i.
- (P) For every r ≥ 8, with m = ⌊2^r/r⌋ and h = the largest power of two ≤ r/8, the journal's encoder is a map π_r from {0,1}^{n_src} to N_r-bit files, n_src = 2^r + rm. Every output bit is a constant or a copy of one source bit. Every image is a proper ASCII DIMACS 3-CNF, and SAT(π_r(x)) = A^{(r)}(x) up to a fixed relabeling of the inputs.
- (S) Substituting such a π into an LTF∘LTF circuit increases neither the gates nor the wires.
- (L) There are explicit constants κ, κ′ with 16·n_src ≤ N_r ≤ κ·n_src and N_{r+1} ≤ κ′·n_src(r).

## 2. The steps

### K. The primary source, exactly

- **Model** (p. 1, p. 4). An LTF is [Σ aᵢxᵢ ≥ t] with real weights. LTF∘LTF means bottom LTF gates on the inputs plus a single output LTF. The output gate "can take in input variables as well as outputs of previously computed LTFs". The proofs count gates as the number of LTF gates, and wires as connections: a bottom gate "with u wires" has fan-in u. MAJ∘MAJ (polynomial integer weights) is a special case.
- **Andreev's function** (p. 1). n = 2·2^k. x ∈ {0,1}^{2^k}, blocks a_{i,1..2^k/k} for i = 1..k, and A_n = x_{bin(p₁…p_k)} with p_i the parity of block i. The paper adds: "(For simplicity we may think of k itself as a power of two…)". The proof (p. 11) writes x ∈ {0,1}^{n/2} and "k := ⌊log₂ n⌋". That is inconsistent with n = 2·2^k by one, and harmless.
- **Theorem 1.1** (p. 2). "Any function f that agrees with A_n on at least a (1/2+ε)-fraction of inputs for some ε ≫ √(log(n)/n) cannot be computed by LTF∘LTF circuits with fewer than Ω(ε³n^{3/2}/log³(n)) gates or fewer than Ω(ε³n^{5/2}/log^{7/2}(n)) wires." Exact computation is ε = 1/2, which gives **Ω(n^{3/2}/log³n) gates and Ω(n^{5/2}/log^{7/2}n) wires**, with n = 2·2^k the total input length. The constants are not given.
- **Where the logs come from** (proof, pp. 11–12):
  - A random k-bit function needs Ω(2^k/k²) depth-two gates (Cor. 2.1/2.2, by counting with Roychowdhury–Siu–Orlitsky).
  - A random restriction that leaves one free bit per block leaves a bottom gate unforced with probability O(|P|/√n) = O(log n/√n) (Lemma 1.1, Littlewood–Offord). A gate with u wires survives as a non-single-input function with probability O(u·|P|^{3/2}/n^{3/2}) (Lemma 3.1).
  - Gates: s·log n/√n ≳ n/log²n. Wires: w·log^{3/2}n/n^{3/2} ≳ n/log²n.
- **Other results.**
  - Cor. 1.1: an ε-approximate majority of LTF∘LTF for A_n needs the same Ω(ε³…) bounds.
  - Thm 1.2 (upper bounds): A_n has uniform depth-3 MAJ∘MAJ∘MAJ circuits of **O(n) gates**, LTF∘LTF circuits of O(n³/log n) gates, parity decision trees of depth log₂n, and MOD3∘MOD2 circuits of size O(n²).
  - Thm 1.3: MAJ∘LTF∘LTF bounds o(n^{3/2}/log³n) gates or o(n^{5/2}/log^{7/2}n) wires. This is for a **different** function, B_n (an ε-biased code with m ≈ n^{16} rows and k = 16 log₂n parity blocks), not Andreev.
  - Thm 1.4 (PARITY, 99% agreement): Θ(√n) gates and Θ(n^{3/2}) wires.
  - So for Andreev, KW give depth-two and approximate-majority-of-depth-two bounds, plus one restricted depth-three corollary: no TC⁰₃ circuit of O(n^{1.1}) gates whose output gate has fan-in o(n^{2/15}) (pp. 2, 12). Superlinear gate bounds at depth three are impossible for A_n, because Thm 1.2 gives O(n)-gate MAJ∘MAJ∘MAJ circuits (KW p. 12).
- **General k (a rerun of KW's proof, not their published statement).** The proof uses three things:
  - Cor. 2.1/2.2 for k-bit functions, with no divisibility condition.
  - Lemmas 1.1/3.1 for a partition into |P| = k parts *of equal size*. k rows of b = ⌊2^k/k⌋ bits satisfy this. The bounds become O(k/√(kb)) = O(k/2^{k/2}) and O(u/b^{3/2}) = O(u·k^{3/2}/2^{3k/2}), using b ≥ 2^k/k − 1.
  - The restricted function is f(y₁⊕c₁,…,y_k⊕c_k), and negations are free.

  So KW's proof (not their published statement) gives the bound ≥ c_g 2^{3k/2}/k³ gates and ≥ c_w 2^{5k/2}/k^{7/2} wires for every k ≥ k₀ with blocks of ⌊2^k/k⌋. It uses Lemmas 1.1 and 3.1 with n := k·b and |P| := k, and Cor. 2.1 with k variables. For ε = 1/2 the proof simplifies: fix x to a k-bit function with no LTF∘LTF circuit of c·2^k/k² gates. Some ρ leaves at most the expected number of nontrivial bottom gates. Trivial gates fold into the top gate as constants or direct wires.
  - Why this is needed: with k restricted to powers of two, the admissible lengths are 2^{2^j+1}. These are squared apart, and whitespace padding cannot fill such gaps with a bounded loss. Padding from them halves the exponents, to 3/4 (gates) and 5/4 (wires); see "Resulting bounds".

### P. The projection

The audit [andreev_projection_copy_audit.py](../audits/andreev_projection_copy_audit.py) contains verbatim copies of the journal's `encode` (from [andreev_dimacs_projection_audit.py](../audits/andreev_dimacs_projection_audit.py)) and `bank_name` (from [dense_ascii_chunk_circuit_audit.py](../audits/dense_ascii_chunk_circuit_audit.py)); both of those modules import pycosat at load time. The proof below is for every (r, m, h) with h a power of two, log₂h ≤ r and h ≤ 2^r.
- **(iii) Copies.**
  - The only integer in the output that depends on the source is `lib = bank_name(bank, mask, h)` in `scalar()`. Its decimal string is the bank digit, 1 or 2, followed by `format(mask,'0hb')`, so it always has exactly h+1 digits. For t = 0, …, h−1, the binary digit in position t after the bank digit equals bit h−1−t of the chunk mask, which is one source bit, or a constant 0 in the padded tail of a short last chunk.
  - Each lib occurs in exactly two literals, `+lib` in (−c, lib) and `−lib` in (c, −lib), with fixed signs.
  - Everything else is independent of x:
    - fresh ids come from a counter whose call order depends only on (r, m, h);
    - the hole clauses range over [1, 3·10^h−1] minus the full set of 2·2^h mask names;
    - the units and lookups range over all masks;
    - the clause count and maximum id are fixed, so the header is fixed;
    - every line length is fixed.
  - So π(x) is a fixed template with each source bit printed as one ASCII digit at exactly two byte positions. The digit is '0' = 0x30 or '1' = 0x31, so it differs from the template only in bit 0, and that bit equals the source bit (positive copy). The other 7 bits of each such byte, and all other bytes, are constants.
- **(i) Properness.**
  - The 7 anchor clauses use three distinct anchors.
  - Every core gadget's literals are on distinct variables:
    - xor: three distinct allocations (the running parity, a chunk scalar of the same row, and the fresh output);
    - scalar: a fresh id and a mask name ≤ 3·10^h−1, below all fresh ids;
    - level tree: a fresh id, a level node and an address variable;
    - lookup: a leaf and a bank-2 name;
    - mux: a selector, two distinct table nodes and a fresh id;
    - hole: (−a₀, name, a₁) with name < a₀ < a₁.
  - Unit and binary core clauses are padded with anchors[0] and anchors[1], which occur in no core gadget except the holes (already ternary).
  - Every id 1..V occurs. A bank-1 name occurs in its unit. A bank-2 name occurs in its lookups (h ≥ 1 leaves). A hole id occurs in its hole clause. A fresh id occurs in its defining clauses.
- **(ii) Semantics.**
  - The 7 anchor clauses exclude every nonzero assignment, so a₀ = a₁ = a₂ = 0. Padding is then inert, and holes are satisfied.
  - The units force P_μ = parity(μ). The row scalars and XOR clauses force address[j] = parity of row j; zero padding does not change parity.
  - The root unit and the child clauses (child ↔ parent ∧ literal) make exactly one leaf true, the leaf ℓ = Σ_{j<log₂h} address[j]·2^j.
  - The lookups at that leaf force S_μ = μ_ℓ for all μ. Then table scalar c equals S_{ν_c} = x[ch+ℓ].
  - The mux nodes select chunk c* = Σ_{j≥log₂h} address[j]·2^{j−log₂h}, so the output is x[c*h+ℓ] = x[z] with z = Σ_j par(row_j)·2^j. The final unit asserts it.
  - So π(x) is satisfiable iff x[z] = 1.
- **Identification with KW.** x_t := T[t−1] and KW block i := journal row r−i give bin(p₁…p_k) − 1 = Σ_i p_i 2^{k−i} = Σ_j par(row_j)·2^j. So A_KW ∘ (relabeling) = SAT ∘ π. A different bit order in bin is another fixed permutation of the table inputs, which is also a copy map.

### S. Substitution

Let C be LTF∘LTF on y₁..y_N with s gates and w wires. Let each π_j(x) be one of 0, 1, x_{σ(j)} or ¬x_{σ(j)}.
- In every gate [Σ_j a_j y_j + Σ_g b_g g ≥ t], including the top gate's direct input wires:
  - constants fold into the threshold;
  - all copies of x_i merge into one weight Σ_{π_j=x_i} a_j − Σ_{π_j=¬x_i} a_j, with the threshold shifted accordingly.
- Each old input wire maps to at most one new wire, so no gate's fan-in increases. The gate set is unchanged, and bottom gates that became constant may be deleted.
- Hence C∘π is an LTF∘LTF circuit with ≤ s gates and ≤ w wires.
- A MAJ∘MAJ circuit (negated inputs and repeated wires allowed, wires counted with multiplicity) is an LTF∘LTF circuit with the same counts. Its image need not be MAJ∘MAJ, which does not matter because KW's bound is for LTF∘LTF.
- The device only has to be correct on proper files, and every π(x) is one.

### L. Length, with explicit constants

- **Closed forms.** Write n = 2^r, c = ⌈m/h⌉ and Λ = 3·10^h − 1 (the reserved name range). Then
  - V = Λ + r(2c−1) + 2h + 2n/h + 1,
  - C = Λ + (h−1)2^h + r(6c−4) + 6n/h + 6h − 1, with leading term 12·n/h clauses.
- **Per-line bound.** A line is Σ(digits + sign) + 5 bytes. Every mask name and anchor has h+1 digits, and every fresh id has ≤ D = digits(V). This gives a closed-form upper bound U(r) on the byte length. Its leading term is (n/h)(28D + 8h + 100) bytes, so U·8/n_src ≈ 112·D/h + 32 + 400/h. Asymptotically the true length is about (n/h)(28D + 8h + 84). That figure overshoots at moderate r, by about 10% at r = 16, because most ids there have D−1 digits.
- `python3 andreev_projection_length_bounds.py` takes a few seconds; its output (abridged to four rows of the r = 8..20 table and without the closing C/(n/h) lines):
  ```
  closed-form V, C and streamed byte length == encode() on 20 layouts; U >= length
  r  h  n_src        L_r(bytes)    N_r(bits)/n_src  U_r*8/n_src  C/(n/h)
   8  1        512          44289       692.02       876.47   12.008
  15  1      65528        7613763       929.53      1103.86   11.998
  16  2     131072        7919676       483.38       568.19   12.008
  20  2    2097136      145344109       554.45       624.01   12.000
  kappa = sup_(8<=r<=4096) N_r/n_src  <= 929.53  (exact for r<=20, U beyond)
  kappa' = sup_(8<=r<4096) N_(r+1)/n_src(r) <= 1859.06
  U-ratio over r in [2048,4096]: min 302.06, max 572.12
  asymptotic leading-term envelope 112*D/h + 32 with D/h in [8 log10 2, 16 log10 2): [301.72, 571.45)
  ```
  Measured: N₈ = 354,312 bits (n_src = 512) and N₁₆ = 63,357,408 bits (n_src = 131,072).
- **Tail r > 4096 (proved by estimate).**
  - V ≤ 8n/h, because 10^h ≤ 10^{r/8} < n/h. So D ≤ 0.30103r + 1.91.
  - h > r/16, so D/h < 4.8165 + 30.56/r < 4.824.
  - The lower-order terms (Λ ≈ 3·10^h lines, the 2h-node level tree, h·2^h lookups) are a factor 2^{−0.58r} smaller.
  - So N_r/n_src < 112·4.824 + 32 + 2 < 575 < 929.53, and N_{r+1}/n_src(r) < 575·2^{r+2}/(2^{r+1}−r) < 1151 < 1859.06.
- **Result.** For every r ≥ 8: 16·n_src ≤ N_r ≤ 929.53·n_src (the lower bound is two bytes per source bit; the maximum is at r = 15), and N_{r+1} ≤ 1859.06·n_src(r).
- **Asymptotics.** N_r/n_src does not converge, because h/r oscillates in (1/16, 1/8]. Its limit points fill about [302, 572]. Per table bit, N_r/2^r is asymptotically in about [604, 1143].

### Resulting bounds for 3-SAT

- **At the canonical lengths.** For r ≥ max(8, k₀), (KW)+(P)+(S) give, for every LTF∘LTF circuit deciding SAT on all proper ASCII 3-CNF files of N_r bits:
  - gates ≥ c_g·2^{3r/2}/r³;
  - wires ≥ c_w·2^{5r/2}/r^{7/2}.

  When r is a power of two this uses only the published Theorem 1.1, since m = 2^r/r, h = r/8 and n_src = 2^{r+1}, which is exactly KW's A_n with n = 2^{r+1}. For other r it uses the rerun of KW's proof (§2, step K). Since 2^r ≥ N_r/1859.06 and r ≤ log₂N_r:
  - **gates ≥ c_g (N_r/1859.06)^{3/2}/log₂³N_r** (c_g, c_w as in (KW), §1);
  - **wires ≥ c_w (N_r/1859.06)^{5/2}/log₂^{7/2}N_r**.
- **At every byte-aligned N ≥ N_{max(8,k₀)}, via the rerun of KW's proof.** Pad with spaces inserted inside the last clause line, before its newline; padding bits are constants. Trailing newlines or a whitespace-only line would fail the journal's checker (`splitlines`, line-count equality, 4-token unpack). In-line spaces pass it: `python3 andreev_projection_padding_check.py` prints `padded files: 542 checked (proper per journal assertions; CaDiCaL == KW Andreev)`. That covers all 256 inputs at (2,2,2) with 1 and 7 spaces, and 10 inputs at (8,32,1) with 1, 1000 and 300000 spaces. Take the largest r with N_r ≤ N. Then N < N_{r+1} ≤ 1859.06·n_src(r) ≤ 3718.12·2^r, which gives:
  - **gates ≥ c_g (N/3718.12)^{3/2}/log₂³N** (c_g, c_w as in (KW), §1, here the rerun's constants);
  - **wires ≥ c_w (N/3718.12)^{5/2}/log₂^{7/2}N**.
- **At every byte-aligned N ≥ N_{r₀}, from the published theorem alone.** Here r₀ is the least power of two ≥ max(8, k₀). Pad the same way from the largest power of two r with N_r ≤ N. Then N < N_{2r} ≤ 1859.06·2^{2r}, so 2^r > (N/1859.06)^{1/2}, and r ≤ log₂N. This gives only:
  - **gates ≥ c_g (N/1859.06)^{3/4}/log₂³N** (c_g, c_w from KW's published Ω-constants);
  - **wires ≥ c_w (N/1859.06)^{5/4}/log₂^{7/2}N**.
- **In short.** Ω(N^{3/2}/log³N) gates and Ω(N^{5/2}/log^{7/2}N) wires, with the exponents and logs of KW Theorem 1.1 unchanged. This holds at the lengths N_r with r a power of two by the published theorem, and at every large N via the rerun of KW's proof. From the published statement alone, the every-N bound is Ω(N^{3/4}/log³N) gates and Ω(N^{5/4}/log^{7/2}N) wires. MAJ∘MAJ gets the same bounds.
- **Average case.** For ε ≫ √(log N/N), the same bounds times ε³ hold against agreement 1/2+ε under the push-forward of the uniform distribution through π (through padding∘π at padded lengths). At r a power of two this follows from KW Thm 1.1 directly. At other lengths it uses the general-k rerun with Cor. 2.2. The argument gives nothing for uniformly random N-bit strings: almost none of them is a proper file, and the device is unconstrained off proper files.
- **Cor. 1.1** (ε-approximate majority of LTF∘LTF) transfers the same way, circuit by circuit.

### Finite checks

`python3 andreev_projection_copy_audit.py` takes about a minute.
- **Solver.** The SAT verdicts come from CaDiCaL (version 2.1.3 in the recorded run; exit 10 = SAT, 20 = UNSAT), found on PATH or in a Lean toolchain, with each file piped on stdin. The journal's properness assertions run on every file: three distinct variables per clause, and every id 1..V occurs.
- **Reference function.** The verdict is compared with an Andreev function written from KW's definition (MSB-first bin, KW input order), through the explicit relabeling above. The journal audit's own formula is not used.
- Output (abridged to the lines below):
  ```
  exhaustive (r,m,h)=(2,2,2): 256 inputs, SAT verdict == KW Andreev on all
  exhaustive (r,m,h)=(3,2,2): 16384 inputs, SAT verdict == KW Andreev on all
  random (r,m,h)=(8,32,1): 62 inputs agree
  random (r,m,h)=(16,4096,2): 6 inputs agree
  TOTAL CaDiCaL verdicts matching KW Andreev: 17022
  TOTAL single-bit columns checked: 660
  probe copy check (r,m,h)=(12,341,1): 8188 source bits, 16376 varying bytes (= 2 per bit), file 853395 bytes = 6827160 bits
  probe copy check (r,m,h)=(16,4096,2): 131072 source bits, 262144 varying bytes (= 2 per bit), file 7919676 bytes = 63357408 bits
  ```
- **Coverage.** The checks cover the complete truth tables at k = 2 and k = 3, plus random samples with all-zero and all-one rows at (4,4,2), (4,4,4), (5,6,2), (5,6,4), (6,10,4), (8,32,1), (9,56,1), (12,341,1) and (16,4096,2). The last four of these layouts are the canonical ⌊2^r/r⌋ shapes.
- **Copy checks.**
  - Single-bit flips: each source bit changes exactly two disjoint bytes, from 48 to 49 (bit 0 only). Checked at six layouts, including canonical r = 8.
  - At r = 12 and r = 16, binary-coded probe inputs identify the source bit behind every varying byte, and random inputs then reproduce the whole file from the template.

## 3. The three standard tests

- **(a) Fast globally correct solver on the hard family? Yes.** A RAM program compares the input with the fixed template of length N_r (2·n_src wildcard digits). On a match it outputs x[z] directly (parities of r rows, then one lookup). Otherwise it runs any correct SAT algorithm. On the family this takes O(N) word steps: a byte-by-byte parse, which is linear and enough here. Also, KW Thm 1.2 gives O(n)-gate depth-3 majority circuits for A, so the family is easy at depth three. The bound is purely a depth-two phenomenon.
- **(b) Same bound for a trivially easy language? Yes.** The argument never uses that SAT is hard: any language admitting a linear-size copy projection of Andreev inherits the bound. Examples are Andreev's function itself (linear time) and the language {π(x) : A(x) = 1} (template check plus evaluation, linear time). Whether 2-SAT admits such a projection was **not checked**.
- **(c) The oracle of the relativized-clock note? Unaffected.** The bound concerns oracle-free LTF∘LTF circuits and holds verbatim in the p = 1 oracle world, where plain SAT has an O(n) oracle RAM algorithm. So the bound is consistent with linear-time SAT relative to that oracle, which confirms it says nothing about RAM time. [Relativized clock](relativized-clock.md)

## 4. Exact obstruction and next step

- **Obstruction.** No known simulation turns a time-T word RAM into an LTF∘LTF circuit of size below N^{3/2}. Generic simulations give depth about T, not 2. Depth-two threshold circuits also provably need Ω(n^{3/2}) wires for PARITY (IPS93; tight for 99% agreement by KW Thm 1.4), while a RAM computes parity in O(N/w) steps. A depth-two size bound therefore cannot be converted into a RAM-time bound. The simulation one would need is "every function computable in linear RAM time has LTF∘LTF circuits of o(N^{3/2}/log³N) gates". It is false: Andreev's function is computable in linear time and is the counterexample, by KW itself. So a depth-two bound of this size, for SAT or anything else, says nothing about linear RAM time.
- **Next step on the circuit line (not on the RAM line).** Lift to MAJ∘LTF∘LTF via KW Thm 1.3. That needs a near-linear copy projection of B_n into 3-SAT. If the AGHP ε-biased set KW use is the powering construction (unverified), then ⟨row_z, x⟩ = ⟨p_x(α), β⟩ over GF(2^ℓ) with ℓ = O(log n). Horner evaluation gives circuits of size O(n log²n). Encoding each input-bit occurrence as the last digit of a unit-fixed name ("10" false, "11" true) would give N = O(n log³n) and about N^{3/2}/polylog gates at depth three with a majority output. All of this is unchecked.

## 5. What is not proved

- **Not proved:**
  - Any RAM-time lower bound for SAT, or any lower bound in a model a RAM compiles into.
  - The general-k form of KW Theorem 1.1 comes from rerunning their proof. It is checked against the text, in two independent readings, but it is not published. The published statement covers k a power of two (infinitely many N, squared apart). With padding alone it gives the every-N bound only with exponents 3/4 (gates) and 5/4 (wires).
  - KW's constants c_g, c_w are unspecified, so only the length ratios (929.53, 1859.06, 3718.12) are explicit.
  - That in-line space padding is "proper ASCII DIMACS" in the journal's sense beyond its checker. It is checked only against the journal's assertions and CaDiCaL (542 files). The bound at the canonical lengths N_r needs no padding.
  - Depth-three bounds for SAT (Thm 1.3 needs B_n's projection). Andreev cannot give superlinear depth-three gate bounds (Thm 1.2).
  - Average-case bounds for uniform N-bit strings.
- **Checked at finite size:** semantics at k = 2, 3 (exhaustive) and at nine further layouts (sampled); copy structure at eight layouts; closed forms and exact lengths at 20 layouts and canonical r = 8..20.
- **Proved here:** (P), (S), the length bounds (L) for all r ≥ 8 (numeric to r = 4096 plus the tail estimate), and the transfer.

## Reproducing the checks

Run from `audits/`; CaDiCaL must be on PATH or in a Lean toolchain under `~/.elan/toolchains`.

```
python3 andreev_projection_copy_audit.py
python3 andreev_projection_length_bounds.py
python3 andreev_projection_padding_check.py
```

[andreev_projection_copy_audit.py](../audits/andreev_projection_copy_audit.py) · [andreev_projection_length_bounds.py](../audits/andreev_projection_length_bounds.py) · [andreev_projection_padding_check.py](../audits/andreev_projection_padding_check.py)
