# On word-write-once memory a mutable array costs Ω(log m/log log m) per operation on average, so pebbling after an online write-once conversion gains at most O(log log t)

Model W has w-bit cells, each written at most once and never loaded before it is written, O(1) mutable registers and a public clock. In model W a mutable array of m words has read cost Ω(log m/log(w·t_u)) when each update writes at most t_u cells. On a random alternating workload it has amortized cost Ω(log m/log log m) per operation when w = Θ(log m). Both bounds are asymptotic: they first exceed one probe at m = 2^266 and at log₂ m = 1847. This is a routine instance of the Fredman–Saks chronogram. Its one W-specific step is that an address the decoder does not know must be a cell written in the epoch. So an online conversion of a RAM run into write-once form, followed by pebbling, gains at most an O(log log t) factor on average, if pebbling's generic gain is a factor log t; offline conversions with look-ahead are not covered. Irani, Naor and Rubinfeld's t·log t/log log n simulation is for bit-write-once memory, whose unset bits are read freely, and does not apply here. Whether the log log gap is real is open. The proofs are at manuscript level and were checked during review. This is not a time bound for any language; the linear, quadratic and cubic questions remain open. [Public-address normal forms](three-public-address-normal-forms-of-a-ram-run.md) · [Normalizing stores](normalizing-stores-in-a-sat-solver.md)

## The model and the statements

**Model W (cell-probe form).** Cells have w-bit addresses and contents. Every cell is written at most once. **No cell is loaded before it is written**, on any input. Between operations the scheme keeps r words of mutable registers, and the operation counter is public. An operation is update(i, v), with i ∈ [m] and v ∈ [2^w], or read(q). It performs an adaptive sequence of loads and writes; computation is free. t_u is the maximum number of cells written by one update. Loads by updates are free and unbounded, which makes the lower bound stronger. The read cost is the number of cells loaded. The scheme is deterministic. For zero-error randomized schemes in which every coin outcome obeys model W and the bound t_u, fix the coins (Yao). The decoder uses correctness at every q, so schemes that may err are not covered.

**Distribution D_{m,n}.** n updates (i_s, v_s), i.i.d. uniform on [m] × [2^w], then one read at q uniform on [m], independent of them.

**Epochs.** Take B ≥ 8 and Λ_j = B + B² + … + B^j (Λ_0 = 0). Epoch j is the B^j updates at times in (n − Λ_j, n − Λ_{j−1}].

**Lemma A (worst-case writes per update, one read).** Let m ≥ 2^20, w ≥ log₂ m, r ≥ 1, t_u ≥ 1, B = ⌈8·w·t_u⌉ and n ≥ 2√m. For every model-W scheme as above and every j with 8(r+2)w ≤ B^j ≤ √m,

  Pr_{D_{m,n}}[ the read loads a cell written during epoch j ] ≥ 1/5.

Consequently E[read cost] ≥ (1/5)·(log_B(√m/(8(r+2)w)) − 1). If (r+2)w ≤ m^{1/4}/8, then

  **E[read cost] ≥ log₂ m / (20·log₂(8·w·t_u + 1)) − 1/5.**

**Lemma A′ (amortized, alternating random updates and reads).** The average cost C per operation satisfies C ≥ c·log m / log(w·C + 2) for an absolute c > 0 and all m ≥ m₀, with w = O(log m); c = 1/1600 was derived during review. So C = Ω(log m / log log m) when w = Θ(log m). The exact statement is in Section 5.

**Credit.** This is the Fredman–Saks chronogram bound in its standard shape, t_q·log(w·t_u) = Ω(log m). Pătraşcu and Demaine (p. 3) state the Fredman–Saks partial-sums bound as "t_q lg(b t_u) = Ω(lg n)", with b "the number of bits in a cell (word)". The proof of Lemma A is a routine instance of that method. The one step specific to model W is the **abort rule**: an aborted simulation identifies an epoch-j cell, so the decoder computes Bad_j itself instead of receiving it. That step is what lets the method apply to an array, which costs O(1) in the ordinary cell-probe model. Lemma A′ adds the routine averaging of the post-epoch window over read times. Priority is not established: no search was made for earlier statements of this bound for write-once, persistent or pure-functional arrays. [Pătraşcu–Demaine, arXiv cs/0502041v2](https://arxiv.org/abs/cs/0502041v2)

**The bounds are asymptotic only.** With t_u = 1 and w = log₂ m, the right-hand side of Lemma A stays below one probe until m = 2^266: log₂ m ≥ 24·log₂(8·log₂ m + 1) first holds at log₂ m = 266. With r = 1 and w = log₂ m:
- the hypothesis (r+2)w ≤ m^{1/4}/8 alone needs log₂ m ≥ 40;
- for Lemma A′ (r = 1, t̄ = 1), the explicit bound reaches one unit per operation only at log₂ m = 1847, and 16(r+2)w ≤ m^{1/4} needs log₂ m ≥ 45.

Neither lemma is a statement at any feasible size.

## 1. What the literature gives in model W

**Irani, Naor and Rubinfeld (1988), technical report.** Pages 1–10 of 15 were read, from the scan; pages 2–9 and 14 were checked again during review. Pages 11–15 (pebble-sticker game, WO-PSPACE = P, conclusions, references) and the journal version (Math. Systems Theory 25, 1992) were not read. [Irani–Naor–Rubinfeld, UCB/CSD-88-434](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-434.pdf)
- **Their models.** The WOMM is *bit*-write-once: "A bit of write-once memory may be set … but never reset" (p. 4). The word-WOMM is "A word … may be written to only once … initially all memory is set to 0" (p. 4). So unwritten words can be read, and return 0. There are C(n) regular registers; p. 4 lists C(n) = c or n^ε. With C(n) = c the register side matches model W. The blank-reads-as-0 rule (and the larger choices of C(n)) put the word-WOMM **outside model W**, which forbids loads of unwritten cells.
- **The bound t·log t/log log n.** It is Corollary 3.3 (p. 7): "An algorithm that runs in O(t) time on a RMM can be simulated in O(t log t/log log n) steps on a WOMM." Its proof stores child addresses so that "the address of the i-th child can be changed into the address of the i+1-th child by only setting bits". So it is bit-write-once only. p. 6 says of Theorems 3.1–3.3: "All but the third also work on the word-WOMM". **It does not apply in model W.**
- **Results that read blank cells.** Theorem 3.2 (O(t log b) when every location changes at most b times, word-WOMM included) does "a binary search … to find the last place in which a value was written" (p. 6), which reads blank cells. Theorem 3.5 (persistence with an O(log log n) slowdown, and simulating the WOMM on the word-WOMM with an O(log log n) slowdown) uses "binary search to find the next blank location" (p. 9). Neither lands in W.
- **What lands in W.** Theorem 3.1 (p. 6): O(t·log s) on the WOMM and the word-WOMM, by path copying in a balanced tree whose root is kept in a register. It never loads an unwritten cell.
- **General simulations.** p. 5: "every data structure can be simulated with an extra O(log n/log log n) multiplicative time factor on the WOMM and an extra O(log n) multiplicative factor on the word-WOMM". So the best general bound in W found in the literature is Theorem 3.1.
- **Openness.** p. 3: "We do not know if any multiplicative increase in running time is actually required for any problem on the general write-once memory model." p. 14 repeats it as an open question.
- **Lower bounds.** p. 8: Vitter's proof gives "Ω(n·log n/log log n) steps on the register-restricted WOMM and Ω(n·log n) steps on the register-restricted word-WOMM", for "maintaining a variable through n updates" when "an adversary may clear the regular memory registers between updates" (p. 2). "This proof does not apply to the general write-once memory models." Also p. 8: "this gives hope only for showing lower bounds on online simulations of RMM by WOMM … Our success in this task has not been better."

**Pătraşcu and Demaine (SIAM J. Comput. 2006).** Abstract and pp. 1–3 read. They prove t_q·lg(t_u/t_q) = Ω(lg n) and t_u·lg(t_q/t_u) = Ω(lg n) for partial sums and dynamic connectivity, and say the chronogram "cannot prove a trade-off … better than t_q lg t_u = Ω(lg n), which was achieved for the marked-ancestor problem … This limitation … translates into an Ω(lg n/lg lg n) limitation." Fredman–Saks and Alstrup–Husfeldt–Rauhe were not consulted; their bound shapes are taken from this paper.

## 2. Proof of Lemma A

Fix j. Put ℓ = B^j. Let I_j be the set of indices updated in epoch j and P_j the set of indices updated after epoch j, so |P_j| ≤ Λ_{j−1}. Let A_pre be the array before epoch j and A_end the array after it. Condition on U_< (all updates before epoch j) and U_> (all updates after it). Both are independent of the epoch-j updates E_j, so H(I_j | U_<, U_>) = H(I_j).

*Entropy.* The epoch-j indices form a uniform sequence in [m]^ℓ, so its entropy is ℓ·log₂ m. Given the set I_j, the sequence is one of at most |I_j|^ℓ ≤ ℓ^ℓ sequences. Hence **H(I_j) ≥ ℓ·log₂(m/ℓ).**

*Decoder.* The decoder knows U_< and U_>. Because the scheme is deterministic, it can re-run the scheme on U_<. It then knows every cell written before epoch j (including time 0), with its content, and it knows A_pre. It also knows P_j. It receives the message M:
- (M1) the final registers: r·w bits;
- (M2) the number of cells written by updates after epoch j (at most t_u·Λ_{j−1}), then each such cell's address and content: at most 2w·t_u·Λ_{j−1} bits plus a count field;
- (M3)–(M5), described below.

For each q ∈ [m] the decoder runs the read of q from the final registers. A load of a pre-epoch cell, a post-epoch cell or a cell the read itself wrote is answered. At the first load of any other address it aborts and puts q in Bad_j. **This is the step that uses model W:** that address was written (no unwritten loads), and not before or after epoch j, so it was written *during epoch j*. Hence q ∈ Bad_j implies that the real read of q loads an epoch-j cell. Up to that point the simulation agrees with the real run.

For each q ∈ Good_j = [m] \ Bad_j the decoder obtains the read's output, which is A_final[q] by correctness. If q ∉ P_j, then A_final[q] = A_end[q]. Let C_j = {q ∈ I_j \ P_j : A_end[q] = A_pre[q]} (the new value equals the old one). Then for q ∈ Good_j \ P_j: q ∈ I_j \ C_j iff A_final[q] ≠ A_pre[q]. So the decoder recovers (I_j \ P_j \ C_j) ∩ Good_j exactly. The message adds the rest:
- (M3) k = |(I_j \ P_j \ C_j) ∩ Bad_j| and that set as a k-subset of the known set Bad_j: ⌈log₂(ℓ+1)⌉ + ⌈log₂ C(b, k)⌉ bits, with b = |Bad_j|;
- (M4) I_j ∩ P_j as a subset of the known P_j: ⌈log₂(ℓ+1)⌉ + ⌈log₂ C(|P_j|, k_P)⌉ bits;
- (M5) C_j: ⌈log₂(ℓ+1)⌉ + |C_j|·w bits.

Every field's length is known to the decoder when it reaches that field, so M is prefix-free given (U_<, U_>). Hence H(I_j) ≤ E|M|.

*Bounds.*
- (M3): log₂ C(b, k) ≤ ℓ·log₂(e(b+ℓ)/ℓ) for all 0 ≤ k ≤ min(b, ℓ). Since k·log(eb/k) increases for k ≤ b, this holds when ℓ ≤ b; when ℓ > b, log₂ C(b, k) ≤ b < ℓ. By Jensen, the expectation is at most ℓ·log₂(e(βm + ℓ)/ℓ), where β = E[b]/m.
- (M4): E[k_P] ≤ ℓ·Λ_{j−1}/m, and log₂ C(|P_j|, k_P) ≤ k_P·log₂(e·Λ_{j−1}).
- (M5): E|C_j| ≤ ℓ·2^{−w}, because the last epoch-j value of q is uniform and independent of A_pre[q].

Writing R for everything except (M3)'s binomial term:

  ℓ·log₂(m/ℓ) ≤ R + ℓ·log₂(e(βm + ℓ)/ℓ), hence **β ≥ 2^{−R/ℓ}/e − ℓ/m.**

*Constants.* With B ≥ 8 we have Λ_{j−1} ≤ (8/7)·B^{j−1}.
- (M1) and (M2)'s count field: (r + 2)w/ℓ ≤ 1/8, using ℓ ≥ 8(r+2)w.
- (M2)'s cells: 2w·t_u·Λ_{j−1}/ℓ ≤ (16/7)·w·t_u/B ≤ 2/7.
- All count fields and ceilings together: at most (5·log₂(ℓ+1) + 7)/ℓ ≤ 0.11, using t_u ≤ ℓ and ℓ ≥ 24w ≥ 480.
- (M4): at most m^{−1/2}·log₂(e√m) ≤ 0.012 for m ≥ 2^20.
- (M5): at most w·2^{−w} < 10^{−4}.

So R/ℓ ≤ 0.533 and β ≥ 2^{−0.533}/e − m^{−1/2} ≥ 0.25 ≥ 1/5. The displayed bounds sum to 0.5328, and the exact terms to 0.5293. Since q is uniform and independent of Bad_j, Pr[the read loads an epoch-j cell] ≥ Pr[q ∈ Bad_j] = β.

*Counting.* Each load hits one cell, which belongs to one epoch, so E[read cost] ≥ Σ_j β_j. The epochs with 8(r+2)w ≤ B^j ≤ √m number at least log_B(√m/(8(r+2)w)) − 1, and all of them exist because Λ_j ≤ (8/7)·√m ≤ n. ∎

## 3. Why the w-free form is not obtained

A natural guess is t_q ≥ c·log m/log(5·t_u), without w. Its argument runs: "If more than half of all addresses could be read without probing a cell written during epoch j, those later cells would encode half of epoch j's random values; so B > 4·t_u". The inference is false. A random index is updated in epoch j with probability only about ℓ/m. A read that avoids epoch j for an index not updated there returns the old value, so it reveals only that the index is **not in I_j**. That is about log₂(1/β) bits per element of I_j, not w bits per value. The post-epoch cells carry up to 2w·t_u·Λ_{j−1} bits, enough for a membership filter of I_j with false-positive rate 2^{−Θ(w·t_u/B)}. The comparison is therefore between B and w·t_u, not between B and t_u. This is exactly where w enters Lemma A. The "values" half of the argument proves only that a read of an index updated in epoch j loads a cell from epoch j or later: one epoch per read, so t_q ≥ 1. The w-free statement itself is left open, not refuted; during review every path-copying epoch had (I_j \ P_j) ∩ Good_j = ∅, so good reads revealed no epoch-j value at all.

## 4. Where "no unwritten loads" is used, and that it is needed

Take the versioned-address scheme: cell (i, k) holds the k-th version of index i, and a read gallops and binary-searches over unwritten cells (the shape of Irani–Naor–Rubinfeld's Theorem 3.2). It writes 1 cell per update and, for n = Θ(m), has O(1) expected read cost on D_{m,n}, because the number of versions of an index is about Poisson(n/m). So the conclusion of Lemma A fails for it once m is large; below m = 2^266 the bound of Lemma A is under one probe anyway. The decoder's inference "unknown address ⇒ epoch-j cell" is false there: one load of a blank cell puts q in every Bad_j at once.

## 5. Proof of Lemma A′ (amortized)

*Setup.* Operation 2s−1 is update(i_s, v_s) and operation 2s is read(q_s), all i.i.d. uniform. There is no per-operation bound. Let t̄ = E[cells written by all operations]/n and C = E[loads + writes over all operations]/n. Let 𝒯 be the set of read positions T ∈ (n/2, n], so |𝒯| ≥ n/5. Put t̄′ = max(1, t̄) and B = ⌈120·w·t̄′⌉. Fix T ∈ 𝒯 and j with 16(r+2)w ≤ B^j ≤ √m.
- Epoch j(T) is the ℓ = B^j operations at positions (T − Λ_j, T − Λ_{j−1}]. They include ℓ′ ≥ ⌊ℓ/2⌋ updates, and Λ_j ≤ (8/7)·√m < n/2, so the epoch lies inside the sequence.
- For j = 1 the window contains the read at T itself. That is harmless: the decoder answers the read's own writes, the (M2) window (T, T) is empty, and the epoch's updates all lie below T.
- I_j is the set of indices updated in the epoch, and H(I_j) ≥ ℓ′·log₂(m/ℓ′) as before.
- The decoder is given every operation outside the epoch and before T, *reads included*. These are independent of I_j.

*Changes from Section 2.*
- (M1) is now the registers after operation T−1.
- (M2) lists every cell written by any operation (update or read) at a position in (T − Λ_{j−1}, T). Their number N_{T,j} is sent in Elias-gamma code, so (M2) costs at most 3w·N_{T,j} + 1 bits for w ≥ 2.
- Cells written during the epoch by reads are epoch cells. The decoder runs the read code for every q ∈ [m] from the registers after T−1; correctness holds for every q. Abort ⇒ an epoch-j cell is loaded, by model W, exactly as before.
- The read at T uses the independent uniform q_T, so Pr[read at T loads an epoch-j cell] ≥ β_{T,j} := E|Bad_{T,j}|/m.

The same computation gives, for each T,

  β_{T,j} ≥ 2^{−R_{T,j}/ℓ′}/e − ℓ′/m,  with R_{T,j} ≤ (r+2)w + 3w·E[N_{T,j}] + 3·log₂(ℓ+1) + 6 + (M4) + (M5).

*Averaging over T.* An operation at position p lies in the (M2)-window of at most Λ_{j−1} read positions T. Hence Σ_{T∈𝒯} E[N_{T,j}] ≤ Λ_{j−1}·t̄·n, and the average of E[N_{T,j}] over T ∈ 𝒯 is at most 5·Λ_{j−1}·t̄. Since x ↦ 2^{−x} is convex, Jensen gives

  avg_T β_{T,j} ≥ 2^{−avg_T R_{T,j}/ℓ′}/e − ℓ′/m.

*Constants* (using ℓ′ ≥ 0.49ℓ, ℓ ≥ 960 and m ≥ 2^20):
- post-epoch cells: 15·w·t̄′·(8/7)·B^{j−1}/(0.49·B^j) ≤ 35/120 < 0.30;
- registers and count field: (r+2)w/ℓ′ ≤ 0.13;
- count fields: (3·log₂(ℓ+1) + 6)/ℓ′ ≤ 0.08;
- (M4): at most 0.012;
- (M5): below 10^{−4}.

So avg_T R_{T,j}/ℓ′ ≤ 0.523 and avg_T β_{T,j} ≥ 2^{−0.523}/e − m^{−1/2} ≥ 0.25 ≥ 1/5. The displayed bounds sum to 0.5221, and the exact terms to 0.5062.

*Counting.* Each load hits one epoch, so the average expected cost of the reads in 𝒯 is at least Σ_j avg_T β_{T,j}. The number of valid j is at least log_B(√m/(16(r+2)w)) − 1 ≥ log₂ m/(4·log₂ B) − 1. ∎

*The statement.* For m ≥ 2^20, w ≥ log₂ m, 16(r+2)w ≤ m^{1/4} and n ≥ 3√m, the reads in the second half have average expected cost at least (1/5)·(log₂ m / (4·log₂(120·w·max(1, t̄) + 1)) − 1). Since C ≥ t̄ and the reads in the second half are about n/4 of the operations, C ≥ (1/25)·(log₂ m / (4·log₂(120·w·max(1, C) + 1)) − 1). Hence C = Ω(log m / log log m) when w = O(log m).

Scope: this needs no per-operation bound, so it covers amortized schemes with rebuild bursts, LSM types included. It still concerns one fixed random workload, a simulation method, and the cell-probe count.

## 6. Consequences, each with its scope

- **Online step-faithful write-once conversions.** These are simulations that serve each source load or store online as a read or update of the array in model W.
  - **Online** means that while serving source step s the conversion loads no input word that the source has not read by step s. Loads of input words already read are allowed and counted.
  - *Input words* (argued on paper during review; neither script has input words). Treat the input words of the operations in epoch j as epoch-j cells. The decoder knows their addresses and, from its side information, every other input word. So the proofs of Lemmas A and A′ go through unchanged.
  - Without the online condition the proof fails, because cells written before epoch j can then depend on epoch j's inputs. The bound fails too: an offline conversion can load the whole input at step 1, tabulate every answer at address base + T, and serve each read with one load, O(1) amortized in the cell-probe count. This matters if input reads are allowed anywhere, as a convention for write-once programs may allow.
  - Run the source program that performs the workload of Lemma A′. Its online conversion costs Ω(log m / log log m) per source step on average over that random workload, whether the scheme is amortized or worst-case, when w = Θ(log m) and m is large. Irani–Naor–Rubinfeld's Theorem 3.1 gives O(log m) inside W.
- **Normal form plus pebbling.** Take the generic gain of pebbling an explicit DAG to be a factor log t; with R rounds the rounds-against-pebbles entry of round three gives Θ(log R). Under that assumption, an online step-faithful write-once normal form followed by pebbling gains at most O(log t·log log m / log m) = O(log log t) on this workload, on average, when m ≥ t^{Ω(1)}, w = Θ(log m) and m is large. If the conversion cost is Θ(log m), it gains nothing. That pebbling's gain "cancels exactly" is still unproved: Lemmas A and A′ leave exactly the log log factor open. [Round three](parallel-proof-attempts-of-27-november-round-three.md)
- **Overlap.** No journal note states Lemma A (searches of the notes, here and during review, read the openings and matching lines only).
  - The store-normalization note already summarizes Irani–Naor–Rubinfeld as above (Theorem 3.3 is bit-write-once, and Vitter's bound is for the register-restricted interface). It also proves a *snapshot-local* bound, q ≥ log_{b+1}(U+1) for cells that change at most b times. That note says the bound's premise fails with "a public clock … changing register contents"; Lemma A keeps both, for arrays, at the price of the w inside the logarithm.
  - The same note gives a bit-write-once conversion with slowdown O(1 + log(T+1)/log w) by a unary-mask radix. Its sparse trie reports zero on a missing path ("A missing path on a load reports zero without allocating anything"). So the journal's existing normal form lies outside model W, and Lemma A′ does not apply to it.
  - The monotone-rank note proves Ω(P·log log H) for a bit-write-once replay with advice and known event times: a different model and a smaller factor. [Persisting monotone rank queries](persisting-monotone-rank-queries.md)
  - The snapshot-query note is a static s·q bound for describing solver memory. [Persistent snapshot query cost](persistent-snapshot-query-cost.md)
  - Two notes use Fredman–Saks-style epochs, but for a static solver's own discovery order; neither states an array bound in model W. [Birth-epoch reuse](birth-epoch-reuse.md) · [Discovery-epoch snapshot codes](discovery-epoch-snapshot-codes.md)
- **The public-address map.** This settles the write-once row of the public-address note's table for online conversions: the write-once form was the one normal form left there that can feed pebbling without public addresses.

## 7. Checks

**The decoder of Lemma A.** `write_once_array_epoch_decoder_check.py` (about 2 s) runs m = 4096, n = m, w = 32, B = 2 (finer epochs than the lemma needs; it tests the *decoder*, not the constants) with three seeds:
- schemes: path copying with F = 2 (t_u = 25 writes) and F = 16 (t_u = 49), both in model W; versioned addresses (VA), outside W;
- for each epoch it runs the encoder and decoder of Section 2 and checks that the decoder recovers I_j exactly, that for the W schemes every abort is a load of a cell written during epoch j, and that for the W schemes Σ_j β_j ≤ mean read cost.

```
PC(F=2) m=4096 seed=1 writes/update=25 mean_tq=13.000 sum_beta=5.339
   j= 9 ell=  512 |I_j|=  487 post_cells= 12750 beta=0.401 decode_ok=True aborts_in_epoch=True msg_bits=   817694 log2C(m,|I_j|)=    2150
PC(F=16) m=4096 seed=1 writes/update=49 mean_tq=4.000 sum_beta=3.325
VA m=4096 seed=1 writes/update=1 mean_tq=2.821 sum_beta=11.000
   j= 2 ell=    4 |I_j|=    4 post_cells=     2 beta=1.000 decode_ok=True aborts_in_epoch=False msg_bits=      214 log2C(m,|I_j|)=      43
ALL_W_CHECKS_PASS
```

All 99 epoch decodes succeed. For VA, Σβ_j = 11 exceeds the mean read cost of 2.82: the inequality of the proof fails outside W, as Section 4 predicts. The message lengths for path copying (817,694 bits against log₂ C(m, |I_j|) = 2,150 at j = 9) are far above the entropy, because these schemes violate B ≥ 8w·t_u at this size; the constants are checked only by the arithmetic of Section 2. This script never has reads that write cells, never exercises the correction field (M5) (with 32-bit values no coincidence occurs) and does not run the decoder of Lemma A′.

**Independent check.** `write_once_array_independent_check.py` was written during review from the statements, not from the script above, and covers all three gaps. Its schemes are PC2 and PC4R (path copying; PC4R's reads write cells and load back their own writes), LOG (clock-addressed, t_u = 1), LSM (Bentley–Saxe levels, amortized, with bursts) and VA as the outside-W control. It runs the Lemma A decoder (B = 2 and 3) and the Lemma A′ decoder (n = 2m alternating operations, 6 read times in the second half), and checks for every epoch that I_j is decoded, that every abort is an epoch-j load, that Bad_j is exactly the set of q whose real read loads an epoch-j cell, and that Σβ_j is at most the mean read cost. With 2-bit values the correction field C_j is used in 500 epochs:

```
# epoch decodes: ok=795 failed=0
# field usage over all epochs: {'epochs': 795, 'good>0': 159, 'bad>0': 716, 'P>0': 360, 'C>0': 500, 'dropP_breaks': 360, 'dropP_harmless': 0}
INDEPENDENT_W_CHECKS_PASS
```

Over its four recorded runs (m = 64, m = 256 with 32-bit and with 2-bit values, m = 1024) it decodes 2,120 epochs with no failure. VA fails the W checks in every run, as predicted. Its "dropP_breaks" count is true by construction, so it is not a test.

**Constants.** `write_once_array_constants_check.py`, also from the review, recomputes every constant and threshold above:

```
first log2 m with log2m/(20 log2(8 log2m+1)) - 1/5 >= 1 : 266
first log2 m with (r+2)w <= m^(1/4)/8 at r=1, w=log2 m : 40
first log2 m with 16(r+2)w <= m^(1/4) at r=1, w=log2 m (Lemma A'): 45
first log2 m where A' consequence bound (t=1, w=log2 m) gives C >= 1: 1847
```

## 8. The three standard tests

- **(a) Fast solver for the hard family?** Yes, trivially. Random update/read sequences cost O(1) per operation on a RAM with mutable memory. Lemma A is a bound on model W only, so it bounds a simulation method, not a language.
- **(b) Same bound for 2-SAT?** Yes. Any RAM program that runs the random array workload, with its memory converted online and step-faithfully into model W, pays the same factor; a linear-time 2-SAT solver is no exception. Lemma A cannot separate SAT from anything.
- **(c) The oracle of the relativized-clock note.** The probe statement uses no instruction semantics and holds in any world. The step version needs one instruction to load O(1) cells. Relative to that oracle one instruction reads a packed string of any length, and unwritten memory reads as zero, so the premise of the step version fails there and the step version does not relativize to that model. Whether its conclusion fails relative to that oracle is not shown. [Relativized clock](relativized-clock.md)

## 9. Exact obstruction and next step

1. **The w-free form: open.** The per-epoch encoding of Section 2 cannot give it (Section 3). Its accounting allows the post-epoch cells to hold a membership filter for epoch j at log₂(1/β) bits per element, so with B = O(t_u) it yields only β ≥ 2^{−O(w)}. That this limits every chronogram-style argument is a reading, not a theorem; it agrees with the Fredman–Saks shape t_q lg(b·t_u) = Ω(lg n), where the cell size b sits inside the logarithm. The next lemma to try is *refresh additivity*. Over all read times, every window of Λ_{k−1} operations must contain, in its own cells, a certificate of B^k·log₂(1/β) bits about the B^k updates before it, at every level k at once. If certificates of different levels need disjoint cells, then L·B·log₂(1/β) ≤ O(t_u·w), with L = log_B m; with w = Θ(log m) this gives t_q = Ω(log m / log t_u). What blocks it: one w-bit cell could serve several levels, and the entropy accounting does not add across levels, because each level's constraint is conditioned on a different past.
2. **The Pătraşcu–Demaine trade-off: open.** An estimate, not proved: information transfer is capped at O(1) amortized for this problem. In W the decoder needs only contents, never addresses, and a read needs at most w + O(log n) bits about the past (a value plus about one membership bit per level). So a sharp trade-off would have to come from a navigation or refresh argument as in item 1, not from information content.
3. **A structure with max(t_q, t_u) = o(log m) in W, counting reads as well: not built in the worst case.** On 28 November a round-five note built one in the amortized sense on the random alternating workload: packed presence tables, rebuilt in the same pass as each merge so that every key is read O(1) times per level, cost O(log m / log w) loads plus writes per operation in expectation, which with Lemma A′ is Θ(log m / log log m) at w = Θ(log m). The worst-case form and arbitrary operation sequences stay open. [Packed presence tables](packed-presence-tables-for-a-word-write-once-array.md) Path copying and LSM-type schemes (levelled or tiered, with static dictionaries) give Θ(log m). Sketch, not checked: a hierarchy of frontier filters with fan-out B gives t_q = O(log m / log B) with O(B) *writes* per update, amortized; a worst-case version needs deamortization. Each rebuild must *read* the keys, so it costs Θ(B·log_B m) loads per update. This would show that Lemma A's write-only cost model cannot be improved beyond log m / log t_u. A real structure needs a way to merge filters without re-reading keys; the bit-write-once model achieves this by setting bits in place, which model W forbids.

## 10. What is not proved

- The w-free form, the Pătraşcu–Demaine trade-off, a structure with max(t_q, t_u) = o(log m) in the worst case or on arbitrary operation sequences (an amortized one for the random workload is in a round-five note), and the sharp statement "max(t_q, t_u) = Ω(log m) in model W".
- Lemmas A and A′ are proved, but only in a narrow scope:
  - an average over one random workload, in the cell-probe count;
  - with w = O(log m), and only for large m (useful from m = 2^266 and log₂ m = 1847);
  - for conversions, only online ones.
- The extension to input words was argued on paper during review. The normal-form consequence assumes that pebbling gains at most a factor log t.
- Lemma A is a routine instance of the Fredman–Saks chronogram, with one model-specific step, the abort rule. No priority over earlier write-once, persistent or pure-functional array bounds is claimed, because none was searched for.
- The frontier-filter scheme of Section 9 is an unchecked sketch, and the cap on information transfer is an estimate.
- Nothing here bounds SAT, or any language, and no step toward the target or the native milestone is claimed. Lemmas A and A′ only narrow the gain that online step-faithful write-once normal forms plus pebbling could give: to at most O(log log t) on the random array workload, when the live memory is polynomial in t.
- The checks are finite and test only the decoders' correctness, not the constants.

## Reproducing the checks

Run from `audits/`; no script writes files.

```
python3 write_once_array_epoch_decoder_check.py
python3 write_once_array_independent_check.py 8 3 2
python3 write_once_array_constants_check.py
```

The first takes about 2 seconds. The independent check takes about 1.5 seconds per run; its other recorded runs are `6 1`, `8 3` and `10 1` (the last about 4.5 seconds), and with no argument it runs m = 256 with two seeds. The constants check is instant. [Epoch decoder check](../audits/write_once_array_epoch_decoder_check.py) · [Independent check](../audits/write_once_array_independent_check.py) · [Constants](../audits/write_once_array_constants_check.py)
