# Deterministic RAM time T fits in word-priced alternating time O(T/log log T) on the native band, through a seeded write-once array

On the native-band RAM (w(m) = 12⌈log₂(m+2)⌉, a read-only input of known length), DTIME_RAM[T] ⊆ ATIME^word_RAM[O(T/log log T)] for every T with m ≤ T ≤ 2^{w/2}, that is T ≤ m^6, that is computable from m in O(T/log log T) word steps. Guesses are priced in words and the number of alternations is unbounded; counted in bits there is no gain, since a path guesses O(T·log T/log log T) bits. The proof chains three steps, each checked during review: a seeded write-once array, which is the packed presence tables of the round-five note on composite keys hashed by a degree-2 polynomial modulo a prime and costs O(n(1 + log n/log w)) expected word steps on every fixed sequence of n operations; a write-once normal form of the RAM run built on that array; and a truth-claim game in which each load names its writer, whose existential player follows Dymond–Tompa's pebbling strategy, read at source during review. Two dependencies remain: the solution of Paul–Tarjan–Celoni's recurrence, which Dymond–Tompa cite and which was not re-derived, and the word-step count, which is argued and not instrumented. This meets the normal-forms note's condition g = o(log T) for its write-once route and attains the write-once note's ceiling of a log log t gain. Consequence (A), A_RAM ∉ DTIME_RAM[o(N log log N)] for the alternating acceptance problem, would give the journal's target (U), ATIME^word_RAM[n] ≠ DTIME_RAM[n], in a stronger form; it is a proof outline whose width bookkeeping is not yet written. Consequence (B) is a restricted-model result with three qualifications. Novelty is not established: Mak's 1995 thesis on the unit-cost RAM is unread. Nothing here is about SAT, the alternation criterion (K) or the milestone NTIME_RAM[n] ≠ DTIME_RAM[n]; the linear, quadratic and cubic questions remain open. [Packed presence tables](packed-presence-tables-for-a-word-write-once-array.md) · [Normal forms of a RAM run](three-public-address-normal-forms-of-a-ram-run.md#27-what-each-form-gives-to-games-and-protocols) · [Write-once arrays](mutable-arrays-on-word-write-once-memory.md)

## The machine and the statements

**The machine** is the native-band RAM of the [unary-clock band note](native-unary-clock-band.md#machine-and-complete-language): w(m) = 12⌈log₂(m+2)⌉ for m input bits, a read-only packed input of known bit length, and zero-initialized work words. The seeded array uses only add, subtract, multiply (low word), Boolean operations, comparisons, and right shifts by a level-dependent amount. Where a shift count must be a literal, the right shift is a division by 2^{w−ℓβ}, kept per level with one division by B. The chain does not live on the five-instruction machine: there the width is 16⌈log₂(N+2)/16⌉, so the range m ≤ T ≤ 2^{w/2} is essentially empty, and the input occupies the writable words from address 0, where the layout below puts its first region.

**Model W** is that of the [write-once note](mutable-arrays-on-word-write-once-memory.md): a scheme writes each cell at most once, never loads a cell before it is written, and keeps O(1) registers between operations.

**The seeded-array lemma.**
- *Parameters.* w ≥ 20, and β ≥ 1 with B = 2^β and B² ≤ w. The seed is g = (p, ρ, a, b, c), five numbers of at most w + 2 bits, so at most ten words. A seed is *good* if p is a prime with 2^w < p < 2^{w+1}, ρ = ⌊4^{w+1}/p⌋ (Barrett's constant), and a, b, c ∈ Z_p.
- *The scheme S_g* implements an array indexed by [2^w]. Each index starts at a default value: 0, or the read-only input word when the index is an input address.
- **(i) Every seed, every sequence.** For every seed g, good or not, and every sequence of at most 2^{w/2} operations update(x, v) and read(q) with x, q ∈ [2^w], every read returns the last value written to q, or q's default, no cell is written twice, and no cell is loaded before it is written.
- **(ii) Every fixed sequence.** Fix p prime and ρ correct, and draw a, b, c uniformly from Z_p. For every sequence σ of n ≤ 2^{w/2} operations chosen before the seed, E_{a,b,c}[loads + writes of S_g on σ] ≤ 75·n·(⌊log_B n⌋ + 1).
- **(iii) Word steps.** E[word steps] ≤ C·n·(⌊log_B n⌋ + 1) + O(B), with C absolute. With B = 2^{⌊½ log₂ w⌋} this is O(n·(1 + log n / log w)).

**The normal-form lemma.** For every program P of this machine with time T, m ≤ T ≤ 2^{w/2}, there is a program N that reads an O(1)-word seed g from its first registers such that, for every g and x, every step of N_g(x) makes at most one work-memory load and one store, every work cell is stored at most once and none is loaded before it is stored; if N_g(x) halts within β it outputs P(x); and for every x some g makes it halt within β = O(T·log T / log w).

**The named-writer lemma.** Let N be a program as in the normal-form lemma, and let β(m) be computable from m in O(β/log β) word steps. Then {x : ∃g, N_g(x) accepts within β(|x|) steps} ∈ ATIME^word_RAM[O(β/log β)].

**Theorem.** DTIME_RAM[T] ⊆ ATIME^word_RAM[O(T/log log T)] for every T with m ≤ T ≤ 2^{w/2} (that is T ≤ m^6) such that T(m) is computable from m in O(T/log log T) word steps, for example T = m^k, where O(1) multiplications suffice because the input length is known. The computability condition is needed because the alternating machine computes its own budget c·β/log β and every path must halt within O(T/log log T). **The gain needs word-priced guesses.** Counted in bits, a path guesses O(T·log T/log log T) bits, more than T, so there is no bit-priced gain; the round-three and round-five entries say the same of their games. Larger polynomial T needs a wider word on the alternating side, which is not written out.

**Where it sits in the journal.** The [normal-forms note](three-public-address-normal-forms-of-a-ram-run.md#27-what-each-form-gives-to-games-and-protocols) says of the write-once row: "The truth-claim entry gives ATIME(T·g/log T), where g is the conversion overhead, so this route reaches (U) if g = o(log T)". The write-once note's title caps the route: "pebbling after an online write-once conversion gains at most O(log log t)". The seeded array supplies g = O(log T/log log T), which meets the condition and gives the theorem above, and so attains that ceiling; (U) itself still needs the width bookkeeping of consequence (A) (Section 6). The route is the journal's: the truth-claim game is the round-three entry of the [round-three summary](parallel-proof-attempts-of-27-november-round-three.md), and the named writer and the normal form are the round-five entry of the [round-five summary](parallel-proof-attempts-of-28-november-round-five.md), which also records why guessed fields placed per branch are unsound. The round-five note on [packed presence tables](packed-presence-tables-for-a-word-write-once-array.md) sketched the seeded array as its next lemma.

## 1. The seeded array

- **Hash.** h(x) = (a·x² + b·x + c) mod p, and h′(x) = ⌊h(x)/2⌋ ∈ [0, 2^w). Each entry of a run is three cells (h′(x), x, v). Runs are sorted by the composite key (h′(x), x).
- **Buckets.** The bucket of x at exponent e ≤ w is the top e bits of h′(x), that is h(x) >> (w + 1 − e). So the bucket is monotone in the sort key, and the buckets at exponent e + 1 refine those at e; these are the two properties the merge and the read use. Ties in h′ are broken by x, so distinct addresses are never confused.
- **Levels.** Level ℓ uses e_c(ℓ) = ℓβ and e_f(ℓ) = (ℓ+1)β, with no cap: the round-five scheme with μ := w. Since n ≤ 2^{w/2} and β ≤ ½·log₂ w, every level in use has (ℓ+1)β ≤ w/2 + β ≤ w, so the capped regime never occurs, and a read of a never-updated address visits at most ⌊log_B n⌋ + 1 levels.
- **Runs.** Run (ℓ, g) covers the update window [g·B^ℓ, (g+1)·B^ℓ), so it holds at most N = B^ℓ entries. Its directory has 2^{ℓβ} = N coarse buckets, each with its own start cell and end cell: two cells rather than the round-five note's packed one, because offsets now go up to n rather than m.
- **Presence tables** are the round-five note's, indexed by fine bucket. A version of level ℓ has B^{ℓ+1} vectors of B bits, packed B to a word in the low B² bits, so a version is exactly N words. The vector of fine bucket f is in word f >> β at bit offset (f AND (B − 1))·B, and run r's bit is at position B − 1 − r, so the lowest set bit is the newest run.
- **Read(q).** Compute h(q) once. Go through the levels ℓ = 0, 1, … up to ⌊log_B U⌋, skipping a level whose clock digit is 0. In each level load one presence word and scan the flagged runs newest first; in each, load the directory cells of q's coarse bucket and scan entries until one is ≥ (h′(q), q). Stop at the first run that holds q and return its value. If no run holds q, return q's default: 0, or one load of the read-only input word.
- **Update(x, v).** Compute h(x) once and write run (0, U) as one entry. Write level 0's presence version, one load and one write. Then run the round-five merge cascade unchanged on the composite keys: selection rounds, newest wins on ties, and directory and presence words written in the same pass.
- **Layout.** Clock addressing as in the round-five note. Each (kind, level) region holds at most 3n cells (run entries 3n, directories 2n, presence versions n), and there are at most 3(w/β + 1) regions. So RS = w − ⌈log₂(3(w/β + 1))⌉ − 1 depends on w alone, with 2^RS > 2^w/(12(w/β + 1)). Every sequence of n ≤ 2^{w/2} operations fits once 36(w/β + 1) ≤ 2^{w/2}, which holds for every β ≥ 1 once w ≥ 20; the exact condition, 3·2^{w/2} ≤ 2^RS, already holds at w = 18 with β = 1, and the layout overflows at w = 16, β = 1 (Section 7). The bit-scan table lies in the unused upper half of the address space.

## 2. (i) Legality and correctness, for every seed and every sequence

The round-five note's proof of legality and correctness uses only these facts: the bucket is a monotone function of the sort key, nested across levels; run windows partition the update history; each structure is built once; and every load targets an existing version, an existing directory cell, an entry below a directory end bound, or the bit-scan table. None of them depends on which function h is, so the argument holds for any deterministic h_g: [2^w] → [0, 2^{w+1}). A bad seed only makes the hash useless; the final value is masked to w + 1 bits, so it stays in range. Composite keys are compared on (h′, x), so equal h′ for distinct addresses is harmless. The default-value read is one load of read-only input, outside work memory, and the layout fits for w ≥ 20. ∎

## 3. (ii) Expected cost on a fixed sequence

**The run key sets do not depend on the seed.** S_r, the set of distinct addresses updated in run r's window, is fixed by σ, and so is the set of runs that hold q, and with it the run where a read stops, since flags have no false negatives. Only the layout (bucket counts, flags, directory contents) depends on h, and all expectations below are over a, b, c with the sets fixed.

**3-wise independence.** Distinct addresses x, y, z are below 2^w < p, so they are distinct mod p. The map (a, b, c) ↦ (h(x), h(y), h(z)) is linear with the Vandermonde matrix of (x, y, z), whose determinant ±(x − y)(y − z)(z − x) is nonzero mod p, so the triple is uniform on Z_p³. Hence Pr[bucket_e(x) = t] ≤ 2^{w+1−e}/p < κ·2^{−e} with κ = 2, and events on h(x), h(y), h(z) multiply; in particular Pr[bucket_e(x) = bucket_e(y)] ≤ κ·2^{−e} for x ≠ y.

Below, every scanned entry is charged 2 probes (h′ and x), and every bit scan 1 probe for the table load.

**Read, at a level where it does not stop.** Here q ∉ S_r for every examined run r. Write N = B^ℓ, so |S_r| ≤ N, and n_r = #{y ∈ S_r : coarse(y) = coarse(q)}. With 2^{e_c} = N and 2^{e_f} = BN:
- Pr[r flagged] ≤ Σ_{z ∈ S_r} Pr[fine(z) = fine(q)] ≤ N·κ/(BN) = κ/B, a two-point event.
- E[n_r·1(flagged)] ≤ Σ_{y,z ∈ S_r} Pr[coarse(y) = coarse(q) ∧ fine(z) = fine(q)]. The y = z terms give at most κ/B. When y ≠ z the addresses y, z and q are distinct, and this is where 3-wise independence is needed: each term is at most κ²·2^{−e_c−e_f}, and the N² terms give κ²/B. So E[n_r·1(flagged)] ≤ (κ + κ²)/B = 6/B.
- A flagged run costs one bit-scan load, 2 directory cells and at most n_r entries, so at most (1 + 2)·κ/B + 2·6/B = 18/B in expectation. With at most B − 1 runs and one presence word, a level costs **< 19**.

**Read, at the run that holds q** (at most one per read): a bit scan, 2 directory cells, the entries up to q, at most 1 + #{y ∈ S_r \ {q} : coarse(y) = coarse(q)} with mean at most 1 + κ, and the value load. Total ≤ 1 + 2 + 2(1 + κ) + 1 = **10**. So **E[read] ≤ 19·(⌊log_B n⌋ + 1) + 10**, with no capped levels to treat separately.

**Merge into level ℓ ≥ 2.** The inputs are B runs at level ℓ − 1 with |S_r| ≤ N/B, so Σ_r |S_r| ≤ N and Σ_r |S_r|² ≤ N²/B. For an output bucket b at exponent ℓβ, let k_b count the *distinct* addresses in b, X_{r,b} = |S_r ∩ b|, X_b = Σ_r X_{r,b}, F_b the flagged runs (|F_b| ≤ X_b), and Z_{r,b} = |S_r ∩ (c(b) \ b)|, where c(b) is b's input coarse bucket at exponent (ℓ−1)β. There are k_b + 1 rounds, and per round a flagged run costs a bit scan, 2 directory cells and at most X_{r,b} + Z_{r,b} + 1 entries, so

  cost_b ≤ (k_b + 1)·Σ_{r∈F_b} (5 + 2X_{r,b} + 2Z_{r,b}) ≤ 7(k_b + 1)·X_b + 2(k_b + 1)·Σ_r X_{r,b}·Z_{r,b}.

Repeated addresses are where a fixed sequence differs from the random workload: one address may lie in all B input runs. That is why rounds are counted with k_b and copies with X_b.
- **First term.** Let m_y be the number of input runs holding y, so Σ_y m_y ≤ N. Then Σ_b E[k_b·X_b] ≤ Σ_r |S_r| + Σ_{u≠y} m_y·κ/N ≤ (1 + κ)N and Σ_b E[X_b] ≤ N, so the first term is ≤ 7(2 + κ)N = **28N**.
- **Second term, with no four-point term.** In Σ_b E[(k_b + 1)·X_{r,b}·Z_{r,b}], the address u counted by k_b, y ∈ S_r ∩ b and z ∈ S_r ∩ (c(b) \ b) satisfy z ≠ y and z ≠ u, so at most three distinct addresses occur. The "+1" part and the u = y part each give Σ_r |S_r|²·κ·2^{−(ℓ−1)β} ≤ κN, and the distinct triples give Σ_r N·|S_r|²·κ²·B/N² ≤ κ²N. So the second term is ≤ 2(2κ + κ²)N = **16N**.
- **Other costs**, together ≤ **10N**: 5 per output entry (load x and v, write three cells), 2 directory writes per bucket, 2 presence words per bucket (the old version loaded, the new one written), and N/B input presence words.

So **E[merge] ≤ 54N, at most 54 per update per level**. The merge into level 1 has inputs with one entry each and no directory and costs at most 3(2 + κ)N + 9N + N/B ≤ 22N; a level-0 update costs 5. **Total**, for every fixed σ with n operations:

  E[cost] ≤ n·(5 + 54·⌊log_B n⌋) + n·(19(⌊log_B n⌋ + 1) + 10) ≤ 75·n·(⌊log_B n⌋ + 1). ∎(ii)

This is amortized over the whole sequence, which is what the normal-form lemma needs, since the budget β is a total. One update can cascade merges through every level and cost Θ(n). Each structure is built exactly once, by the clock: when a level's digit returns to 0 the merge is all the work, the next run starts a fresh presence version with no load, old versions are abandoned inside the 3n region, and no global rebuild ever happens, since levels never cap, the seed and RS are fixed, and the clock never wraps (checked during review).

## 4. (iii) Word steps

- **The hash, with no division and no high product.** Numbers below 2^{3w} are held in half-word limbs, so schoolbook products of numbers with at most 6 half-limbs cost O(1) word steps. Barrett reduction of z < p², with k = w + 1 (so 2^{k−1} < p < 2^k) and ρ = ⌊2^{2k}/p⌋: put z₁ = ⌊z/2^{k−1}⌋ and q̂ = ⌊z₁·ρ / 2^{k+1}⌋. Then z₁·ρ ≤ 2^{k+1}·z/p, and z₁·ρ > (z/2^{k−1} − 1)(2^{2k}/p − 1) gives q̂ > z/p − 3, so r = z − q̂·p lies in [0, 3p). The code always performs exactly two conditional subtractions of p and masks to w + 1 bits, so its step count does not depend on the seed. h(x) takes three reductions and is evaluated once per update, stored in the entry, and once per read. A wrong ρ or a composite p gives some deterministic function, which Section 2 covers.
- **Bit scans.** Iterating over the set bits of a vector u uses u AND (0 − u), a table load and u AND (u − 1). Since u AND (0 − u) is a power of two, only the B cells TAB[2^i] = i are ever loaded; they are written once at initialization, at sparse addresses in the upper half of the address space, which is W-legal and costs O(B).
- **Presence-table copy.** The new version's word for output bucket b is the old word OR'ed with 1 << ((f AND (B − 1))·B + B − 1 − r) for each output entry with fine bucket f: O(1) per entry and per word.
- **Newest wins at O(1) per key.** Each round selects the minimum composite key among the flagged runs' current keys, ties to the larger r, in O(|F_b|) word steps, inside the per-round charge; older duplicates are skipped by the "> last output" test.
- **Addresses and control.** Region bases are (kind, ℓ) times 2^RS; slot sizes 3·2^{ℓβ} and 2·2^{ℓβ} are shift-and-add; clock digits are (U >> ℓβ) AND (B − 1), or divisions by B^ℓ kept per level.

So word steps ≤ C·(probes + n·(⌊log_B n⌋ + 1)) + O(B). That is (iii). ∎ It is argued, not instrumented, here or during review.

## 5. The normal form, the named-writer game and the inclusion

**Proof of the normal-form lemma.** N_g runs P instruction by instruction and serves P's work loads and stores through S_g; each of N's instructions makes at most one load or store. Every N_g is write-once with no early load, for every g and every x, by (i): the layout only has to hold the array operations, of which there are at most T ≤ 2^{w/2} whatever g is, because σ_x is P's own sequence, the same for every g since every g gives correct reads, and a step counter stops N at β. As σ_x does not depend on g, for a fixed prime p (one exists, by Bertrand) E_{a,b,c}[steps of N_g(x)] ≤ c₁·T + C·T·(⌊log_B T⌋ + 1) + O(B), and some (a, b, c) achieves this. Take β twice that bound, with the counter rejecting after β steps. With B = 2^{⌊½ log₂ w⌋}, β = O(T·log T / log w). ∎

**The named-writer game** (the round-three truth-claim game with the writer of each load named; written out in full during review).
- *Records.* The genuine record R_i of step i consists of the registers after step i, including the PC and the step counter; (A_i, y_i), the address and value stored at step i, or ⊥; and j_i, the step that stored the work cell loaded at step i, or ⊥. After halting R_i repeats with A_i = j_i = ⊥. R_0 is the initial state, and it contains g.
- *Positions* are (c, κ_c, P, k): the challenged index c with its claimed record κ_c, a table P, a partial map from indices to records with P(0) = R_0 fixed, and the remaining budget k.
- *Terminal test*, once P(c−1) is defined: recompute step c from P(c−1)'s registers. For a work load from address A, require j := κ_c.j with j < c, j ∈ dom P and P(j).A = A, and take P(j).y as the loaded word; an input load reads the input; otherwise require κ_c.j = ⊥. Accept iff the recomputed record equals κ_c.
- *Move.* If k = 0, reject. Otherwise ∃ names a nonempty list Q of (index, record) pairs, each one index word plus O(1) record words, and the budget becomes k − |Q|. ∀ then stays, giving (c, κ_c, P ⊕ Q, k − |Q|), or picks an element (q, κ) of Q, giving (q, κ, P ⊕ Q, k − |Q|).
- *Claim.* If (c, κ_c, P, k) is winning for ∃ and P(i) = R_i for every i < c in dom P, then κ_c = R_c. By induction on k:
  - *Terminal case.* P(c−1) = R_{c−1}, so the recomputed step is genuine apart from the loaded word. For a work load from A, P(j) = R_j with j < c, so step j genuinely stored y_j at A; N_g stores A only once, so A holds y_j at time c and j is the genuine writer. By W-legality the genuine load has a writer, so the honest record exists, and determinism gives that the recomputed record is R_c; the check accepted, so κ_c = R_c.
  - *Move case.* Take ∃'s winning Q and order its elements with index below c by nondecreasing index. Each element's branch is winning with a smaller budget, and every table entry of P ⊕ Q below its index is from P, so genuine, or an earlier element, genuine by this inner induction; so each element is genuine, whatever the overwrite rule. The stay branch is winning with a smaller budget, so κ_c = R_c. ∎ Elements at or above c are never needed, so duplicates and overwrites are harmless.
- *Root.* ∃ announces g, an index h ≤ β and κ_h, a claim that N_g has halted and accepted; play starts at (h, κ_h, {0 ↦ R_0(g)}, K). If that position is winning, κ_h = R_h. The seed lies in R_0 and is fixed before any ∀ move, so on every branch "genuine" refers to the same run; this is why it must be announced at the root and not guessed per branch.
- *Completeness.* If N_g(x) accepts at step h ≤ β, ∃ plays honest records and follows Dymond and Tompa's strategy on the genuine DAG on {0..h}, with edges i−1 → i and j_i → i, so in-degree at most 2. The terminal test fires exactly when the pebble game ends, and their Lemma 1 bounds the placements on every play by O(h/log h).
- *Cost.* Each placement costs O(1) guessed words and O(1) word steps, into a table indexed by vertex number in zero-initialized memory, with a presence-flag word per index and addresses below O(β) < 2^w; each ∀ move costs one word and the terminal check O(1). So every path takes O(K) = O(β/log β) word steps, with K computed at the start; this is where the computability of β is used. ∎

The round-three game is the special case in which the address base + j fixes the writer, so no witness is needed and a load of a history cell that step j never wrote reads 0, decided by step j's own record. In general W programs "not yet written" would be a universal claim, which is why the named writer needs model W.

**Dymond–Tompa's Lemma 1, read at source during review** (Waterloo report CS-83-08, report pp. 2–5). Time is the number of pebble placements on a play ("If, even against best defence by the Challenger, the Pebbler can always win the game using at most t pebble placements, then … G can be 2-person pebbled in time t"), so O(1) words per placement is the right price; the Challenger may only stay or move to a vertex pebbled in the Pebbler's most recent move, as the game above models it; and the proof is Paul, Tarjan and Celoni's recursive split, with the recurrence q(m) ≤ max{q(m/2 + m/log₂m) + 2m/log₂m, 2q(m/2 − m/log₂m + d) + d}, whose solution is cited from Paul–Tarjan–Celoni and was not re-derived. [Dymond–Tompa, Waterloo CS-83-08](https://cs.uwaterloo.ca/research/tr/1983/CS-83-08.pdf)

**The inclusion.** By the named-writer lemma, L(P) = {x : ∃g N_g(x) accepts within β} lies in ATIME^word_RAM[O(β/log β)] = ATIME^word_RAM[O(T / log w)]. For w = 12⌈log₂(m+2)⌉ and m ≤ T ≤ 2^{w/2}, log T = Θ(w), so log w = log log T + O(1), and the theorem follows. Every g that halts gives P's answer, and the counter rejects after β. The guesses are the seed, announced at the root and shared by every branch; claims whose content the one-step check recomputes; and the named writer, read only by its own vertex's check, so a local witness. The round-five warning about guessed fields placed per branch therefore does not apply.

## 6. Consequences

**(A), a proof outline; the width bookkeeping is not yet written.** If DTIME_RAM[t] ⊆ ATIME^word_RAM[O(t/log log t)], which the theorem gives in its range, then A_RAM ∉ DTIME_RAM[o(N log log N)], where A_RAM = {(π, x, 1^h) : the alternating program π accepts x within h steps at width w(|x|)}, with the native band's guest-width convention.
- The journal's diagonal J of the [alternation dichotomy](alternation-dichotomy-for-dimacs-sat.md#1-statements) is in DTIME_R[O(n²)], and every deterministic program that halts within n² steps on all long inputs errs on J.
- The theorem at t = Θ(n²) applies, since n² ≤ n^6 and n² is computable in O(1): it gives an alternating program π_J whose branches all halt within s(n) = O(n²/log log n).
- Suppose D decides A_RAM in f(N) = o(N log log N), and let E(x) run D on the virtual instance (π_J, x, 1^{s(n)}). Then N = Θ(n²/log log n) and log log N = log log n + O(1), so N·log log N = Θ(n²), and E decides J in o(n²) ≤ n² steps on long inputs, contradicting the diagonal.
- *Bookkeeping not written*, each item constant overhead by the review's account: E runs at width w(n) while D runs at w(N) ≈ 2w(n); arithmetic in limbs, with division by Knuth's Algorithm D on half-word digits; D's wider addresses through a constant-depth trie in zero-initialized memory, at most 4·f(N) nodes of 2^{w(n)/2} cells; and virtual input words at O(1) each.
- *What it would give.* A_RAM ∈ ATIME^word_RAM[O(N)] by a universal alternating interpreter, as the unary-clock band note argues for U ∈ NTIME[N]. So (A) reads ATIME^word_RAM[O(N)] ⊄ DTIME_RAM[o(N log log N)]: the journal's target (U), ATIME^word_RAM[n] ≠ DTIME_RAM[n] with unboundedly many alternations, in a stronger form, with no collapse and no padding argument. It is a diagonalization plus a non-relativizing speedup, the RAM analogue of the tape fact that DTIME(t) ⊆ ATIME(t/log t) makes the ATIME-complete problem need deterministic time N log N.
- *What it is not.* It is not about SAT, not the alternation criterion (K), which needs few blocks and would bear on SAT, and not the milestone NTIME_RAM[n] ≠ DTIME_RAM[n].

**(B), a restricted-model result with three qualifications.** No suitably write-once RAM decides A_RAM in o(N log N): such a decider D would put A_RAM into ATIME^word_RAM[o(N)] by the named-writer lemma.
1. It covers only explicit-history deciders, where the round-three game applies, and W-legal deciders, through the named writer. Write-once RAMs that read unwritten cells as 0 are not covered: "cell A not written before c" is a universal claim, and the round-five census shows the named-writer game unsound outside W.
2. It needs an alternating time hierarchy for word-priced RAMs, A_RAM ∉ ATIME^word_RAM[o(N)]. Diagonalization with the players swapped would give it, since complementation is free, but the journal states only the deterministic J, and a search found no alternating diagonal.
3. It needs the decider's time bound to be computable in O(f/log f) word steps, for the budget.

It says nothing about general RAMs: path copying converts a general RAM to explicit history at Θ(log) per step, which cancels the gain. The seeded array's conversion at O(log/log log) is what upgrades (B) to (A).

## 7. Computation

**One level at a time, fixed key families, cost averaged over the seed.** `write_once_array_seeded_level_costs.py` simulates the merge (level 2) and the read (level 1, and level 2 with B = 16) with the accounting of the round-five review's large-B Monte Carlo: one probe per scanned key, a packed directory cell, 3 per output key. Its counts are therefore lower than the bound of Section 3, which charges 2 per entry; what it tests is dependence on B and on the key family. The hashes are poly2, the 3-wise polynomial mod 2^61 − 1 with buckets the top bits of the 61-bit value; poly1 = (a·x + b) mod p, only 2-wise independent; ms, multiply-shift (A·x mod 2^64) >> 3 with A odd; and id, no hash. The families are fixed and each run draws a fresh seed. For poly2 it prints:

```
Merge at level 2, cost per update per level, mean over seeds [max over seeds]
  poly2                B=8             B=32            B=128            B=512
  uni        15.99 [17.66]    16.75 [17.28]    16.98 [17.14]    17.03 [17.06]
  rep        10.29 [11.75]    10.38 [11.84]    10.34 [10.91]    10.34 [10.45]
  cons       16.03 [18.31]    16.78 [18.23]    16.98 [17.27]    17.02 [17.07]
  ap32       15.95 [18.11]    16.80 [18.73]    16.98 [17.33]    17.04 [17.08]
  inter      16.09 [20.25]    16.81 [19.11]    16.99 [17.41]    17.02 [17.07]
  hot        15.13 [17.31]    16.55 [17.37]    16.93 [17.16]    17.01 [17.05]
Read at level 1, cost per level with all B - 1 runs present, mean over seeds (s.e. at B >= 512)
  poly2       B=8    B=32   B=128          B=512         B=1024   level 2, B=16
  uni        4.12    4.63    4.63    4.75 ± 0.54    5.12 ± 0.53       4.42
  ap1        3.92    4.33    4.74    4.05 ± 0.49    4.47 ± 0.44       4.99
  ap32       3.79    4.39    4.48    5.13 ± 0.45    5.27 ± 0.47       4.04
  apodd      3.85    4.75    4.36    4.47 ± 0.43    4.75 ± 0.55       4.17
  ap1old     7.90    8.69    9.20    8.48 ± 0.52    8.90 ± 0.45       9.16
  rep        3.75    3.09    3.86    1.00 ± 0.00    1.00 ± 0.00       4.15
  repq       5.38    5.45    5.50    5.40 ± 0.09    5.48 ± 0.09       5.59
```

The merge families are random 40-bit keys (uni), the same B^{ℓ−1} addresses in all B runs (rep), consecutive keys (cons), stride 2^32 (ap32), run r holding the residue r mod B (inter), and one address in every run (hot); 100 seeds, 20 at B = 512. The read families have q absent amid random keys (uni), in the middle of a progression of step 1, 2^20 or 1,000,003 (ap1, ap32, apodd), present only in the oldest run (ap1old), absent in the middle of the same progression in every run (rep), or present in every run (repq); 400 seeds, 60 at B ≥ 512. From B = 128 to 512 the merge cost changes by at most 0.08, and it stays below the large-B limit of about 17.07 of the round-five Monte Carlo; the read shows no dependence on the level. The linear hashes have flat means but heavy tails: for multiply-shift on ap32 the merge means are 15.76, 16.20, 16.82 and 15.44 with maxima 33.00, 36.15, 99.53 and 35.80, and poly1 on ap32 at B = 512 has mean 19.29 and maximum 73.27. The 60-seed rep rows at B ≥ 512 mislead in both directions (poly2 and poly1 show 1.00 because no seed flagged; multiply-shift shows 69.13 because one seed flagged every run), so the repeated-address family was rerun with 200,000 seeds:

```
  rep-read poly2 B=    8 ell=1 seeds=  200000  cost/level mean     3.984 (se 0.019) max      71.0  Pr[flag] 0.11925  B*Pr[flag] 0.954
  rep-read poly2 B=  128 ell=1 seeds=  200000  cost/level mean     4.590 (se 0.093) max    1017.0  Pr[flag] 0.00772  B*Pr[flag] 0.988
  rep-read poly2 B= 1024 ell=1 seeds=  200000  cost/level mean     4.698 (se 0.267) max    7162.0  Pr[flag] 0.00101  B*Pr[flag] 1.029
  rep-read ms    B=    8 ell=1 seeds=  200000  cost/level mean     3.524 (se 0.020) max      50.0  Pr[flag] 0.07860  B*Pr[flag] 0.629
  rep-read ms    B=  512 ell=1 seeds=  200000  cost/level mean     5.249 (se 0.753) max  132350.0  Pr[flag] 0.00126  B*Pr[flag] 0.643
  rep-read poly1 B=  128 ell=1 seeds=  200000  cost/level mean     4.671 (se 0.185) max    8510.0  Pr[flag] 0.00494  B*Pr[flag] 0.632
  rep-read poly1 B=  512 ell=1 seeds=  200000  cost/level mean     3.913 (se 0.272) max   27595.0  Pr[flag] 0.00105  B*Pr[flag] 0.538
```

For poly2, B·Pr[flag] is 0.93 to 1.03 at every B from 8 to 1024, in line with the two-point bound Pr[flag] ≤ κ/B, and the mean stays between 3.98 and 4.70. For multiply-shift the means rise from 3.52 at B = 8 to 4.75–5.25 at B ≥ 128; for poly1 they rise from 3.52 at B = 8 to 4.67 at B = 128, then fall to 3.91 and 3.99 at B = 512 and 1024. With standard errors up to 0.75 the linear hashes' means cannot be told apart from poly2's, but their maxima are larger (132,350 against 3,578 at B = 512); they come from multipliers that place a whole progression in q's coarse bucket. The spot checks give 16.022 for the poly2 merge with 200 seeds (the round-five Monte Carlo gives 16.09), and, without a hash on 40-bit keys, where every key falls in bucket 0, 62.047 per update and 71.000 per read level.

**Multi-level, during review.** `write_once_array_seeded_independent_simulator.py` was written during review from the description of Section 1, after reading the one-level simulator. It runs the full scheme on composite keys with the Barrett formulas of Section 4 and p = nextprime(2^w), in a write-once integer memory with RS fixed from w that aborts on a second write or an unwritten load, builds the bit-scan table, and checks every read against a reference map. On good seeds it found no W-violation and no read error, with mean probes per operation as a fraction of 75·n·(⌊log_B n⌋ + 1):

| w, B, n, seeds | uni | rep | ap | cons | hot | absent |
|---|---|---|---|---|---|---|
| 32, 2, 16384, 20 | 0.154 | 0.102 | 0.155 | 0.155 | 0.093 | 0.154 |
| 32, 4, 16384, 20 | 0.168 | 0.114 | 0.168 | 0.169 | 0.093 | 0.168 |
| 64, 8, 32768, 10 | 0.167 | 0.115 | 0.167 | 0.169 | 0.089 | 0.167 |
| 256, 16, 16384, 5 | 0.192 | 0.118 | 0.191 | 0.194 | 0.102 | 0.192 |

Here rep updates the same √(n/2) addresses cyclically and reads absent addresses in the middle of that progression, which is the three-point configuration with repeated keys in every run; the maximum over seeds is never above 0.20 of the bound. Six kinds of bad seed (a constant hash, a composite p, a wrong ρ, ρ = 0, p = 0, all fields 2^{w+2} − 1), on all six families at (w, B, n) = (32, 4, 4096), (32, 4, 2048) and (64, 8, 4096), gave 108 runs with no W-violation and no read error; the cost rises to 897–1276 probes per operation for a constant hash on uni, and at most to 1,532.68 (a constant hash on cons), so a bad seed only costs steps, which the step counter turns into rejection. Its default suite, at w = 32, B = 4, n = 2048, ends:

```
negative control: W-VIOLATION load of unwritten cell 503319552
negative control 2: W-VIOLATION second write of cell 134217728
default suite: problems 0
```

The two controls load one entry past a run's end and rewrite a directory cell. `write_once_array_seeded_word_fit_check.py` wraps the simulator's memory and asserts that every written value is below 2^w; on the families uni, rep, cons and hot at (w, B, n) = (32, 4, 4096), (64, 8, 8192) and (256, 16, 4096), presence words reached exactly B² bits (16, 64 and 256), entries at most w bits and directory cells at most 13. `write_once_array_seeded_layout_edge_check.py` runs n = 2^{w/2} updates with RS fixed from w:

```
w=16 beta=1 n=256 RS=9: region overflow kind 0 level 0 offset 512 >= 2^9
w=18 beta=1 n=512 RS=11: all 512 updates fit
w=20 beta=1 n=1024 RS=13: all 1024 updates fit
w=20 beta=2 n=1024 RS=13: all 1024 updates fit
w=22 beta=1 n=2048 RS=14: all 2048 updates fit
```

## 8. The three standard tests

- **(a) Fast solver for the hard family?** Not applicable to the seeded array and the inclusion, which are an upper bound for a data structure and a simulation valid for every language. Consequence (A) is about A_RAM, which is not SAT and has no claimed relation to SAT's time.
- **(b) The same for 2-SAT?** Yes. The inclusion puts 2-SAT, like everything in DTIME_RAM[T], into ATIME^word_RAM[O(T/log log T)]; nothing here separates SAT from 2-SAT.
- **(c) The oracle of the [relativized clock](relativized-clock.md).** The seeded array uses only O(1)-word operations and never reads unwritten memory, so as an upper bound it holds in every oracle world. The inclusion does not relativize as proved: the named-writer game needs in-degree at most 2, that is one step reads O(1) words, while one packed query reads a string of arbitrary length, and in that world unwritten memory also reads as zero, which is outside W. The [barrier note](what-any-proof-of-superlinear-sat-time-must-get-past.md#c-the-multilinear-extension-oracle-algebrization-and-the-speedup-counter-world) shows that a relativizing proof of such a speedup cannot exist for the packed-query interface; the proof here avoids that only through the in-degree-2 step DAG.

## 9. Exact obstruction and next steps

1. **Multiply-shift is not covered, and sampling cannot settle it.** The one-seed argument for flags uses only two-point events, but the read's term E[n·1(flag)] and the merge's E[k·X·Z] are three-point events. For a linear hash an arithmetic progression through q makes them strongly correlated (a heuristic, not proved): given that q + j·d lands in q's fine bucket, a·d is close to a multiple of p/j, and then many q + i·d land in q's coarse bucket. The measured tails show this; the means do not decide it. The chain does not need multiply-shift.
2. **Consequence (A)** needs its width bookkeeping written and checked (Section 6).
3. **Remaining checks of the chain:** Paul–Tarjan–Celoni's recurrence solution; the word steps, instrumented; Mak's 1995 thesis (Section 10); and T above 2^{w/2}.
4. **The block count.** The route uses unboundedly many alternations, so it does not feed the alternation criterion (K), which needs few blocks.

## 10. Literature

- **Dymond and Tompa, CS-83-08 (1983 report).** Read at source during review, pp. 2–5: the statement and proof of Lemma 1. The JCSS 1985 version was not read.
- **Paul, Tarjan and Celoni.** The recurrence solution is cited by Dymond and Tompa; not accessed.
- **Searches**, at summary level, returned Dymond and Tompa's DTIME(T) ⊆ ATIME(T/log T) for Turing machines and Paul and Reischuk's earlier T·log log T/log T, and found no statement of DTIME_RAM[t] ⊆ ATIME_RAM[o(t)] for the unit-cost RAM.
- **Mak, "Parallelism Always Helps".** Its abstract simulates a unit-cost RAM running in time T by a CREW PRAM in time O(√T·log T): a PRAM speedup, not an alternating one. The round-three summary read the 1993 report version and judged it dead as a route to the alternating speedup.
- **Mak's 1995 thesis, "The power of parallel time"** (University of Illinois). Its search summary says the parallel speedup holds for the unit-cost RAM, without naming the parallel model; an Illinois report's summary likewise announces "this relationship also holds for RAM's under the unit-cost measure". Neither document was accessed (HTTP 403). If the thesis contains an alternating unit-cost speedup with gain log T, it would supersede the inclusion.
- Wegman–Carter's k-wise independence and Barrett reduction were not used as sources; both facts are proved inline (Sections 3 and 4).
- **Novelty is not established.**

## 11. What is not proved

- Two dependencies of the chain: Paul–Tarjan–Celoni's recurrence solution, cited by Dymond and Tompa and not re-derived; and the word steps, argued and not instrumented here or during review (the review's simulator counts probes and computes the hash with Python integers, not half-word limbs).
- The constants 75, 54 and 19 are upper bounds, not optimized.
- The sparse bit-scan table of B cells (Section 4) is argued only: the review's simulator writes the full 2^B-entry table, and the one-level simulator charges a bit scan without a table.
- The one-level computation uses the review's accounting on fixed key families, B ≤ 1024 (merge B ≤ 512), levels 1 and 2, and the Mersenne prime 2^61 − 1; the multi-level check with the Barrett hash and the fixed layout is the review's simulator.
- Multiply-shift's expectation on progressions is not settled; the chain does not need it.
- Consequence (A) is a proof outline whose width bookkeeping is not written, and nothing here claims that (U) is reached. Consequence (B) holds only with its three qualifications, and the alternating hierarchy it needs is not in the journal.
- T above 2^{w/2} and any route to NTIME_RAM[n] ≠ DTIME_RAM[n] are not treated.
- Novelty is not established (Section 10).
- Nothing about SAT, and no step toward the linear, quadratic or cubic targets. The route's ceiling is the write-once note's: a log log T gain, with unboundedly many alternations and no bit-priced gain.

## Reproducing the checks

Run from `audits/`. No script writes files unless given `--out DIR`.

```
python3 write_once_array_seeded_level_costs.py
python3 write_once_array_seeded_independent_simulator.py
python3 write_once_array_seeded_word_fit_check.py
python3 write_once_array_seeded_layout_edge_check.py
```

The one-level script compiles `write_once_array_seeded_level_costs.cpp` and `write_once_array_seeded_repeated_reads.cpp` into a temporary directory and runs every configuration above, two processes at a time, in about 25 seconds; `--raw` prints every output line. The independent simulator's default suite takes about 5 seconds; its review runs are `cost 32 1 16384 20 uni,rep,ap,cons,hot,absent` (and the same with BETA 2), `cost 64 3 32768 10 …`, `cost 256 4 16384 5 …`, `bad 32 2 4096`, `bad 32 2 2048` and `bad 64 3 4096`, together about ten minutes. The word-fit check takes about 3 seconds and the layout check about one. [One-level costs](../audits/write_once_array_seeded_level_costs.py) · [One-level simulator](../audits/write_once_array_seeded_level_costs.cpp) · [Repeated-address reads](../audits/write_once_array_seeded_repeated_reads.cpp) · [Independent simulator](../audits/write_once_array_seeded_independent_simulator.py) · [Word-fit check](../audits/write_once_array_seeded_word_fit_check.py) · [Layout check](../audits/write_once_array_seeded_layout_edge_check.py)
