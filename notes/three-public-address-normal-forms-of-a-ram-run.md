# Three public-address normal forms of a RAM run must be kept apart, and the online form costs at least m − r − ⌊c/w⌋ loads per load

Three "public address" normal forms of a RAM run must be kept apart. (a) An online address-public simulation learns each requested address only when it must answer it. Holding m arbitrary full words, with r registers and c control bits, it loads at least m − r − ⌊c/w⌋ cells per load, and a scan attains this up to an additive constant. This is proved here and no priority is claimed: it is likely folklore for deterministic oblivious RAM. Under the weaker reading, in which only each window's access pattern must be public, a scan prologue already gives one probe per load window, so the online condition is what the bound needs. (b) The verification form and (c) general deterministic address-public simulation are already in the journal, with one correction. For deterministic word-step checkers the verification exponent is at least γ_k, and equality is open; exact networks have exactly γ_k. A tagged table records what each form gives pebble games, counting games and digest protocols. Nothing here is progress on SAT time; the linear, quadratic and cubic questions remain open. [Simulation by exact networks](simulating-a-ram-step-by-exact-networks.md) · [Trace multiplicity](trace-multiplicity-and-list-volume.md) · [Batched last writers](batched-last-writers-and-public-forward-probes.md)

## Where the journal already has each part

| Part | Where the journal already has it | What is left here |
|---|---|---|
| (a), upper bound | Simulation note §2.6: the scan-everything fallback, O(T·(T+n/w)·w) gates | Nothing. A per-load scan of m cells is the same construction. |
| (a), analogues in other measures | List-and-matrix note, second paragraph: one standalone lookup among m words needs Θ(mw) bounded-fan-in gates, and "Costs of composing many reads can be much lower". Capacity-line note, Proposition 4: MC(MUX_k) = 2^k − 1. | The probe statement for address-public RAMs is not in the journal. That is Lemma A below. |
| (a), a related public-probe bound | Batched-last-writers note: a public batch of O(k) forward probes needs Ω(m log m) advice bits to reproduce last writers | A different model (advice, batched targets). Not used. |
| (b) | Simulation note §2.3: c*_net(k) = 1 + γ_k with γ_k ∈ [σ_k, 1]. Batched-last-writers note, last paragraph: in exact networks an explicit history equals one gather plus O(Tw), and "computing the hidden order by an ordinary deterministic circuit incurs an additional cost". | The reading in word steps, and one correction (Section 2.5). |
| Converting word steps to circuits | Trace-multiplicity note: a solver whose address trace is the same on all inputs has circuits of O(n + R + T(g(w)+w)) gates. With g(w) = w^{1+o(1)} it needs (n/w)·w^{σ_3−o(1)} steps on the dense list projection. | Only the deterministic special case, R = 0 (Section 2.5). |
| (b), upper end | Local-sorting note: O(t·h) word comparator slots, uniform | None. |
| (c), floor | The trace-multiplicity note (above). Simulation note §2.4: √w per bit in a field without ports (from the preprint; conditional). Simulation note §2.5: Ω(log T) per step under Li–Li (FHLS, abstract only). | None. |
| (c), ceiling | Simulation note §2.6; in word steps O(T·(T + n/w)) | None. |
| (c) implies sorting | Simulation note §2.5: "fixed-access-pattern (oblivious) simulation of a RAM pays Ω(log T) extra word steps per step, conditionally". This is the radix-sort argument. | None. |

[List and matrix costs](list-and-matrix-costs-for-ram-and-tapes.md) · [Capacity line](the-instruction-capacity-line-is-capped-at-a-packed-scan.md) · [Local sorting](local-sorting-for-parsimonious-ram-encodings.md)

So the new content is (a) as a normal-form statement, plus the table of Section 2.7.

## 1. Definitions and statements

**Model.** The journal's word RAM:
- w-bit words and a fixed program text;
- r registers and c = ⌈log₂(number of program lines)⌉ control bits;
- a read-only input region and zero-initialised work memory.

[Native band](native-unary-clock-band.md)

**Address-public.** A program is address-public if the kind and the address of the access at step s are functions of (s, n) only.

**Public layout of the sources.** The sources below take parameters (m, T′). Fix them as functions of n so that schedules may depend on them, for example m = T′ = the largest power of two with (m + T′ + 1)·w ≤ n, with the remaining bits as padding. Otherwise a scan's schedule would depend on a header word.

**Online public-probe memory (OPM) with parameters (m, w).**
- A deterministic program as above. It is driven by operations o_j = (op_j, a_j, u_j) with op ∈ {load, store}, a_j ∈ [m] and u_j ∈ {0,1}^w.
- o_j is placed in a request register, not counted in r, at the start of window j.
- Window j has a length and an access sequence that depend only on (j, m): the windows and the probes are public.
- At the end of a load window, a designated register must hold the logical content x[a_j]. That is the last value stored at a_j, or 0 if there was none.
- D must be correct on every operation sequence in a prefix-closed set 𝒪. The default is all sequences.
- C_j is the set of cells whose first access within window j is a load. It depends only on (j, m).
- Fix any set A_j ⊆ [m]. S_j is the set of logical contents reachable before window j, over the prefixes in 𝒪 after which every load (load, a, 0) with a ∈ A_j is allowed. Lemma A holds for every such A_j.

**Lemma A.** For every OPM D and every window j at which 𝒪 allows a load,

  w·|C_j| ≥ log₂ |S_j restricted to A_j| − r·w − c.

If 𝒪 is all sequences and j > m, then S_j = ({0,1}^w)^m and A_j = [m], so |C_j| ≥ m − r − ⌊c/w⌋. This equals m − r once w > c. If the simulator's word width is w_Q instead of w, the count reads |C_j| ≥ (m·w − c)/w_Q − r.

**Corollary B (the in-RAM, input-faithful form).**
- *Source P_fresh(m, T′).* The input words are x_0..x_{m−1} and q_1..q_{T′}. P copies x into cells 0..m−1. Then, for j = 1..T′, it reads q_j and loads cell q_j mod m.
- *Simulator.* Let Q be any address-public program with r registers and c control bits that, for each j, holds x_{q_j mod m} in a designated register at a public time τ_j. Let λ_j be the first time Q loads the input cell of q_j.
- *Claim.* For every j, Q loads at least m − r − ⌊c/w⌋ cells other than q_j's cell during [λ_j, τ_j]. If the replies are produced online, i.e. τ_j < λ_{j+1}, then Q makes at least T′·(m − r − ⌊c/w⌋ + 1) loads in all.

**Proposition C (pointer chasing).**
- *Source P_chase(m, T′).* Copy x_0..x_{m−1}. Let a_0 ∈ [m] be an input word (or take a_0 := input word mod m). Then v_j = M[a_{j−1}] and a_j = v_j mod m.
- *Claim.* For m a power of two there is an address-public Q with public windows: m copy windows, the first of which also contains the prologue, then T′ load windows. Every window serves one source step. Q holds (v_j, a_j) in designated registers at the end of load window j, and each load window makes exactly one probe.
- *Cost.* With Batcher's bitonic sorter the prologue costs O((m+T′)·log²(m+T′)·log T′) word steps.

Parts (b) and (c) are restated from the journal in Section 2.5, and the table is in Section 2.7.

## 2. Proofs and checks

### 2.1 Proof of Lemma A

Let h ∈ 𝒪 be a prefix of j − 1 operations, and let σ(h) = (R, κ, M) be D's state at the start of window j: registers, control state and memory. Because D is deterministic and o_j arrives only at the start of window j, σ is a function of h.

Inside window j the access sequence is fixed. By induction over the steps of the window, every register value and every stored value is a function of (R, κ, o_j, M|C_j). A load from a cell in C_j returns that cell's content at the start of the window. A load from any other cell returns a value stored earlier in the window.

So for a load o_j = (load, a, 0), the reply is F(R, κ, a, M|C_j) for one fixed function F. Correctness gives x(h)_a = F(R(h), κ(h), a, M(h)|C_j) for every a ∈ A_j. Hence x(h)|A_j is a function of (R(h), κ(h), M(h)|C_j), and that tuple takes at most 2^{rw + c + w|C_j|} values.

For the second sentence of the lemma, m stores of arbitrary words to distinct addresses reach every x. This gives |C_j| ≥ m − r − c/w. Since |C_j| and m − r are integers, |C_j| ≥ m − r − ⌊c/w⌋. ∎

Remarks.
- **Sharper register term.** The term rw + c can be replaced by the logarithm of the number of distinct pairs (R, κ) at the start of the window. Registers whose values depend only on j, such as loop counters, cost nothing.
- **Tables of small words.** If the stored words are themselves addresses in [m], then |S_j| = m^m. The bound becomes (m·log₂m − rw − c)/w, which is at most about m/12 − r at the journal's width w = 12⌈log₂(n+2)⌉, since m ≤ n. It is still tight up to additive terms: a module can pack ⌊w/log₂m⌋ such values per word and scan ⌈m·log₂m/w⌉ cells. So "m − O(1)" is the full-word case. The sources here copy full input words, so they fall in that case.
- **Stores.** If 𝒪 fixes the kind of each operation (a public kind schedule, as for P_fresh and P_chase), store windows are not bounded by Lemma A: appending each store to a log at a public position costs one probe. Under the default 𝒪, every window j > m can serve a load, so Lemma A bounds every such window. Over a sequence with T′ loads after m arbitrary stores, the total is at least T′·(m − r − ⌊c/w⌋).
- **Pointer chasing under the strong reading.** A generic OPM driven by P_chase still pays m − r − ⌊c/w⌋ per load, because C_j is fixed by j alone and the bound comes from correctness on all sequences. So if "step-faithful" means the source's CPU plus a generic memory module, pointer chasing satisfies (a).

### 2.2 Proof of Corollary B

Fix j and every input word except x and q_j.

The state of Q just before time λ_j depends on the input only through cells loaded before λ_j, and q_j's cell is not among them. So that state is a function of x alone; write it (R(x), κ(x), M(x)).

Let C be the set of cells whose first access in [λ_j, τ_j] is a load. C is public and contains q_j's cell. As in Section 2.1, the designated register at time τ_j holds F(R(x), κ(x), M(x)|C∖{q_j}, q_j). On input cells, M(x) is just the input words there.

Correctness for every value of q_j gives x_a = F(…, a) for all a ∈ [m]. So the map x ↦ (R(x), κ(x), M(x)|C∖{q_j}) is injective on ({0,1}^w)^m, and therefore |C∖{q_j}| ≥ m − r − ⌊c/w⌋. If τ_j < λ_{j+1} for all j, the intervals are disjoint and the counts add. ∎

**Without the online order** the bound holds per interval only, and different intervals may share loads. An offline simulation reads all the queries first and answers them with one oblivious gather: two sorts and a scan. With AKS or columnsort this costs O((m+T′)·log(m+T′)) word steps. That is the general or verification regime, not (a).

### 2.3 Attainment

Store x verbatim. Keep k words in registers and scan the other m − k cells, choosing the reply with a branch-free equality select. Store windows also scan, writing the new word back with a select (or a pending store is flushed during the next scan). A load window then loads m − k cells and uses r = k + r_0 registers, where the number r_0 = O(1) of scratch registers is fixed by the instruction set. Hence

  m − r − ⌊c/w⌋ ≤ min_Q |C_j| ≤ m − r + r_0.

The constant is pinned up to r_0 + ⌊c/w⌋, in the regime c < w, which a scan with O(1) or O(k) code lines satisfies. The case k = 0 is run as Check 2 below.

### 2.4 Proposition C, and the finite checks

**Construction of Q_weak.**
1. *The prologue, which in the claim's window structure is merged into the first copy window; the script logs it separately and the trace is the same.*
   - Read x and a_0, and set F_0[i] = x_i mod m.
   - Compute F_{k+1} = F_k ∘ F_k with one oblivious gather per k:
     - sort the table records and query records by (key, tag) with a bitonic network;
     - propagate each table value along its key group with a branch-free scan;
     - sort the records back by query index.
   - Compute A[j] = f^j(a_0) for j < T′ by applying F_k to the public set of j whose bit k is set.
   - Compute V[j] = x[A[j−1]] with one more gather.
2. *Windows 1..m.* Copy x_i into cell i, mirroring P's stores.
3. *Load window j.* Load V[j] (one probe) and set a = v AND (m − 1).

Every index condition in the bitonic network is arithmetic in the loop counters, so a uniform version with one fixed program text exists (paper argument). The script instead runs per-size control: Python loops over public ranges.

**The toy check.** `public_address_simulation_toy_check.py` runs both simulations on a logged toy word RAM, in about 20 seconds. Check 1 runs Q_weak against P_chase; Check 2 runs the scan Q_scan against P_fresh. Key output lines:

```
negative control (direct pointer chase, m=4 b=2 T'=3): distinct traces=52 (must be > 1)
Q_weak  exhaustive m=4  b=2 T'=8  inputs=1024   identical_trace=True register_mismatches=0 probes_per_load_window=1 trace_len=3249 prologue_ops=3225 scan_cost_m*T'=32
Q_weak  exhaustive m=4  b=3 T'=6  inputs=16384  identical_trace=True register_mismatches=0 probes_per_load_window=1 trace_len=3195 prologue_ops=3175 scan_cost_m*T'=24
Q_weak  sampled    m=8  b=4 T'=12 inputs=300    identical_trace=True register_mismatches=0 probes_per_load_window=1 trace_len=11637 prologue_ops=11597 scan_cost_m*T'=96
Q_weak  sampled    m=16 b=5 T'=20 inputs=100    identical_trace=True register_mismatches=0 probes_per_load_window=1 trace_len=38829 prologue_ops=38757 scan_cost_m*T'=320
Q_scan  exhaustive m=4  b=3 T'=2  inputs=262144 identical_trace=True reply_mismatches=0 loads_per_window=5 (=1+m) first_read_of_q_j_inside_window_j=True tau_j<lambda_j+1=True
TOTAL mismatches: 0
```

The full run also covers every m = 2, 4 with T′ = 1..8 and every Q_scan size. For Q_scan the script records each window's start and end in the log. It asserts that the first load of q_j's input cell falls inside window j, and that window j ends before q_{j+1} is first read.

**What the trace test certifies.** The trace is the full operation log: every memory access with its kind and address, and every ALU operation by name. All data-dependent choices go through logged ALU operations whose logged names do not depend on the data. So identical traces over all inputs certify, at these sizes, a public memory schedule and an input-independent control flow. The negative control, which loads directly at the data address, gives 52 distinct traces, so the test does detect data-dependent addresses. Records of O(1) words are stored as tuples in one cell; this is a toy simplification.

**Independent check.** `public_address_simulation_independent_check.py`, written during review, uses integer words and packs records into one integer, with no tuples. It takes about 30 seconds:
- R1 uses a different prologue, branch-free scans of the read-only input, exhaustive at m = 2 and 4;
- R2 uses pointer doubling with Batcher's odd-even merge sort instead of the bitonic sorter, exhaustive at m = 2 and 4 and sampled at m = 8 and 16, and counts the prologue's operations;
- R3 runs an offline simulator for P_fresh;
- R4 is the negative control.

```
R4 negative control m=4 b=2 T=3: distinct traces = 52
R1 scan-prologue m=4 b=3 T=4 inputs=16384 identical=True mismatches=0 probes/load-window=1 prologue_len=57
R2 doubling(oddeven-merge) m=16 b=5 T=33 inputs=60 identical=True mismatches=0 probes/load-window=1 prologue_ops=44246 m*T=528
R2 cost (formula) k=16 m=T=2^16 prologue_ops=4.12e+09 m*T=4.29e+09 ratio=0.960  pro/((m+T)log2^2(m+T)log2 T)=6.80
R3 offline P_fresh m=4 b=3 T=2 identical=True mismatches=0 online_order_holds={False} min_loads_in_[lambda_j,tau_j]_excl_qj=6 (>= m - O(1))
```

**What the checks show, and what they do not.**
- *Per window.* The literal reading of (a) fails under the weak reading already at m = 4: one probe per load window instead of at least m − r.
- *Any oblivious prologue works.* A prologue that precomputes v_1..v_{T′} by branch-free scans of the read-only input, Θ(m·T′) in total, already gives one probe per load window (R1). So the per-window refutation is the definitional point, and pointer doubling matters only for the total cost.
- *Total cost.* At these toy sizes the doubling prologue costs far more than the scan's m·T′: 38,757 operations against 320 at m = 16. Its O((m+T′)·log²(m+T′)·log T′) cost is a paper count. The independent check's closed-form count matches its measured counts for m = T′ = 2^4..2^8 and puts the crossover with m·T′ at about m = T′ = 2^16. The refutation does not need the total-cost version.
- *The online order.* The offline simulator of R3 violates τ_j < λ_{j+1}, and each interval [λ_j, τ_j] still holds at least 6 loads other than q_j's cell at m = 4. This agrees with Corollary B: the per-interval bound holds, and the counts add only under the online order.
- *Bounded windows (remark, not checked).* For T′ = O(m), the prologue can be cut into pieces of O(log³ m) steps placed inside the m copy windows. So even a uniform bound on the length of every window does not rescue the literal (a).

**Conclusion.** Under the weak reading, (a) is false for pointer chasing. What (a) needs is freshness of the requested address relative to the simulator's state, which Corollary B makes explicit as λ_j ≤ τ_j < λ_{j+1}. "Addresses taken from loaded words" does not supply it, because a deterministic source's addresses are functions of an input the simulator may read at the start.

### 2.5 Parts (b) and (c), from the journal, with one correction

**Conversion to circuits.**
- An address-public program satisfies the clocked-slot hypothesis of the trace-multiplicity note with R = 0, because its trace is one fixed sequence.
- That note's simulation then gives a circuit of O(n + S·(g(w)+w)) gates for an S-step address-public program, and the circuit converts to a k-network with linear overhead.
- Here g(w) = w^{1+o(1)}, using Schönhage–Strassen multiplication and Newton division as in simulation note §2.1. With O(w²) schoolbook circuits, the floors below become vacuous.

**(b) Verification form.**
- *Lower bound.* An address-public deterministic checker of claimed T-step histories, with the load replies given, decides G_w on m = T/2 rows: store the table, then make m loads with claimed replies. So S ≥ vol_k(G_w)/w^{1+o(1)} ≥ m·w^{σ_k−o(1)}, by the read-only lookups note.
- *Upper bound.* Sorting by (address, time) with the uniform O(t·h) comparator slots of the local-sorting note gives S = O(T log T).
- *Exponent.* Define the deterministic verification exponent θ_ver like γ_k, with the word steps S of the best address-public checker in place of volume/w. Then θ_ver lies in [σ_k, 1]. Evaluating the bound along the subsequence that attains γ_k's limsup gives θ_ver ≥ γ_k.
- **The correction.** θ_ver is not simply the journal's γ_k. γ_k is a network exponent, and networks sum over the hidden order; for a deterministic circuit the batched-last-writers note says computing that order "incurs an additional cost". Whether θ_ver = γ_k is open. For exact networks the corresponding exponent is exactly γ_k, with per-step exponent 1 + γ_k (simulation note §2.3). The correction concerns deterministic address-public checkers counted in word steps, so it does not contradict the journal.
- *Input size.* This form takes Θ(T) reply words as input. That is the kind of commitment made by the description-first games note and by the round-two access-log entry (a code of the address-sorted store log) and QBF entry (claimed last writers).

[Read-only lookups](circuits-for-read-only-batched-word-lookups.md) · [Description-first games](description-first-games-fail-on-one-hard-table-opponent.md) · [Round two](parallel-proof-attempts-of-27-november-and-why-each-stopped.md)

**(c) General deterministic form.** Let f(T) be the cost per source step. Then:
- f ≥ (log T)^{σ_k−o(1)} for every finite field k. This is the deterministic case of the trace-multiplicity note, applied to D_w, which a RAM decides in O(N) steps.
- f ≥ (log T)^{1/2−o(1)} if some characteristic has no ports (simulation note §2.4; from the preprint, unchecked).
- f = Ω(log T) under Li–Li (simulation note §2.5; FHLS abstract only), because radix sort is a linear-time RAM program.
- f = O(m) with m ≤ T + n/w (simulation note §2.6, in word steps).

f = polylog T would give deterministic circuits of size T·polylog T through the conversion above. So it implies a positive answer to the open c*_det question (c*_det < ∞) in its uniform form. This is not an equivalence: the converse needs circuits that are uniform and can be evaluated address-publicly. No sub-quadratic deterministic ceiling for general RAMs is in the journal or known here.

### 2.6 Register-public control

The round-three path-parity entry works with runs whose control is public. Read here as register-public control, this means the control registers may read the input but never a data word.
- **Pointer chasing enters this class after one rewrite.** Replace its memory loads by input reads: the control computes a_j by reading input word a_{j−1} in the read-only copy, which equals M[a_{j−1}]. So no costly conversion is needed and no bound arises.
- **What a resistant source would need.** Its addresses would have to be computed data, for example words produced by arithmetic on earlier loads and then stored.
- **What proving it would take.** One would have to show that an O(1)-word process reading the input cannot recompute those addresses within a given time. That is a time–space lower bound for machines with O(log n) bits of space. With unlimited time, every logspace-computable address function is recomputable.

No source is named here as satisfying the condition.

### 2.7 What each form gives to games and protocols

**Targets.**
- (K): the criterion of the alternation note, J ∈ ATIME[O(t/log^{1+ε} t)] with o(log log t) blocks.
- (U): unboundedly many alternations, ATIME^word_RAM[n] ≠ DTIME_RAM[n].

[Alternation criterion](alternating-native-speedup.md)

**Tags.**
- [J]: a journal note.
- [P]: proved here.
- [R]: a reading, not checked.
- [A]: an unrefereed attempt, recorded in a round summary. In round three: the truth-claim, path-parity, rounds-against-pebbles and equality-digest entries. In round two: the access-log and QBF entries.

[Round three](parallel-proof-attempts-of-27-november-round-three.md)

| Form (cost per source step) | Pebble games: Dymond–Tompa, truth-claim games, rounds against pebbles | Path-parity counting game | Equality-digest protocol |
|---|---|---|---|
| **Step-faithful public trace, online.** ≥ m − r − ⌊c/w⌋ loads per load [P]; a scan attains m − r + O(1) [P] | The DAG is explicit, but the run grows by a factor Θ(m). For DAG-agnostic pebbling, a gain of one logarithm leaves s ≫ t, so s breaks for (K) and for (U). On chained loads the converted DAG also has depth ≥ T′, so depth-based evaluation gains nothing [P+R] | The schedule is public, but every load is an m-way select (nonlinear). On chained loads the nonlinear depth is δ ≥ T′, so s breaks. k = Θ(log t·log N) in any case [R; A] | Predecessors are public, so the digest is unnecessary and the protocol reduces to the pebble column, on a run Θ(m) times longer [R] |
| **Verification form, replies given.** Between T(log T)^{σ_k−o(1)} and O(T log T) [J]. The exponent is ≥ γ_k; equality is open [J+R] | The DAG is explicit only after Θ(T) reply words have been guessed. So b = Θ(t·w), which breaks b for (K); for (U) the guess alone costs Θ(t), which breaks s [J: description-first games note; A: round-two access-log and QBF entries] | The replies become input, so control is public, but the same commitment breaks b and s [R] | This is the equality-digest entry's own setting: the digest replaces the commitment. The open step is a sound digest [A] |
| **General deterministic address-public.** f(T) ∈ [(log T)^{σ_k−o(1)}, O(m)], and Ω(log T) under Li–Li [J] | **DAG-agnostic pebbling only**, i.e. using only the gain guaranteed on every bounded-degree DAG. Dymond–Tompa guarantees one logarithm, so the alternating time is T·f/log(T·f), below T iff f = o(log T): open, and false under Li–Li. For (K), the Θ(log R) gain with R rounds of the rounds-against-pebbles entry is the universal gain; its O(log R) cap is on graphs chosen for each R, so it caps only DAG-agnostic R-round pebbling. A simulation whose DAG has pebbling price or depth well below S/log S would gain more, and nothing cited excludes one [R] | The form supplies public control, but the simulation adds nonlinear depth (comparators). k = Θ(log t·log N) breaks k for (K) [A+R] | Predecessors are public, so each load record can be checked against its public predecessor. The digest is unnecessary, and the protocol reduces to the pebble column with overhead f [R] |
| **Write-once.** Its cost is a separate round-four question, not yet recorded | This is an explicit-history machine. The truth-claim entry gives ATIME(T·g/log T), where g is the conversion overhead, so this route reaches (U) if g = o(log T); for DAG-agnostic pebbling also only if [A]. For DAG-agnostic pebbling, (K) is capped by the rounds-against-pebbles bound [A] | Not applicable: the addresses are data-dependent [R] | Not analysed [R] |

**Scope.** Randomized obliviousness is a different object: equality in law of access patterns, online oblivious RAM with O(log m) to polylogarithmic overhead, and Larsen and Nielsen's Ω(log m) bound. Nothing is claimed about it, and the journal's RAM is deterministic. [Larsen–Nielsen (not read)](https://users-cs.au.dk/larsen/papers/oram.pdf)

## 3. The three standard tests (for Lemma A and Corollary B)

- **(a) Does the hard family have a fast globally correct solver?** Yes. P_fresh runs in O(m + T′) steps, and so does P_chase. Lemma A bounds a class of simulations, not the time of any language.
- **(b) 2-SAT.** The argument does not depend on the language. A step-faithful address-public version of a linear-time 2-SAT solver pays the same ≥ m − r per fresh load. So the bound does not separate SAT from 2-SAT and cannot be a SAT bound, which is as it should be for a statement about simulations.
- **(c) The oracle of the relativized-clock note.** The count charges w bits per probe.
  - One query instruction of that note reads an arbitrarily long packed string (ω(w) bits), so it can "probe" the whole memory in one instruction. The probe count is void relative to that oracle.
  - The bit count w·|C_j| survives, trivially.
  - So the lemma uses exactly the property the barrier demands, that one instruction reads O(w) bits. It does not by itself supply a lower bound.

[Relativized clock](relativized-clock.md)

## 4. Exact obstruction and next step

**Status of each form.**
- Step-faithful (online) public traces are dead unconditionally: Θ(m) per load (Lemma A, Corollary B).
- The verification form is a commitment to Θ(T) words.
- For DAG-agnostic pebbling (only the universal one-logarithm gain of Dymond–Tompa), the general form gives a speedup only if f(T) = o(log T), a word-step overhead below one logarithm per step. Via radix sort that would give address-public sorting in o(T log T), which Li–Li forbids (simulation note §2.5, conditional). So DAG-agnostic pebbling after the general form reaches (U) only if Li–Li fails. For (K), the universal Θ(log R) gain with o(log log t) rounds is far too small.
- These conclusions do not cover a simulation whose access DAG has pebbling price or depth well below S/log S. Nothing cited here excludes one. For a T-step sequential run such a DAG would be a strong parallelisation, so none is expected for general RAMs, but that is not proved.
- The one normal form left that can feed pebbling without public addresses is the write-once form.

**Next step, if this line continues.**
- An unconditional f(T) = Ω(log T) for address-public deterministic simulation would close the general row for DAG-agnostic pebbling and (U). The journal's best floor is (log T)^{σ_k}, and the list technique cannot exceed one logarithm here. [Technique ceiling](the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md)
- Separately, one needs a lower bound on the pebbling price of the access DAG of every address-public simulation of some explicit RAM family.
- The opposite outcome would be an address-public simulation with f = o(log T), or with a low-price DAG, for a natural RAM class.
- None of these has been tried.

## 5. What is not proved

- Lemma A and Corollary B are counting statements about classes of simulations. They give no time bound for any language and nothing about SAT.
- The literal (a) is refuted only under the weak reading. The prologue's asymptotic cost is a paper count. The uniform version and the window-spreading remark were not checked.
- The tightness constant r_0 was not computed for the journal's instruction set.
- Priority: the counting is elementary and probably folklore for deterministic oblivious RAM. One search, reading result snippets only, found no statement of it. No priority is claimed.
- Parts (b) and (c) rest on the journal's notes and, where the journal says so, on the 24 November preprints. The Li–Li and FHLS statements are conditional and taken from abstracts.
- The cells of the table tagged [R] are readings, and those tagged [A] rest on unrefereed attempt entries. The path-parity and equality-digest cells were not checked against those entries during review.

## Reproducing the checks

Run from `audits/`; neither script writes files.

```
python3 public_address_simulation_toy_check.py
python3 public_address_simulation_independent_check.py
```

The toy check takes about 20 seconds (`quick` as an argument runs smaller sizes in about 4); the independent check takes about 30 seconds. [Toy check](../audits/public_address_simulation_toy_check.py) · [Independent check](../audits/public_address_simulation_independent_check.py)
