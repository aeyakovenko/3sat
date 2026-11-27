# A persistent tradeoff for querying a solver's actual memory

**Research journal, 24 November 2026.** Suppose a fixed correct deterministic SAT solver runs in $O(NL^a)$ time on the specified packed load/store RAM, for fixed $a\ge0$, where $N$ is the explicit input length in bits and $L=\max(2,\lceil\log_2(N+2)\rceil)$. Its workspace is unrestricted. There is a solver-dependent family of unsatisfiable formulas, one at every sufficiently large source padding length, with the following property. Set
$$
 K_N=N/L^{3a+9},\qquad D_N=N/L^{a+6}.
$$
For every integer query-time budget $1\le U\le cK_N/L$, there is an interval of $\Omega(D_N/U)$ consecutive instruction times **strictly before the first halt**. At every time in the interval, every $s$-bit description that answers each writable-memory word query in at most $q\le U$ native evaluator steps satisfies
$$
 s q=\Omega(K_N).
$$
Here $q\ge1$ and the positive constants are independent of $N$ and $U$. In particular, at linear SAT time the same interval of $\Omega(N^{1/2}/\log^6 N)$ consecutive steps enforces $sq=\Omega(N/\log^9 N)$ for every choice of scheme with $q\le\sqrt N$. Another interval of $\Omega(L^{2a+4})$ internal times enforces the **uncapped** bound $(s+L)q=\Omega(K_N)$.

Descriptions may be precomputed with unlimited time from the entire run. The evaluator receives the queried address, actual time, original formula and description length. Each time can have its own description, program and query latency. Even a common, arbitrarily precomputed data bank of at most $c_0 N/L^{a+4}$ bits may be provided to every query. The formula works for all such banks. The hard interval can depend on the bank and the budget $U$. Its memory contents may persist while other instructions execute. Static data structure lower bounds also study supplementary indices with access to the underlying input. Here the query measures ordinary RAM work on the actual state of a program. [Gál and Miltersen](https://doi.org/10.1016/j.tcs.2007.02.047) · [Earlier prescribed-grid bound](solver-snapshot-descriptions.md)

## Checking a schedule with different query clocks

Use the bounded universal machine on a source of $n_0$ bits with clock $H=\Theta(n_0^2)$ and its locally addressable 3-CNF $F_x$ of length $N=\Theta(HL^3)$. Set $T=\lceil CNL^a\rceil$ for a valid bound on the solver. A fixed verifier guesses the common bank $Z$ and a schedule of at most $N$ segments, their increasing endpoints from zero to a proposed rejecting halt $E\le T$, controllers, internal description rows with lengths $s_i$, and integer caps $1\le q_i\le N$. These are data of the verifier. No real exponent or selection algorithm is supplied to it. At time zero use genuine zero work memory with $q_0=1$. There is no terminal memory row.

The evaluator has a fixed word-width coefficient, word-indexed code and data, finite opcode set and bounded-arity instructions. Its general interpreter pays a constant number of native operations per emulated instruction on this common interface. Fresh scratch per word query is implemented by separate bounded address banks or by clearing just the touched words. Code bounds, lengths, timeouts and out-of-bounds reads have fixed deterministic conventions. The selected row, formula and common bank are read-only. One may include a compact code mode that parses a prefix-coded instruction list on each invocation, charging every parsing step to the query clock. This accommodates any fixed program in the common instruction set with a constant bit and time overhead depending on that program. Thus malformed rows denote definite word functions too. Solver constants, the evaluator convention and the source word-width coefficient are fixed before forming the self-input. Every runtime array used on capped guesses has a polynomial address range. Compile the solver and checker using the constant-factor native simulation in the [packed transfer](packed-band-transfer.md) and the [signed-verifier width audit](adaptive-invariant-selectors.md).

Let $g_i=t_{i+1}-t_i$, and let
$$
 R=O\left(1+\max_i\{g_i(q_i+1)\}+\max_i q_i+\operatorname{poly}(L)\right).
$$
After checking the directory and computing an upper clock from it, ask whether any one segment is defective. Start with its proposed controller and addressable memory. A local store overrides the decoded starting memory for the rest of this replay. Check the ending controller, and at a universally challenged address compare the replayed final word with the next description when there is an internal endpoint. Equivalently the defect test *guesses* the mismatching address. For the last segment require a rejecting halt. The clock $R$ charges all starting-row evaluations in a selected segment and its one ending-row evaluation. The replay starts with a clean local overlay. If no defect exists, induction from the genuine initial state forces every internal endpoint to be the true state and gives a genuine rejection. The verifier uses one ordinary, fully materialized SAT call to decide existence of a defect.

Write $m_0=O(n_0+1+\lceil |Z|/L\rceil)$ for the ordinary public words, $S=\sum_i s_i$, $u=\max(1,\max_i s_i)$ and $P$ for the number of segments. A general read-only directory and packed pool cost the following time, including the final $O(n\log^a n)$ SAT call at its own input length:
$$
 O\big(RL^{a+3}+(m_0+P)L^{a+2}+S L^{a+1}+\operatorname{poly}(L)\big). \tag{1}
$$
This uses the [materialized-input conversion](materialized-input-census.md). For the sharper bound, put the timestamps, controllers, query caps and true lengths into the row payloads. The outer verifier checks the directory before compiling the defect instance. Its replay consults two adjacent rows, irrespective of how many addresses it subsequently queries within a row. Grouping either the rows or the columns of each dyadic size bucket gives the following cost, including construction:
$$
 O\big(R L^{a+3}+m_0 L^{a+2}+(S+P L+uL)L^a+\operatorname{poly}(L)\big). \tag{2}
$$
The $PL$ term pays for the metadata of every boundary, and $uL$ pays for random reads of the selected rows. Both terms are needed in this argument. Variable query clocks change a constant number of directory fields and the replay cap. A single verifier can guess a tag and use either construction. [Whole-row selection and the two circuit layouts](bulk-snapshot-selection.md)

On its own padded description, a timely signal makes $F_x$ satisfiable, and the same signal certifies that the correct solver rejects $F_x$. Hence $F_x$ is unsatisfiable and no branch can signal within $H$ source steps. An honest branch proving rejection too cheaply supplies a contradiction. All the following constant choices are made *after* fixing this one program and its simulation overhead. The mathematical choices only identify honest witnesses it could guess.

## Choosing checkpoints from the query time at each instant

Let $E$ now be the actual first rejecting halt. Choose a small positive constant $\gamma$, and put $J=\gamma H/L^{a+3}$. Suppose that a cheap row at time $t$ satisfies
$$
 (s_t+\lambda)q_t\le K,\qquad q_t\le U,
$$
where $\lambda\ge1$, and $J/U$ grows. Its proposed jump is $j_t=\lfloor J/q_t\rfloor$. Start at time zero with no paid row and jump $\lfloor J\rfloor$. Let $w=\lfloor J/(4U)\rfloor$. Suppose every window of $w$ consecutive internal times contains at least one cheap time. If $E\le t+j_t$, finish at $E$. Otherwise choose a cheap checkpoint between $t+\lceil j_t/2\rceil$ and $t+j_t$. The target range contains a full internal $w$-window because $j_t\ge2w$, and ends strictly before $E$. The integer times increase until the process finishes. This argument covers a vacuous window premise on a short run as well; a run already halted at zero can be certified directly. [Finite checkpoint selection in Lean](../lean/PersistentSnapshotIntervals.lean)

Every paid checkpoint except possibly the last is followed by a segment of length at least $j_t/2$. Their proposed jumps sum to at most $2E$, and $J/q_t\le j_t+1\le2j_t$. The cost of the last paid row is at most $K$. Consequently
$$
 \sum_{\rm internal}(s_i+\lambda)\le 4KT/J+K,\qquad
 P=O(1+TU/J),\qquad R=O(J+U+\operatorname{poly}(L)).
 \tag{3}
$$
These inequalities allow unbounded variation of $q_i$ between consecutive rows. A fixed grid for a single query cap cannot give the simultaneous quantifiers in the theorem.

## Paying for the rows

In the greedy construction use $\lambda=L$, $K=\eta K_N$ and $1\le U\le U_{\rm high}=\lfloor\eta K_N/L\rfloor$, where $\eta>0$ is small. We have $T/J=O(L^{2a+6}/\gamma)$, so (3) gives
$$
 S+(P-1)L=O\big((\eta/\gamma)H/L^a\big).
$$
Also $u\le K+1$ and $uL=o(H/L^a)$. The bound on $P$ from (3) gives $P=O((\eta/\gamma)N/L^{a+4})<N$ for all sufficiently large $N$. With the common bank included, (2) takes at most
$$
 O(\gamma H)+O((\eta/\gamma)H)+O(c_0 H)+o(H)
$$
steps including interpretation. First make $\gamma$ small compared with the clock constant. Then choose $\eta$ and $c_0$ small. This would give a timely signal. Some full internal window of length $w=\Omega(D_N/U)$ therefore has no cheap time. This conclusion is simultaneous for the different query bounds at a time because each proposed jump used its own decoder's clock. The program accepts all admissible schedules and banks, so the argument applies on the same formula for every $U,Z$.

For $U\le\eta K_N/(2L)$ subtract $Lq\le\eta K_N/2$ from the window's bound $(s+L)q>\eta K_N$ to obtain the displayed pure bit-time product. At $U=U_{\rm high}$ a still slower decoder already has $(s+L)q>\eta K_N$ since $s+L\ge L$. This yields the uncapped bound on a window of $\Omega(D_N/U_{\rm high})=\Omega(L^{2a+4})$ times, even for clocks above the verifier's cap $N$.

A circuit-size consequence at individual times follows by taking the common bank empty. A size-$g$ bounded-fan-in circuit for the memory word at a given time can be evaluated in $O(g+L)$ native steps from $O((g+L)L)$ bits of circuit description when $g\le N$. In particular apply the result with $U=\lfloor N^{2/3}\rfloor$. Throughout the resulting interval this yields $g=\Omega(\sqrt N/L^{(3a+10)/2})$, since a circuit below that scale has query time below $N^{2/3}$. This statement permits a different circuit at every time.

## What remains unresolved

For $a=0$, the first theorem forces $sq=\Omega(N/\log^9 N)$ throughout its interval on its specified range of query budgets even if the scheme is chosen after seeing both the input and the time. The verifier proves a necessary property of any linear-time solver with unrestricted memory. No upper bound violating this tradeoff on those same runs is known. The result also uses a near-linear SAT algorithm on the small defect instance. Substituting a quadratic or cubic clock into that call changes the cost and does not prove the same assertion for those solvers.
