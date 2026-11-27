# A golden-ratio lower bound on cumulative writable memory for SAT

**Research journal, 24 November 2026.** On the packed logarithmic-word RAM let $E(F)$ be the time at which a deterministic solver first signals that $F$ is unsatisfiable. Define the cost of this computation by
$$
 C_A(F)=\sum_{0\le t<E(F)}(1+\#\{a:M_t[a]\ne0\}).
$$
Memory is initially zero, $M_t$ is the writable array before instruction $t$, and the input is read-only. Addresses and values take a constant number of words. The additive one charges time and suffices for a fixed number of controller registers up to constant factors. Clearing a word removes it from subsequent charges. Arbitrarily large workspaces are allowed.

**Theorem.** Put $\varphi=(1+\sqrt5)/2$. For every fixed $c<\varphi$, no deterministic solver for ordinary explicit SAT has $C_A(F)=O(N^c)$ on all unsatisfiable formulas of encoded length $N$. In fact the program need only signal on every unsatisfiable input and never give that signal on a satisfiable one. The cost on satisfiable instances can be unbounded.

More generally, suppose unsatisfiability has a sound nondeterministic recognizer with some accepting path of time $O(N^d)$ on every unsatisfiable formula, $d\ge1$. A separate deterministic, sound recognizer for unsatisfiability cannot have cumulative cost $O(N^c)$ on all such inputs if
$$
 d(c-1)<1 .
$$
Taking the same deterministic program as the reference gives the first statement because its time is bounded by its cumulative cost. The quantifier over inputs is worst case. For every claimed constant and every length threshold there is a larger unsatisfiable instance violating the proposed bound.

Ryan Williams established the golden-ratio exponent for the product of time and maximum space. A bound from below on that product alone does not give the same bound on the sum here, since the maximum may be attained only briefly. Beame and Kornerup study cumulative memory and establish transfers from several types of time-space arguments. Our proof selects sparse states along an actual rejecting run before applying a complementary simulation. Priority for this SAT cumulative-cost formulation has not been established. [Williams, Theorem 4.11](https://people.csail.mit.edu/rrw/automated-lbs.pdf) · [Beame and Kornerup](https://arxiv.org/abs/2301.05680) · [Fortnow, Lipton, van Melkebeek and Viglas](https://lance.fortnow.com/papers/files/tst.pdf)

## Certifying a low-cumulative computation

Let a fixed deterministic program on a public input have a genuine signaling computation of cost $C$ and duration $E$. In each full window of $w\ge1$ successive internal times choose a time minimizing $1+\#\operatorname{supp}(M_t)$. Take zero and the signaling halt as endpoints. Every gap is at most $2w$, including the last partial window. The sum over selected internal times of $1+\#\operatorname{supp}(M_t)$ is at most $C/w$. This follows by charging $w$ times each minimum to its disjoint window. For zero or short runs one can go directly from the initial state to the signal. [Formal selection and cost bound](../lean/CumulativeSnapshotCuts.lean)

Supply a controller at each internal endpoint and its sorted list of nonzero address–value pairs. Addresses absent from a genuine list return zero. Including directory offsets, counts, times and final controller, the whole witness uses $O(1+C/w)$ words. A nondeterministic verifier for a *defect* chooses an interval, replays it, and tests its ending controller and one freely chosen address of the next claimed memory. Loads consult a local write overlay first, then binary-search the starting list. The initial state is genuine, and the final check requires the actual signal. Fix a bounded, total word-return convention on all purported lists. Sorting and uniqueness are necessary only for the honest encoding; any total decoded array passing all checks satisfies the same induction. The directory, range bounds, clock and increasing times are checked, and the selected interval is guaranteed to have at most $2w$ steps. An interval ending at the terminal signal need not compare a final memory. If a signaling halt exists, the honest lists pass. Conversely, if no defect exists, determinism implies that all described states are genuine and the signal occurs.

For a public input of $m$ words the defect machine has input $O(m+1+C/w)$ words and runs in $O((w+1)\operatorname{polylog} H)$ time for all well-formed directories, with $H$ a polynomial upper scale for the quantities here. The outer recognizer checks the directory by a linear scan and makes the defect machine receive only verified public data and tagged array bounds. Bad syntactic data simply cause the outer branch to fail. Each selected word, including a word in the original input, can be read directly by its computed index. No whole table scan is charged to a replay. Repeated reads, zero writes, previously unmentioned addresses and late use of an unchanged word are covered by the all-address check.

## A complementary simulation with a separate input cost

Let an arbitrary fixed nondeterministic RAM have a step budget $R$ on $m$ public words, and put $H=\max(R,m,2)$. The notation $\widetilde O$ suppresses fixed powers of $\log H$ at each finite stage. We consider smooth polynomial clocks, with fixed rational powers and arbitrarily small constant exponent slack. Initially its nonacceptance has a nondeterministic certificate verifiable in $\widetilde O(R^d+m^d)$ time by materializing the usual explicit bounded-computation 3-CNF and running the reference UNSAT recognizer. The reduction size and construction time are $H\operatorname{polylog}H$. A satisfiable bounded-computation formula cannot receive an accepting certificate. A global cutoff loses no promised timely accepting branch. [Locally accessible bounded RAM formula](packed-band-transfer.md)

Suppose more generally that such nonacceptance can be recognized in time $\widetilde O(R^e+m^d)$ with $1\le e\le d$. We now use the *deterministic cumulative-cost* hypothesis. Form the virtual formula for acceptance of the original machine within its budget $R$. Follow the deterministic UNSAT recognizer on this formula up to its own signal. On genuine nonacceptance it signals with cumulative cost $\widetilde O(H^c)$. Each of its native input reads is simulated by the bounded-formula generator with the original input as an immutable bank. Store the sparse native work array directly in a separate bank of a sufficiently wide simulator. The generator requires only $\operatorname{polylog}H$ setup, scratch and per-step overhead, never a writable copy of the full formula. In particular, the simulator also has cumulative cost $\widetilde O(H^c)$ because a polylogarithmic persistent table or per-instruction overhead multiplies the sum by at most a fixed polylogarithm. The time term in that sum pays for intervals when the work array is empty. This distinction matters because materializing a long formula as writable persistent state could destroy the cumulative bound.

Choose $w=\lceil H^x\rceil$, with $0<x<c$. Guess and check the directory and lists above, capping their length by $\widetilde O(H^{c-x}+1)$. Use the previously derived **nondeterministic nonacceptance** procedure on the nondeterministic defect machine. The relevant work and public input of this last machine are respectively $\widetilde O(H^x)$ and $\widetilde O(m+H^{c-x})$. This produces a certificate for original nonacceptance in time
$$
 \widetilde O\big(H^{xe}+H^{(c-x)d}+m^d\big).
$$
The cost of guessing and checking the whole witness fits the second term since $d\ge1$. This use of the prior procedure does not raise the *whole original horizon* to the power $e$. It acts on the shorter segment test, while the full list is charged in the input term. It also does not require the deterministic recognizer to halt on satisfiable instances. Any accepted proof would imply that the recognizer signaled genuinely. Every successful branch and every guess is bounded before the hierarchy simulation. As $H=\max(R,m,2)$, when the new work exponent is at most $d$, $H$ can again be replaced by $R$ in the work term while retaining $m^d$.

For precise clock bookkeeping, each stage may use a common original scale in binary metadata and fixed polynomial-times-polylog padded dimensions. The hierarchy instance below starts with its input length a fixed power of the source clock. Every fixed-depth subcall in that application has a positive polynomial replay allowance in its parent scale, so its word widths are fixed-factor comparable, and fixed powers of either logarithm can be absorbed. One can pad the public directory to its announced capacity without changing the displayed input term. Equivalently, bound unused clocks using rational exponents with a small strict margin at each of the finitely many stages. The local simulation uses only ordinary bounded-width instructions.

## Why the exponent is the golden ratio

Balance the two work exponents using $x=cd/(e+d)$. A single step replaces $e$ by
$$
 e'=\frac{cde}{e+d}.
$$
Start with $e_0=d$. In the nontrivial range $1<c<2$, the positive iterates converge to $d(c-1)$, since
$$
 \frac1{e_{j+1}}=\frac1c\frac1{e_j}+\frac1{cd}.
$$
They are decreasing until they cross one whenever $d(c-1)<1$. With $d\ge1$ that inequality itself implies $c<2$. If $c\le1$, relax the hypothesis to an exponent slightly above one. The boundary $d=1$ allows the first step to drop below one. For real supplied bounds one may first slightly increase both $c,d$ to rationals preserving the strict inequality, and absorb all fixed logarithmic losses in the final strict margin. This also covers a near-linear reference time up to polylogarithms by relaxation. Every recursive use of the speedup prior to the final crossing has $e\ge1$.

The resulting fixed nondeterministic procedure certifies nonacceptance in time $\widetilde O(R^{e_j}+m^d)$ with $e_j<1$. On a universal diagonal with source clock $R=m^K$ for any sufficiently large fixed integer $K>d$, this is $o(R)$. The bounded nondeterministic interpreter gives the contradiction. On its own padded program description, set the distinguished success halt to the sign tested by the interpreter. A timely success would certify that no timely success exists. If there is no timely success, completeness supplies one within the smaller clock. Universal simulation of this one fixed program costs only a constant factor (or polylogarithmic overhead within the strict power gap). [Bounded diagonal and native widths](packed-band-transfer.md) · [Complementary-time hierarchy and checkpoint method](https://lance.fortnow.com/papers/files/tst.pdf)

## If the reference recognizer is near-linear

Write $L=\max(2,\lceil\log_2(N+2)\rceil)$. There is a quantitative one-stage result. If the reference recognizes UNSAT in $O(NL^a)$ time, then for **each** deterministic sound UNSAT recognizer $A$ accepting every unsatisfiable formula there is a family of unsatisfiable inputs on which
$$
 C_A(F)=\Omega(N^2/L^{2a+10}).
$$
The reference may be nondeterministic. The target can be arbitrarily slow on other inputs.

For this statement take a signed bounded-interpreter formula of length $N=\Theta(hL^3)$ and $h=\Theta(n_0^2)$. Set $C_F=C_A(F)$. A support of $k$ nonzero words requires cumulative cost $\Omega(k^2)$ when $k$ exceeds a fixed constant, since initially there are none and only a bounded number of words can become nonzero per instruction. Use the minimum-occupancy cuts above, and encode each honest selected memory by a static perfect hash table of $O(1+k)$ words with its keys and values. It answers a word lookup in constant native time. This step uses the specified ordinary word arithmetic including multiplication and division; a fixed number of words suffice for intermediate products. The verifier treats out-of-range queries, malformed fields and timeouts by fixed total conventions. Tables need only be easy to read. The prover may construct them without a time bound. [Fredman, Komlós and Szemerédi](https://www.cs.princeton.edu/courses/archive/fall09/cos521/Handouts/storingasparse.pdf)

Use $w=\max(1,\lceil\sqrt{C_F}/L\rceil)$ in the honest branch. The number of rows is $O(1+C_F/w)$, the total payload is $O((1+C_F/w)L)$ bits, and the longest row has $O((1+\sqrt{C_F})L)$ bits. A single defect query chooses only two adjacent rows. By the [whole-row construction](bulk-snapshot-selection.md), its encoded length and construction time are
$$
 O\big(wL^3+(1+C_F/w)L+(1+\sqrt{C_F})L^2+n_0L^2+\operatorname{poly}(L)\big)
 = O\big(\sqrt{C_F}\,L^2+n_0L^2+\operatorname{poly}(L)\big).
$$
If $C_F\le\eta N^2/L^{2a+10}$ for sufficiently small fixed $\eta$, the number of rows is below $N$ and the reference's accepting UNSAT branch, together with construction, fits inside $h$. The verifier guesses the schedule and table lengths; it need not know $C_F$ or the analytic optimum $w$. On this verifier's padded self-input a timely signal certifies a real UNSAT signal by the target, while making its own formula satisfiable. Hence the formula is unsatisfiable and cannot have the proposed cheap target run. This gives the family and the lower bound. Time zero and very short runs can be checked directly.

## Relation to elapsed time

A $T$-step word RAM can write to $O(T)$ distinct words, so it can accumulate $O(T^2)$ word-steps. In particular a hypothetical $O(N)$ SAT algorithm can have cumulative cost of order $N^2$. With the resulting exponents $d=1$ and $c=2$, the recurrence starts at $e_0=1$ and gives $e_j=1$ at every depth. The recursion then supplies no strict time saving. The [snapshot query bound](persistent-snapshot-query-cost.md) supplies a different obstruction along actual intervals of a near-linear solver. None of these results excludes unrestricted linear, quadratic or cubic running time.
