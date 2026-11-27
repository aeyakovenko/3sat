# The cumulative length of queryable SAT solver states

**Research journal, 24 November 2026.** Fix an ordinary deterministic SAT solver on the packed logarithmic-word RAM and a uniform RAM evaluator. For an unsatisfiable formula $F$ of bit length $N$, consider each instruction time $0\le t<E$ before the solver first rejects. Let $s_t$ be the minimum length of a string from which the evaluator can return the true value of **any** writable word at time $t$, with a fixed worst-case query budget $Q(N)$. The evaluator gets the original read-only formula, time, address and string length. The chosen strings can depend on the entire run and can include different programs at different times. Charge instruction steps and initialize private decoder scratch on every call. There is no bound on preprocessing. The cost is
$$
 D_{A,Q}(F)=\sum_{0\le t<E}(1+s_t).
$$
Use $s_t=\infty$ if no string works. On a run whose time fits no fixed polynomial, the time term itself violates every polynomial bound under consideration. Formally the decoder can receive $t$ in a read-only binary field; on all hypothesized cheap runs it occupies a constant number of native words. A fixed uniform interpreter can also serve as the evaluator, with its instruction and data encoding charged in the string. These choices yield a conditional, word-query version of resource-bounded description length. [Allender on indexed decoding and the KT measure](https://people.cs.rutgers.edu/~allender/papers/fsttcs01.pdf) · [Packed decoder convention](persistent-snapshot-query-cost.md)

**Theorem.** For any fixed polylogarithmic query budget and every fixed $c<(1+\sqrt5)/2$, the worst-case $D_{A,Q}$ on unsatisfiable inputs is not $O(N^c)$. This applies to every correct deterministic solver with unrestricted workspace. Even each instruction's independently optimal description must be charged in the sum. The hypothesis requires no common compression algorithm and the proof does not compute the minimum descriptions.

More generally let $Q(N)\le N^\beta\operatorname{polylog}N$ for some fixed $0\le\beta<1$, and suppose a sound nondeterministic reference recognizer for UNSAT has an accepting path of length $O(N^d)$ on every unsatisfiable input. For $c,d\ge1$, a sound deterministic recognizer signaling on all such inputs cannot have $D_{A,Q}=O(N^c)$ if $d(c+\beta-1)<1$. Using the deterministic program as its own reference gives the unconditional threshold
$$
 c < \frac{1-\beta+\sqrt{(1-\beta)^2+4}}{2}.
$$
The conclusions for $c<1$ follow by relaxation. A different consequence, assuming a linear-time reference, is the exclusion of every $c<2-\beta$. With unlimited query time a fixed program can replay the solver from its input; charging the time allowed to each query matters here.

## Transfer of the description cost

Use the public-input nonacceptance simulation for a bounded nondeterministic machine with $m$ public words, budget $R$ and $H=\max(2,R,m)$. The base procedure materializes its bounded-computation formula and runs the reference recognizer in $\widetilde O(R^d+m^d)$ time. Let $F$ denote that genuine formula. In the inductive step, on original nonacceptance, the deterministic target recognizer has a true rejecting run on $F$ whose description cost is $\widetilde O(H^c)$. Source size and formula length differ by at most the factors accounted for in the base construction. All references to the formula inside a replay or evaluator call are implemented by its uniform word generator with access to the original public input. Selecting cuts on the **native target run** makes the description hypothesis apply directly. [Source construction and simulation induction](cumulative-sat-memory.md)

Pick a least-cost time in each full internal window of $w=\lceil H^x\rceil$ instructions. The finite averaging lemma with occupancy $s_t$ bounds the total of $1+s_t$ at the chosen times by $D_{A,Q}/w$. Each selected row also needs $O(\log H)$ bits of timestamps, lengths, and controller data. Consequently the whole directory and its payloads occupy $\widetilde O(1+H^{c-x})$ words, even when each time uses a different decoder program. A nondeterministic verifier guesses this directory and checks its bounds. [Finite selection lemma](../lean/CumulativeSnapshotCuts.lean)

The local defect check chooses one interval. Replaying a target store writes to a fresh local overlay. An incoming read at an untouched address is served by the selected description at the interval's starting time, with that time and the virtual $F$ as parameters. The ending controller is compared directly, and the ending memory is compared at one freely challenged address against the next description. A missing terminal signal is a defect. The first memory is the true all-zero array. Each decoder is clocked and returns a fixed value on timeout or malformed output. Thus each supplied row denotes a total array, including on dishonest guesses. Absence of a defect forces all rows to decode the actual intermediate states by induction. The honest selected rows satisfy every challenge. All query-dependent scratch can be isolated or cleared in time proportional to the capped query computation.

The defect check takes $\widetilde O(H^{x+\beta})$ time since the gap is at most $2w$, each native instruction accesses a bounded number of words, and the formula's length is $\widetilde O(H)$. A rational exponent upper clock and fixed logarithmic factors suffice even if the original $Q$ is not itself constructible. Giving the verifier a larger clock preserves honest witnesses and totality on other guesses. Its public input occupies $\widetilde O(m+H^{c-x})$ words. Apply the previous nondeterministic nonacceptance procedure with work exponent $e$ and public-input exponent $d$ to this test. The new work exponent is the maximum of $e(x+\beta)$ and $d(c-x)$, while the input term remains $\widetilde O(m^d)$. Choose
$$
 x=\frac{dc-e\beta}{e+d},\qquad e'=\frac{de(c+\beta)}{e+d}.
$$
Until the final crossing $1\le e\le d$. In the stated range $c+\beta<2$, $c\ge1>\beta$, so $0<x<c$ and $e'\le d$. Starting at $e_0=d$, reciprocal iteration converges to $1/[d(c+\beta-1)]$ when $c+\beta>1$. Whenever the strict inequality in the theorem holds, a finite stage has $e'<1$. The limiting case $c+\beta=1$ follows by relaxation. The same bounded self-input diagonal with $R=m^K$, $K>d$, then gives a contradiction. All depths and exponent margins are fixed before supplying the source inputs. [Hierarchy argument and clock conventions](cumulative-sat-memory.md)

## Different latencies at different times

There is an unconditional extension that lets every time choose its own query clock. Fix $p>1$ and let
$$
 D_p(F)=\sum_{0\le t<E}\min_{(s,q)}(1+s+q^p)
$$
where the minimum is over the honest descriptions and their integer worst-case latencies $q\ge1$ at that time. The same chosen row contributes both length and latency. With a reference of exponent $d$ as above, $D_p=O(N^c)$ on all unsatisfiable inputs is impossible when
$$
 d(c-1)<1-1/p.
$$
For example, without a separate reference, $p=2$ excludes every exponent $c<(1+\sqrt3)/2$. A solver can trade a shorter description for a longer query time at each instruction. Even after minimizing independently at every time, this sum must exceed the proposed bound on arbitrarily large rejecting runs.

To see this, assume the cost bound, set $w=\lceil H^x\rceil$ and allow a query clock of $Q=\lceil H^{(c-x)/p+\delta}\rceil$ for fixed small $\delta>0$. For any minimizing choices the number of times with $q>Q$ in the **entire run** is at most $\widetilde O(H^{x-p\delta})$. Consequently at least half the times in every full window of length $w$ are eligible. In each window take an eligible time of least $1+s_t$. Its cost is at most $2/w$ times the sum in that window. The whole witness still takes $\widetilde O(1+H^{c-x})$ words. The replay now takes $\widetilde O(H^{x+(c-x)/p+\delta})$ time. Ignoring an arbitrarily small exponent slack for the moment, balancing the replay and public-input terms gives
$$
 c-x=\frac{ce}{d+(1-1/p)e},\qquad e'=\frac{cde}{d+(1-1/p)e}.
$$
Here $0<x<c$ whenever $e\le d$. For $c>1$ the positive iterates starting at $d$ converge to $d(c-1)/(1-1/p)$, by the linear recurrence on their reciprocals. Under the strict hypothesis they cross one at a finite depth and decrease at each prior step. Continuity at this finite set of choices allows a small positive $\delta$ and rational clocks at each stage while preserving the final strict crossing. If $c\le1$, relax it upwards first. The same diagonal applies. This averaging proof loses its strict improvement at $p=1$.

## What fails for the first moment

Consider the tempting replacement of a uniform query clock by a bound on $\sum_t (1+s_t)q_t$. A selection argument depending only on the numbers $s_t,q_t$ cannot guarantee the same replay savings. For integer $W\ge2$ take duration $E=2W+1$, with the initial zero row at unit latency. Give every internal time a unit-length row and declare its latency to be
$$
 q_t=\left\lfloor \frac{W}{E-t}\right\rfloor+1.
$$
The proposed integral costs $O(W\log W)$ by the harmonic sum. A replay with no internal checkpoint costs more than $W$. Every possible last internal checkpoint also gives $(E-t)q_t>W$. Thus no schedule meets this replay cap, even with all the offered rows available. These prescribed latencies are an obstruction to the numerical selection rule. A separate verifier for a list of guessed reads bypasses the obstruction and proves a lower bound even for the additive first moment $\sum_t\min(1+s+q)$. [Segment audit](first-moment-snapshot-audits.md) · [Unconditional exponent](first-moment-heavy-bootstrap.md) An actual RAM changes a bounded number of words per step, so a proof exploiting alternate descriptions of adjacent true states would need an additional lemma.

A linear-time solver has no known subquadratic upper bound on the sum of its shortest descriptions at polylogarithmic query time. Giving a sparse list of the live words at every time permits nearly quadratic cost in a linear run. This is the missing implication for the elapsed-time goal. Literature priority for the unconditional SAT description-cost theorem is unverified.
