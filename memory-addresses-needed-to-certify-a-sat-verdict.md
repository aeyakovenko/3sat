# How many work addresses suffice to certify a SAT rejection?

Fix a deterministic, correct SAT solver $M$, an unsatisfiable formula $F$ and an upper clock $T$ for its run. Consider all **accepting candidate runs** up to $T$ that follow its actual program from its true initial controller and read the actual input. They may give arbitrary word replies to work loads. For candidate $r$, let $D(r)$ be the set of addresses at which some reply disagrees with the latest preceding store **on that candidate's own trajectory**, with default zero. Define
$$
 \tau_M(F,T)=\min\{|S|:\ S\cap D(r)\ne\varnothing
              \text{ for every accepting candidate }r\}.
$$
It is zero if there are no accepting candidates. Otherwise every candidate on this unsatisfiable file has some conflict. The address universe is polynomial in the encoded bit length $N$. This minimum allows a different optimal set on every input and places no cost on finding it.

For every fixed integer $a\ge0$, if $M$ runs in $O(N\log^a N)$ time, the ratio
$$
  \frac{\tau_M(F,T)}{N/\log^{4a+14}N}
$$
is unbounded on arbitrarily long **unsatisfiable** files, for a fixed valid upper clock $T=\lceil C N\log^a(N+2)\rceil$. This holds on the unrestricted logarithmic-word RAM, for both the fixed-width binary encoding and ordinary decimal DIMACS. Thus, if SAT takes linear time, every proposed collection of $C' N/\log^{14}N$ work addresses, on some unsatisfiable instance, remains consistent with an accepting trajectory of the same program. Different collections may require different trajectories. All control decisions, literal input reads, register calculations and work writes in each trajectory obey the native semantics.

More generally, the simultaneous bounds $T=N^{c+o(1)}$ and $\tau_M(F,T)\le N^{e+o(1)}$ on all unsatisfiable files are excluded if
$$
  c\ge1,\quad 0\le e\le c,\qquad
  c^2(c+e)<c+1 .
$$
The guest's public cutoff $T(N)$ in this statement must be computable in polylogarithmic time and include the real solver's halt on every file. Explicit rational-power and fixed-log-power clocks have this property with the usual integer rounding. For slower-to-specify cutoffs charge their construction at each challenged interval. The value of $\tau$ can increase with the clock. Any larger host bound used to absorb exponent slack first enforces the specified guest cutoff, making every still-running candidate reject at that cutoff. Subsequent stuttering leaves the same family of accepting candidates. This distinguishes the public deadline from the actual input-specific halting time. No absolute lower bound beyond linear time follows. [Companion theorem for genuine nonzero replies](fast-sat-must-retrieve-nonzero-work-words.md) · [Classical SAT tradeoffs](https://lance.fortnow.com/papers/files/tst.pdf)

There is a separate satisfiable-file bound. Interchange accepting and rejecting candidates in the definition and write $\tau_M^+(F,T)$ for the least number of addresses that preclude every explicit false rejection on a satisfiable input. If $M$ takes $O(N\log^a N)$ time, $\tau_M^+(F,T)/(N/\log^{6a+20}N)$ is unbounded on satisfiable files. The corresponding power-exponent exclusion is $c^3(c+e)<c+1$. The two polarities use different hierarchy arguments.

## Exact meaning of the address certificate

Given $S$, keep an exact zero-initialized dictionary for its work addresses. Every store to a member updates its word. On a read from $S$, return its current word. On every other work read independently guess an arbitrary word. A resulting execution can accept within $T$ precisely when there is an accepting candidate $r$ with $S\cap D(r)=\varnothing$. The accepting execution itself gives such a candidate. Conversely, replay the candidate's off-set replies and induct through the instructions. At a retained address its latest store came from the same sequence of instructions and had the same value on both runs. [Lean check of candidate consistency](AddressConsistencyCertificates.lean)

If the real computation accepts, there is an accepting execution for **every** $S$ by choosing each true off-set reply. If the real computation rejects and $\tau\le k$, some $|S|\le k$ rules out every accepting execution. Therefore SAT is equivalent, under that upper bound, to
$$
   \forall S\ (|S|\le k)\quad
   \exists\text{ an accepting $T$-step execution with exact memory on }S .
$$
A false accepting trajectory need not resemble the true computation after its first incorrect reply. The quantified test permits a change of every later instruction, address and candidate store. The hypothesis is required only on real unsatisfiable inputs. For true runs without any certificate assumption, the set of **all** addresses actually loaded before halt suffices on a rejecting input: agreement there forces agreement through every true next step. The sharper slice consequence below can discard many of those reads.

## Eliminating the local nondeterminism

Use the standard local reduction of a time-$H$ bounded nondeterministic word-RAM computation with $m$ public words to a $H^{1+o(1)}$-bit SAT instance. Here $H$ bounds both the source clock and $m$. At the final complementary diagonal take $H=n^3$ on $n$ original input bits. Validate a padded, sorted set of $k$ address words against the guest width. Every selected segment rebuilds its direct address-to-slot bank in $O(k)$ work. Retained payloads, registers, clocks and temporary reduction metadata fit $O(k+\operatorname{polylog}H)$ words per checkpoint. The universal challenge can test invalid endpoints or an incorrect initial/final condition at the incident segment. Rejecting halt states stutter and accepting ones stay accepting. The time width, fixed guest programs and polynomial address bounds are as in the companion simulation. [Packed local encoding and complementary hierarchy](packed-band-transfer.md)

For $p$ segments use these four quantifier blocks in order.

1. Universally choose the proposed set $S$.
2. Existentially guess the list of $p+1$ snapshot rows, with the first initialized and the last accepting.
3. Universally choose a valid segment $j$.
4. Existentially choose the missing work replies **within that segment**, verifying its transition between the selected endpoints in the allotted number of guest steps.

A single run yields the list. Conversely the locally feasible pieces concatenate since the retained words and controllers match at each endpoint. The off-set RAM has **no consistency requirement**, even between consecutive reads in the same segment. Thus no other data are needed when concatenating segments. Only a selected pair of rows is made public to the local nondeterministic search at block 4. Block 3 tests whether some $j$ lacks any successful local completion by complementing the result of a SAT call.

For power exponents, set $k=H^{e+o(1)}$, $p=H^{x+o(1)}$. For a fixed $j$, the last SAT slowdown solves the local search in
$H^{c\max(c-x,e)+o(1)}+m^{c+o(1)}$ time. The next ordinary SAT slowdown eliminates the challenge to the whole list. Its source may have all $pk$ checkpoint words as public input. The resulting time bounds have exponents
$$
 W=\max\{c^2(c-x),\ c^2 e,\ c(x+e)\}
 \quad\text{and the separate input term }m^{c^2+o(1)}.
$$
Choose $x=(c^2-e)/(c+1)$. In the stated strict region $e<1$, so $c^2e$ fits, and $W=c^2(c+e)/(c+1)<1$. The remaining existential computation guesses the checkpoint list itself and has only $m+H^{e+o(1)}$ public words.

Suppose nondeterministic bounded computations already admit a conondeterministic simulation in time $H^{u+o(1)}+m^{c^3+o(1)}$. The ordinary SAT reduction starts at $u=c$. Apply this inductive simulation just to the remaining existential block, merging with the opening universal choice. While $1\le u\le c$ the next exponent is $u'=\max(Wu,e c^3)$. The $m^{c^2u}$ term fits the same public penalty. Also $ec^3<c^2+c-c^4\le1$, since $c^4-c^2-c+1=(c-1)(c^3+c^2-1)$. Some fixed number of iterations gives $u'<1$. Here $c^3<c+1<3$, so on $H=n^3$ the original input penalty is $o(H)$. One obtains a complementary simulation below the diagonal clock. Fixed rational slack absorbs ordinary local-reduction logarithms and rounding. Each recursive source is a fixed bounded verifier. Every actual address used by the resulting opponent is bounded by a fixed polynomial in $n$, and the original universal simulator's arbitrary addresses only enter the SAT construction as data. [Alternation-trading framework](https://people.csail.mit.edu/rrw/automated-lbs.pdf)

## Logarithmic clocks

Write $L=\lceil\log_2(H+2)\rceil$, $A=a+3$, and $B=b-3$ for a putative bound $O(N/\log^b N)$ on the certificate. On the local SAT instance take $k=\Theta(H/L^B)$ slots and root clock $O(HL^A)$. Its guest words have constant-time virtual input access after the stated setup, also in decimal using the public table of $H^{1/8}$ short digit chunks per chosen segment. Its construction costs $o(k)$ here. All bounds use the local word model with division. [ASCII and binary costs](fast-sat-must-retrieve-nonzero-work-words.md)

Put $p=\lceil L^x\rceil$. For one fixed $j$ the local nondeterministic search costs $O(HL^{A-x}+k+\operatorname{poly}(L))$ instructions and is given only $O(m+k+\operatorname{poly}(L))$ public words, including its selected pair. The ordinary materialized SAT call for this search costs
$$
 O(HL^{2A-x} + kL^A + mL^{A-1}+\operatorname{poly}(L)).
$$
The next SAT call searches for a chosen $j$ on which this deterministic subroutine reports failure. Its bounded-program circuit gets the selected rows as input sources. Its other public banks still cost $O((m+k)L^2)$ encoded bits. The deterministic subroutine can copy or process its own selected sources freely, but its only external accesses to the full checkpoint table are the two rows it starts from. Compile those sources using one shared subset-OR selector on the now fixed, outer-guess table. This contributes $O(pkL)$ encoded bits and the same construction-time bound. The $p+1$ rows are physically available to the middle reduction. The inner reduction required neither this table nor a copy of its unselected rows. [Materialized RAM input](materialized-input-census.md) · [Selected adjacent rows](checkpoint-table-selection-for-sat.md)

After the two ordinary eliminations, the clocks have contributions $HL^{3A-x}$ and $HL^{x-B+A-2}$ from the local replay and the full table respectively. Other terms are $O(kL^{2A}+mL^{2A-1}+\operatorname{poly}(L))$, and the original existential list guess costs only $O(pk)$. Take $x=(2A+B+2)/2$ to get the common exponent $W=(4A-B-2)/2$. At $B=4A-1$ the other $k$ term fits. Induct on a conondeterministic simulation bound $O(HL^u + mL^{3A})$ starting at $u=A$. The remaining existential computation has only $O(m+k+\operatorname{poly}(L))$ public words, so replacing it by the current simulation gives
$$
 u'=\max\{u+(4A-B-2)/2,\ 3A-B\}.
$$
For $0\le u\le A$ the public-input term $mL^{2A-1+u}$ is still covered. At $B=4A-1$ we subtract $1/2$ until reaching a negative exponent, since the floor $3A-B=1-A$ is also negative. After fixed depth the original $m=O(n)$ term remains $o(n^3)$ and the resulting shortened diagonal computation is impossible. Substitution gives $b=4a+14$. This proof makes no well-foundedness assumption on paths with synthetic load values. They run only up to the public clock.

The integer logarithmic exponent is convenient. More precisely, for every fixed rational $\delta>0$ the negative-file theorem holds with $b=4a+13+\delta$. It suffices to take $0<\delta\le1$, since larger exponents follow by relaxation. With $B=4A-2+\delta$, the decrement is $W=-\delta/2$ and the floor is $3A-B=2-A-\delta<0$. The same fixed-depth iteration therefore finishes. This calculation does not give the endpoint $\delta=0$.

## Satisfiable files and the nondeterministic time hierarchy

Assume instead that every sufficiently large satisfiable file has a set of $k$ addresses meeting the conflict set of every explicitly **rejecting** candidate of length at most $T$. The true solver still halts within $T$ on all files. For any proposed $S$ on an unsatisfiable file, its true rejecting run is an admissible candidate, so no $S$ passes this test. On a satisfiable file the honest set precludes every explicit rejecting run. A spurious run that reaches the deadline without explicitly rejecting is not an obstruction. For the checked execution semantics in this paragraph, stutter real halts, then treat nonhalt at $T$ as a nonrejection.

The nondeterministic source's acceptance now means that **some** $S$ admits **no** projected rejecting execution. For fixed $S$ the latter statement is
$$
 \forall C \;\exists j\;\forall z\quad
 [\text{the claimed rejecting chart $C$ fails an endpoint test,
 or $z$ fails to join its two endpoints in segment $j$}].
$$
Use the local incident-segment checks for malformed charts. The terminal checks range over the off-set replies $z$ for this selected segment. The same two ordinary SAT eliminations as above, with complemented verdicts, leave a universal chart test of clock $O(HL^W+kL^{2A}+mL^{2A-1}+\operatorname{poly}(L))$, where $W=(4A-B-2)/2$. One more ordinary SAT call decides that test by searching for a bad chart. Its public input contains only $m+O(k+\operatorname{poly}(L))$ words. It guesses the entire chart inside the bounded computation being reduced. The outer existential guess of $S$ remains as ordinary nondeterminism. Counting all costs gives the nondeterministic simulation
$$
 O(HL^{W+A}+kL^{3A}+mL^{3A}+\operatorname{poly}(L)).
$$
At $B=6A-1$ one has $W+A=-1/2$, and the $k$ term fits that same time budget. This proves a uniform simulation of a fixed clocked nondeterministic RAM by another nondeterministic RAM on **the same physical input** in $O(H/L^{1/2}+mL^{3A})$ time. A bounded number of extra private words guessed alongside $S$ is also covered if those words specify a sound certificate test obeying the same checks. In particular $O(k)$ chosen public-to-the-inner-call words are already charged by the $k$ term.

Apply this same-sign simulation repeatedly as a whole, starting from a fixed unary multitape nondeterministic hierarchy language with clock $H_0=n^D$ for some fixed integer $D>1$. The RAM can emulate its original tape heads directly. For any fixed number $J$ of applications, the resulting machine on that same unary string runs in
$$
 O_J(H_0/(\log n)^{J/2}+n(\log n)^{3A}).
$$
Indeed after fixed depth each working upper clock is still of order $H_0$ up to a fixed power of $\log n$, all its logarithms are within fixed factors of $\log n$, and each original $m=O(n)$ penalty remains bounded by the displayed second term with a fixed multiplicative constant. A fixed explicit bound for each previous machine can be supplied as the next public clock. No checkpoint guesses survive into the physical input of the next machine.

Finally, a multitape nondeterministic simulator guesses a chronological log of the resulting RAM's reads and writes, checks its fixed-program word instructions and sorts a copy of the records by address and time to verify every read. On unary input the physical word contents are computable from $n$ and the index, or can be included in an initialization bank. Multiplication and division on $O(\log n)$ bits take at most a fixed polynomial in $\log n$ by elementary arithmetic. A deterministic tape merge sort on a constant number of $O(\log n)$-bit records per step takes another fixed polylogarithmic factor. The exponent of this total overhead depends only on the fixed instruction set and record verification scheme. Enlarging $J$ changes machine constants, including word-width coefficients, without increasing this exponent. Choose $J$ large enough that the final tape computation runs in $O(n^D/\log(n+2))$. Theorem 5 of Seiferas, Fischer and Meyer supplies a unary language in nondeterministic time $O(n^D)$ outside that class: take the identity real-time countable function and observe that $(2n)^D/\log(2n+2)=o(n^D)$. This is a contradiction. Substituting $B=b-3=6A-1$ proves $b=6a+20$ on satisfiable files. [Seiferas, Fischer and Meyer](https://doi.org/10.1145/322047.322061) · [Unary hierarchy and transcript verification](positive-witness-hierarchy.md)

In the polynomial regime the same extra SAT call gives exponent $cW=c^3(c+e)/(c+1)$ with separate input cost $m^{c^3+o(1)}$. If $cW<1$, use $H=n^D$ with $D>c^3+1$ and transfer to tapes directly, since a fixed polynomial saving absorbs the tape logarithms. This gives the positive-file region claimed above. The forward argument for the actual backward slice below works on either verdict, with the applicable bound for that polarity.

Likewise $b=6a+19+\delta$ suffices on satisfiable files for each fixed rational $0<\delta\le1$. At $B=6A-2+\delta$ the one-shot same-sign saving is $W+A=-\delta/2$. The number of repetitions needed to absorb the fixed tape simulation overhead can depend on $\delta$. The argument requires a strictly positive saving.

## A backward slice on the real trace

A useful concrete corollary counts actual loads whose data help determine an observable action. Fix a real rejecting trajectory. In its instruction-level dependence graph, mark the verdict, every control-flow decision (including indirect jumps), and the address operand of every work store. Trace marked register operands back to the defining instruction. At a marked work load mark its address computation and the source value of the last actual store to that address, when one exists. At a marked input load mark its address. For a register operation it suffices to trace any subset of input operands whose actual values force the required output regardless of the other operands. The same rule applies to an address or a control test. The simple version takes every operand. Let $S$ consist of the distinct **actual work-load addresses** in this backward closure.

In every candidate run that gives consistent replies on $S$, the marked values and the true sequence of instruction positions are preserved. Prove this forward along the true execution. Required arithmetic and control conditions follow from their marked predecessors. All earlier store addresses agree. Thus a marked work load has the true last writer or the true absence of a writer, and its required stored value was marked. Its address belongs to $S$, so its reply agrees. A marked input comes from the unchanged original input. The final verdict is consequently rejection. This proves $|S|\ge\tau_M(F,T)$, applying even if the machine performs arbitrarily many other loads. A more selective version can demand only the image of each store address in $S\cup\{\bot\}$, where every outside address maps to $\bot$. For this version propose $S$ and check a closed set of marked operands that fixes each store's image, every needed load address in $S$, all control and the verdict. The forward proof is unchanged. In particular, stores whose destination is known by the opcode to lie in a disjoint bank require no address operands to certify their image. This is a sufficient certificate for the semantic minimum, without identifying all sound slices. Dynamic slicing as a program analysis is classical. [Korel and Laski](https://www.sciencedirect.com/science/article/pii/0020019088900543) · [Agrawal and Horgan](https://doi.org/10.1145/93542.93576)

Ignoring earlier store **destinations** in general would invalidate the corollary. For example, load a work cell $G$ initialized to zero, with $G$ distinct from $0,1$, store one at the numeric address just loaded, then accept if the work word at address one is nonzero. The true run writes at zero and rejects. Choosing only the final load address $S=\{1\}$ still permits an accepting candidate: reply one at $G$, genuinely store one at address one on this trajectory, then read it consistently. Retaining $G$ alone also permits forging the final read at address one. The exact minimum here is two. The on-trace latest writer to address one was absent. The missing dependency is the earlier store's possible alias with that final read. [Finite audit of all supports and accepting traces](address_consistency_certificate_audit.py)

The semantic minimum is insensitive to completely isolated dummy traffic under a precise condition. Suppose an appended phase uses a disjoint work bank, preserves the latched verdict regardless of its work replies, and can be completed honestly within the enlarged clock after every candidate core halt. Keep the core clock fixed, for example with an unconditional timeout guard, so a longer outer clock creates no further core candidates. Every accepting augmented candidate restricts to an accepting core candidate. Every accepting core candidate extends by honest operations in the disjoint phase with exactly the same conflict set. A hitting set for the core therefore works for the extension, and projecting any hitting set for the extension back to the core also works. The two minima are equal. Physical access counts can increase arbitrarily in such a phase. Widening the old core clock or letting the added code influence the reported verdict need not preserve the minimum.

There is an exact limitation to this invariance. Prepend $r$ reads of fresh, never-written sentinel addresses to any solver, accepting immediately if any returns nonzero. On genuine runs they all return zero and change no verdict. On a rejecting input, with the core's original cutoff preserved after the prefix, the new minimum is **exactly** $r+\tau_M(F,T)$. For each sentinel $a_i$, a fabricated one there gives an accepting candidate with singleton conflict set $\{a_i\}$. The honest prefix also extends every core candidate without an added conflict. Checking all sentinels together with an optimal core set suffices. This effect already occurs for a machine whose verdict is constantly rejection. Thus the theorem concerns what forces the verdict under arbitrary unchecked work replies for the specified program. Native program rewrites that preserve the verdict can change this measure by a linear term. A check permitting the known zero initializer at those addresses avoids that artificial cost.

## One file for a finite pool of programs

For any fixed finite list of globally correct solvers all obeying the given time bound, one can choose the negative hard files **common to the whole list**, and likewise the positive hard files with their own exponent. Otherwise on every sufficiently large file of the specified sign at least one solver has a successful short certificate. Guess or universally choose its index together with the address set at the original outer quantifier. Every genuine run of the opposite sign survives its monitor for every index, and an honest certificate for one solver suffices on the target sign. Simulate the indexed finite instruction text at fixed overhead with the original clocks. The elimination proofs are unchanged. This applies to the finite set of correct programs of description length at most $C$ obeying a fixed clock, without an effective procedure for recognizing that set.

There is also an unconditional finite-pool alternative that allows **arbitrarily slow members**. Fix a finite list of globally correct programs, public deadline $T=C_0 N\log^a(N+2)$ and fixed constant $C_1$ in $k=\lceil C_1 N/\log^{4a+14}(N+2)\rceil$. At arbitrarily large lengths there is a file satisfying at least one of the following alternatives.

1. It is satisfiable and every program misses the real deadline.
2. It is unsatisfiable and, for every program and every set of at most $k$ checked addresses, there is a candidate consistent on those addresses which has **not explicitly rejected** by $T$. Such a candidate may accept or time out.

Indeed, if neither alternative occurred beyond some length, every positive file would have a timely genuine accept. Every negative file would have some program and set forcing *every* candidate to reject by $T$, including its genuine run. The finite portfolio, running every member through the clock with disjoint banks, would decide SAT in $O(T)$ and supply all ordinary SAT slowdowns. For the root game universally choose a program and its protected addresses, then ask whether there is a consistent candidate that does not reject by $T$. At a positive input the genuine run of each globally correct program qualifies even if it times out. At a negative input the hypothesized forcing choice rules out every such candidate. This is the four-block computation above, so the same complementary diagonal contradicts the hypothesis. Finitely many exceptional input lengths can be hardwired. The timeout convention is essential here; blocking explicit false accepts in a slow program can be vacuous.

Apply the alternative to the list of all correct programs of any one bounded description length. A proof excluding the second alternative for every such list would yield genuine slow files in the first. The current results allow fast programs to produce the second alternative. Passing from a larger family of misleading candidate runs to a longer genuine run is the outstanding step.
