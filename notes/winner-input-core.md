# How many input pins can one losing priority claim require?

There is a deterministic $O(M)$-step RAM computing the actual priority winner on every canonical scale whose losing claims each require at least $M/2$ distinct public-input clauses in any unsatisfiable subset. This holds even if the tableau includes global implications across arbitrarily many clock rows, as long as the remaining encoding still admits all correct computations on free public inputs. The canonical inputs, winners, and pairwise exclusivity are identical to those of the original computation. The program's behavior on noncanonical inputs supplies the obstruction. An inert-input implementation of the original program has no such input sensitivity. [Original priority computation](priority-pinned-sat.md) · [Fixed losing columns and core criterion](disjoint-winner-certificates.md)

## A native computation and its physical pins

Let $M=2^j$, let $a_j$ be the active prefix size, and use $b=\lceil\log_2(a_j+1)\rceil$ bits for the rank or the distinguished no-winner code $a_j$. Set $Q=2^b$. For all large $j$, $Q$ divides $M$. The new program computes the true rank $r$ by running the ordinary scheduler with its prescribed virtual all-zero input. It then scans its own $M$ public bits $X_0,\ldots,X_{M-1}$. For each bit equal to one it XORs $i\bmod Q$ into the rank accumulator. Each iteration takes $O(1)$ operations on $O(j)$-bit words, including the packed input read and bit selection. The program returns the accumulator. The selector for an eligible $e<a_j$ tests equality to $e$; unused output codes select no eligible rank. On the actual all-zero input, the output is $r$ at every scale.

Use one distinct unit occurrence $\neg X_i$ per public bit, with a repeated literal if the physical encoding requires three slots. Every other clause, including a requested selector $o_e$, belongs to the unpinned computation or its claimed output. Require that for *each* public input $X$ and eligible target $e$, there is an auxiliary extension of this latter system exactly when the run selects $e$. The standard RAM compiler separates input initialization from transition and routing checks this way. Uniform clauses adding consequences, compressed checks or extension variables are allowed if this projection property is retained. A unique extension for each honest $X$ would give the same bound. The result needs only existence. [Packed encoding](packed-band-transfer.md) · [Jahanjou, Miles and Viola on local reductions](https://arxiv.org/abs/1311.3171)

## Exact characterization of the selected pins

Fix a losing $e$ and write $d=r\mathbin{\mathrm{xor}}e\ne0$. For a set $S$ of retained zero pins, let $W$ be the binary span of the labels $i\bmod Q$ for $i\notin S$, viewing labels as $b$-bit vectors. With all unpinned computation and selector clauses kept, the system is satisfiable exactly when $d\in W$. Each selection of the free bits gives one sum of the available labels and has a genuine accepting extension precisely for target sum $d$. If reachable, that target has exactly $2^{M-|S|-\dim W}$ admissible public inputs by rank-nullity. This count concerns inputs; routing witnesses may have additional multiplicity.

If $d\notin W$, there exists a binary linear functional $y$ with $y\cdot d=1$ vanishing on $W$: extend a basis of $W$ by $d$, complete it to a basis, and prescribe the functional there. Conversely such a $y$ excludes $d$. Thus $S$ makes the claim impossible exactly when it includes **all** the pins in some set
$$
B_y=\{i<M : y\cdot (i\bmod Q)=1\},\qquad y\cdot d=1.
$$
Every such $y$ has $|B_y|=M/2$, since each successive period contains every $b$-bit vector once. The minimum possible number of input pins, allowing all other clauses for free, is therefore exactly $M/2$. Any unsatisfiable clause subset must contain an entire $B_y$, because adding back all its missing nonpin clauses preserves unsatisfiability. In particular, after fixing fewer than $M/2$ input bits to zero, the available labels span the full space. All $Q$ accumulator values have the same positive number of public completions. At the canonical fully pinned input the rank is completely determined.

This argument concerns the public-input certificate complexity of the output projection. The supports are those of a repeated binary simplex code with a zero column in each period; the half-weight property was proved above. The basic necessity of hitting every sensitive input modification is classical in decision-tree complexity. [Nisan, *CREW PRAMs and Decision Trees*](https://doi.org/10.1137/0220062)

## Uniform clause sampling

Suppose the full formula has $P$ indexed clause occurrences and we take a uniform sample of $s$ distinct occurrences. There are $Q/2$ functionals with $y\cdot d=1$. For a particular support the probability that the sample includes its $M/2$ named occurrences is $\binom{s}{M/2}/\binom{P}{M/2}$, interpreted as zero for $s<M/2$. Consequently
$$
\Pr[\text{sample is unsatisfiable}]\le
\frac Q2\frac{\binom{s}{M/2}}{\binom{P}{M/2}}
\le \frac Q2(s/P)^{M/2}.
$$
For a sample restricted to the public pins with all nonpin clauses supplied, the union over those $B_y$ is exact and inclusion-exclusion gives the exact probability. The finite audit checks the characterization against exhaustive completions, checks their multiplicities, and compares every sample-size count against inclusion-exclusion. [Finite audit](../audits/winner_input_core_audit.py)

The distinction between a locally indexed tableau and a gap-amplified proof system matters for this test. A transformed system can combine many externally supplied input bits into one new constraint. Giving that single occurrence for free changes the pin interface used in the theorem. Dinur's amplification changes the constraint system; local access to the original constraints by itself gives no such guarantee. This example excludes a representation-independent small-core argument based on the canonical winner, mutual exclusion, or uniqueness. Bounds on the unmodified tableau must use its particular clauses. [Dinur, *The PCP theorem by gap amplification*](https://eccc.weizmann.ac.il/report/2005/046/revision/1/download/)
