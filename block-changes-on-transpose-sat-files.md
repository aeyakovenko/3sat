# Counting changes of memory block on unrestricted word-RAM runs

Which part of the tape argument still says something about the access trace of a genuine RAM? Fix an ordinary deterministic RAM decider for SAT. Use a read-only packed input bank, otherwise zero-initialized random-access work memory, a fixed finite program with constantly many word registers, and word size $\Theta(\log n)$ on $n$ encoded bytes. Allow arbitrary addresses and word operations of the journal's fixed basis, arbitrary workspace within its address universe, and arbitrary running time. Count the ordinary individual input and work probes in execution order. Expand instructions with a bounded number of accesses into fixed microinstructions retaining $O(1)$ temporary words. The program has no external real-time clock.

Partition each bank into aligned blocks of $b$ bytes, rounding to a whole number of native words. Keep the ID of the last probed block **separately for each bank**. Charge one change whenever a probe's block differs from the bank's retained ID, starting with empty IDs. Consecutive probes into one block can visit arbitrary offsets without cost in this measure. The interleaving with probes to the other bank does not clear the retained ID. The measure is defined on the actual execution, with the physical input layout fixed. On each projected bank stream this is the aligned one-block cache cost, including the first access. Afshani, Iacono, Jayapaul, Karsin and Sitchinava identify its shift average with a truncated distance cost. Their definition of $B$-stability also uses an input that is hard at several scales. Our theorem concerns the decision on these fixed files and counts common partners at the stated thresholds. [*Locality*, Definition 2.5 and Lemma 3.1](https://arxiv.org/pdf/1902.07928)

**Claim.** On the [proper transpose 2-CNF family](checking-a-word-transpose-with-two-clauses-per-cell.md), set $b$ to a sufficiently large constant times $\sqrt{n\log n}$, rounded as above. At every sufficiently large byte length, some unsatisfiable inputs and some satisfiable inputs require $\Omega(\sqrt{n\log n})$ block changes. This holds for each correct RAM with unlimited workspace. The all-scales proof below strengthens this to $\Omega((n/b)\log\min\{b/\log n,n/b\})$ at each eligible scale, on common inputs of both verdicts. The number of required changes is sublinear. The canonical files themselves have an $O(n/\log n)$ RAM algorithm, so they cannot yield a superlinear time lower bound on this machine.

## Stopping on a change of block

Use the two contiguous arrays of the [one-work-tape argument](one-work-tape-transpose-check.md). Write $V=\Theta(n)$ for their number of independent bits on a diagonal input $(A,A^{\mathsf T})$, and $H=n/b$. Each of the $\Theta(H)$ whole blocks inside each array contains at least a constant times $b/(tw)$ complete rows of $t$ words of $w=\log_2 t$ bits each. Choosing the constant in $b$ sufficiently large accounts for the byte length of a whole DIMACS row and the two partial rows at the ends. Spacing outside the two data sections gives all large byte lengths. Charge bits of each work block as $O(b)$.

Stop the run either on its verdict or on the $R$th change, where $R=\lfloor\epsilon H\log H\rfloor$. For a precise splitting convention, issue a probe request with its address in a temporary register, update the monitoring IDs and count at that request, and execute the data access as the next microinstruction. On the last charged request the monitor can stop before the access. A run that stops there has already requested $R$ actual changes. Apart from terminal bookkeeping, between successive changes only one input block and one work block can be probed. An initial period with a missing ID has the corresponding bank unused. Unused block labels can be omitted. Input coordinates and all work addresses have $O(\log n)$ bits.

Record the at most $R+1$ boundary configurations of the finite controller, registers, microinstruction state, monitoring IDs and counter, the segment labels, and the final status. Allowing a fixed number of extra endpoints has no effect. The record costs $O((1+R)\log n)$ bits. **Elapsed time is absent.** Source segments from two runs can take different numbers of steps. At each join only the recorded machine and monitor state needs to match. An implementation of a software timer using RAM registers or memory is covered by those same state and memory checks.

## What can pass between two segments

For each used work block draw a path through precisely the segments that use it, in their chronological order. Once the control record is fixed, these paths carry the remaining mutable information. A segment using no work block may be a singleton. Concatenate all paths into one spine, with arbitrary public choices of their order. Assign each segment its input-block label if it has one. At least a constant fraction of the blocks from each array appear at most $k=O(1+R/H)$ times, since the total number of labels is $O(1+R)$. Retain equally many such labels on either side. Unused labels may be represented by isolated dummy segments included in the spine so each has at least one occurrence.

Use Fact 4.2 of Maass, Schnitger, Szemerédi and Turán on that spine, adding empty leaves for a binary tree if required. Cutting at most $2k-1$ tree edges separates selected sets of at least $\Omega(H/9^k)$ labels per side. Cut spine edges by removing an endpoint of each. The disjoint unions of actual work paths are subgraphs of the spine, so no remaining component uses both colors of selected labels. Record the incoming and outgoing work block of each removed real segment, for another $O(bk)$ bits. A removed segment reads at most one input block. Its input can come from the correct side because both of its work-block endpoints are fixed. [MSST, Fact 4.2 and Lemma 3.1](https://igi-web.tugraz.at/PDF/61.pdf#page=8)

Intersect the complete rows from the selected first-array blocks with the complete columns from the selected second-array blocks. The intersection carries $\Omega(n/9^{2k})$ independent diagonal bits. By choosing $\epsilon>0$ sufficiently small this is at least $D=\lfloor a n/H^{1/4}\rfloor$ for some $a>0$. Choose that many positions canonically from the common record. Here $b=\Theta(\sqrt{n\log n})$, hence $H^2\log n=\Theta(n)$. The total record length is

$$
       K=O((1+R)\log n+bk)=O(n\log H/H)=o(D).
$$

Freeze the other $V-D$ payload bits. Two diagonals in the same bucket can exchange their second arrays, retaining a legal path with the very same final verdict or block-change cutoff. Replay each remaining component from the source corresponding to its selected input side, and each separator segment from the source giving its input. The control joins agree by the record. A work block initially contains zeroes. On each subsequent visit it has the outgoing value of its last visit. Consecutive visits on the same component use one source, and a crossing between different sources passes through a removed segment with equal boundary values. This inductively validates the replay on actual words even if within-block computation is arbitrarily long or data-dependent.

There are at most $2^{V-D+K}$ buckets. A bucket containing a diagonal that answered UNSAT before the cutoff must be a singleton because mixing two distinct inputs in it would give an UNSAT decision on a mismatch. Therefore all but a $2^{-\Omega(D)}$ fraction of diagonals reach the cutoff. All but that order of fraction are also in buckets of size at least $2^{D/2}$. Each such diagonal has at least $2^{D/2}-1$ distinct mismatching columns on which the deterministic RAM reaches the same cutoff before answering SAT. This proves the claim. It applies to the actual address sequence for both verdicts, without imposing locality on the machine in advance.

The argument uses the short record obtainable when there are few changes. On unrestricted input access a single RAM instruction can request a remote word. The proof gives no way to charge the byte distance traveled to that instruction. Classical external-memory transpose bounds study production of a transposed array with different rules for block transfers and fast memory. Priority for this change-count statement about the SAT decision files is unestablished. [Farhadi, Hajiaghayi, Larsen and Shi, discussion of external-memory transposition](https://cs.au.dk/~larsen/papers/networkcoding.pdf)


## All block sizes on the original transpose

There is a stronger bound on **the same files**, with no permutation search. Let $d=b/\log n$, $s=n/b$, and $H=\min\{d,s\}$. At every aligned whole-word block size with $H$ above a sufficiently large constant, each verdict has inputs requiring

$$
                  \Omega\bigl((n/b)\log H\bigr)
$$

block changes. For $b=\Theta(\log^2 n)$ this is $\Omega(n\log\log n/\log^2 n)$. At small scales a Cartesian product of chosen block labels can miss every matched pair. We instead count individual slots whose two input records can come from different executions.

There are $m=t^2=\Theta(n/\log n)$ slots, each carrying $w=\log_2 t=\Theta(\log n)$ payload bits. Discard slots whose first or second occurrence straddles a block boundary. This discards $O(s+1)$ slots since physical slots are disjoint. Each input block has $O(d)$ complete slots and intersects $O(1+b/(tw))$ physical rows. Thus a given first and second block have at most

$$
             P=O((1+b/(tw))^2)=O(1+d/s)
$$

matching complete slots. Indeed each shared slot is identified by one row of the first array and one row of the second. The identity $d/P=\Omega(H)$ is what allows one proof to cover both small and large blocks.

Use the earlier cutoff with $R=\lfloor\epsilon s\log H\rfloor$. In its segment record discard all payload slots incident with input labels visited more than $k=\lceil C(1+R/s)\rceil$ times. At most $O(R/k)$ labels have this many visits. For a sufficiently large absolute $C$ their blocks cover at most $m/4$ slots. Concatenate the chains of visits to work blocks as before, in a fixed order, including work-free singletons. Partition this spine into intervals of $L=\lceil\sqrt H\rceil$ consecutive segments and freeze the outgoing work block on each **real** chain edge crossing an interval boundary. An artificial edge between two different chains carries no work data. This costs $O(b(1+R/L))$ bits. A separator theorem is unnecessary for this version.

A remaining slot is unsuitable if visits to a block containing its first record and visits to a block containing its second record both occur in the same interval. There are $O((R+1)L)$ pairs of segment positions in common intervals, and each first/second label pair corresponds to at most $P$ slots. Consequently this test discards at most

$$
         O((R+1)LP)=O\bigl(m(1+\log H)/\sqrt H\bigr).
$$

This uses $d/P=\Omega(H)$ and $m=\Theta(sd)$. Incomplete final intervals also have at most $L$ partners per position. At least a constant fraction of all slots survive for large enough $H$.

Color the intervals independently red or blue. For each surviving slot the intervals visiting its first and second blocks are disjoint, at most $k$ of each. The probability all its first visits are red and all its second visits blue is at least $2^{-2k}$, including when a label was never visited. Some coloring therefore separates $\Omega(m2^{-2k})$ slot pairs. Choose such a coloring canonically from the record. Fix a sufficiently small $\epsilon$. These pairs hold at least $D=\lfloor a n/H^{1/6}\rfloor$ independent bits for a fixed $a>0$. In contrast the number of bits frozen outside the payload by the two records is

$$
 K=O((1+R)\log n+b(1+R/L))
   =O\bigl(n(1+\log H)/\sqrt H\bigr).
$$

Thus $K<D/4$ when $H$ exceeds a sufficiently large constant, and $K=o(D)$ as $H\to\infty$. Freeze the other $V-D$ payload bits. Use the first path in all red intervals and the second path in all blue intervals. Every changed physical input occurrence sees the appropriate source. Every change of source along a real work chain has a frozen boundary. The earlier splice and counting argument applies on these very files, yielding exponentially many slow inputs for the stated address measure.

## The same satisfiable inputs at every dyadic scale

Use nested aligned blocks of $2^j$ consecutive native words, retaining the scales with $H_j$ above the constant just chosen. Write $R_j=\lfloor\epsilon(n/b_j)\log H_j\rfloor$. **One and the same RAM run** can be forced to reach $\Omega(R_j)$ block changes at all those scales. This holds on almost every diagonal, and each of almost all rows has exponentially many distinct satisfiable partners with that simultaneous property.

For the diagonals, take a union bound over the single-scale exceptional sets. With $D_* = \min_j\lfloor a n/H_j^{1/6}\rfloor$ their total fraction is $2^{-\Omega(D_*)}$, since $H_j=O(\sqrt{n/\log n})$ and there are only $O(\log n)$ scales. In particular $D_*=\Omega(n^{11/12})$. Lower bounds on separate lists of satisfiable partners cannot simply be intersected. The following extra record aligns them.

On each remaining diagonal stop at the first probe request by which **all** thresholds have been reached. Choose, breaking ties deterministically, one last threshold $R_j$ completed by that request. Up through it there are exactly $R_j$ changes at this scale. Partition this real prefix into segments of that scale. For the last counted probe, use its request/update of the retained ID as the endpoint, before its data reply. For all scales assign the change to the request microinstruction, even when the corresponding load or store is in the next segment. Add the two **last requested word addresses** at each segment boundary, including a sentinel for an untouched bank. This uniquely determines the previous block IDs used by every scale for the first request in the next segment. The additional addresses cost $O(\log n)$ bits and are analyst's observations. The simulated RAM has no extra registers for these observations or for the thresholds.

In a given segment, let $u_i$ count changes at scale $i$ when processing the requests in it, starting with its recorded incoming last addresses. A coarse change implies a fine change on the very same pair of addresses. Hence $(u_i)_i$ is nonincreasing with coarsening. Round each $u_i$ down to zero or a power of two after capping at $n$. The resulting list of exponents, with a separate zero symbol, has $O(\log n)$ ordered entries taking $O(\log n)$ possible ordered values. By monotonicity the **entire list** costs $O(\log n)$ bits because the number of nonincreasing lists of length $q$ on $m'$ ordered values is $\binom{q+m'-1}{q}\le 2^{q+m'}$. This leaves the full cost per recorded segment $O(\log n)$ as before. No elapsed-time bound is needed, even if a single segment makes arbitrarily many fine-scale requests.

Two paths in the enriched bucket still splice. Within each copied segment, requests and their incoming last addresses agree with those of its source, so it realizes at least the common rounded lower count for **each** scale. Their sum at scale $i$ is at least $R_i/2$. A segment exceeding the cap $n$ contributes at least $n/2\ge R_i/2$ by itself. When all segments are below the cap, rounding loses at most a factor of two in each. All source diagonals were stopped before a SAT answer. The resulting mixed path is an actual prefix of the uncapped RAM on the satisfiable mixed file, and has made all these changes before its answer. No multi-counter stopping rule is imposed on the mixed path.

The chosen stopping scale can vary among diagonals. Grouping by it costs $O(\log\log n)$ bits. At that scale there are at most $2^{V-D_j+K_j}$ buckets with the enriched record, with $K_j\le D_j/4$ by increasing the lower cutoff on $H_j$ for this fixed program. Summing over scales gives at most $2^{V-\Omega(D_*)}$ buckets. All but a $2^{-\Omega(D_*)}$ fraction of rows therefore have $2^{\Omega(D_*)}$ distinct late satisfiable partners **at all these scales simultaneously**. This is a statement about actual address sequences on unlimited-workspace RAMs. The packed RAM algorithm for these layouts bounds how large their unrestricted running-time lower bound could be.

## Extending the code exhaustion from $C$ to $C+1$

Fix the instruction set, the number of physical word registers, the maximum elementary probes per instruction, and the constant in the logarithmic word width. Count stored program text in bits, using a fixed encoding. Permit programs of up to $n$ bits for this argument. The program counter and all registers still occupy $O(\log n)$ bits per boundary, with a **uniform** constant. The code itself is fixed on the two paths in any splice. Thus the single-program upper bound on the fraction of diagonals with too few changes at *some* eligible dyadic scale is $2^{-c n^{11/12}}$ for a uniform $c>0$ at large $n$. A program need only give correct verdicts on the finite family at that length.

There are fewer than $2^{C+1}$ candidate texts of length at most $C$. Hence for every $C\le\min\{n,c n^{11/12}/2\}$ almost every diagonal is hard, simultaneously at all the specified scales, for **every** correct candidate text. The union bound here concerns the unsatisfiable diagonals. Its conclusion about different programs does not require a common satisfiable partner. For this step the explicit criteria are code size and the number of executed address changes. The program can spend arbitrarily many instructions within a block. Once $C$ exceeds a fixed constant, the class includes genuine solvers for ordinary SAT, for example a fixed program enumerating assignments to the occurring names.

There is an effective successor operation. Start from **any** old diagonal, including one obtained by exhausting programs at budget $C$, and let $v$ be its number of payload bits. Choose a larger canonical matrix, retain the old $t\times t$ cells in its upper left corner, and fix the corresponding low-order word bits to their old values. Its second array is the transpose of the enlarged first. With $V'$ total payload bits there are exactly $2^{V'-v}$ completions. Across all programs of length at most $C+1$ there are fewer than $2^{V'+C+2-c(n')^{11/12}}$ bad diagonals at new encoded length $n'$. As soon as

$$
                   v+C+2 < c(n')^{11/12},
$$

at least one completion preserves the old bits and forces the block-change bounds against every correct program at the new budget. All files are explicit proper 2-CNFs. A literal finite search can produce a completion. At fixed length the address space, registers and states are finite. For each candidate text and each promise input test its verdict by simulation until halt or a repeated configuration, and retain the programs correct on that promise. Then enumerate the completions and test the dyadic thresholds. The required search can be arbitrarily expensive. The counting proof permits increasing the dimension until the first success. It establishes neither an increment of one encoded bit per extension nor a superlinear number of executed RAM instructions. Indeed the packed solver still decides every promised file in $O(n/\log n)$ time.

[Lean verification of replay across work-block visits](BlockEpochSplice.lean) covers the local splicing implication, the unary-difference encoding of a monotone list of levels, and the factor-two accounting for capped counts. The selection of slots, physical layout, record counts and asymptotic machine implications are manuscript proofs. The [finite layout experiment](permuted_clause_block_audit.py) tests how selected byte blocks share matched slots on small proper formulas, including the splice of two UNSAT source files into a satisfiable file with four mismatching slots. It exhausts all 4,096 four-request traces on the test alphabet across 32,768 segment partitions, checking charges at three nested scales.
