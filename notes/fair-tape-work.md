# How much branching work must successful fair tapes carry?

**Research journal, 24 November 2026.** For an ordinary sampler, the time at which it reads each fair bit matters to a simultaneous search of all its executions. Bounding the work of this search gives an unconditional coding inequality for a discounted output probability. It also bounds how often a candidate counterexample to the [unary coding test](unary-speed-gap.md) can have inexpensive successful tapes. The result applies to the actual unrestricted reference interpreter.

Fix a one-way fair-bit native sampler $S$, a clock $t=2^q$ with $q\ge1$, and an output $y$ of length at most $q$. Let $E_y$ be the event that $S$ publishes $y$ by $t$, let $\mu=\Pr(E_y)>0$, and write $G=C_t^V(y)+\log_2\mu$ on a fixed efficiently literal universal prefix RAM $V$. Normalize an elementary virtual instruction to read at most one new bit. Count each executed instruction, including the one that publishes. On a tape stopped at publication or at $t$, put
$$
 H=\sum_i 2^{b_i},
$$
where $b_i$ counts the fair bits already read before instruction $i$. The bounds below have constants depending only on the fixed machines. For integers $0\le a\le q$,
$$
 \Pr[H\le t2^a\mid E_y]\ \le\ (q+2)^{O(1)}2^{a-G}. \tag{1}
$$
In particular, on a sequence with $G/\log(q+2)$ unbounded, every fixed near-clock cutoff $t(q+2)^c$ covers an inverse-superpolynomial fraction or less of the successful tapes along a subsequence where the ratio tends to infinity.

## Enumerating the actual computation tree

Set $B=t2^a$. Grow the computation tree one virtual instruction at a time, allowing a step whenever its charge $2^{b_i}$ would keep the accumulated charge at most $B$. A deterministic instruction has one successor and a fresh fair-bit read has two. A node reached after $j$ reads has probability $2^{-j}$, since a unique sequence of $j$ bits reaches this particular node of the unmerged tree. The expected total charge on a fair path through the retained steps is therefore exactly the number of retained instruction nodes. Each path has charge at most $B$, so there are at most $B$ such nodes, plus at most $2B+1$ terminal or rejected children. This identity allows unrestricted, data-dependent memory addresses and control flow. [Lean proof of the finite tree identity](../lean/PrefixTreeWork.lean)

A deterministic native depth-first traversal restores each overwritten simulated word on return from a child. The instruction pointer, registers, input counters, output state and any modified memory cells have a bounded number of changes per virtual native step. An undo stack and a sparse addressed store implement these changes in $\mathrm{poly}(q)$ overhead per visited node. This includes log-time bookkeeping for zero-initialized memory and an output prefix of at most $q$ bits with an overflow flag for longer publications. Both addressing and the stack length use $O(q)$-bit integers, since $a\le q$. A bound of $t$ on the simulated steps per path still applies.

A retained random-bit read at residual depth $j$ costs $2^j\le B$. Every terminal therefore has depth at most $q+a+1$. All recovered output masses have the common denominator $2^{q+a+1}$, and even their total fits in $O(q+1)$ bits after scaling. Accumulate each publication with weight $2^{-d}$ at its exact terminal depth $d$. Sort the positive masses by size, breaking ties lexicographically. If the retained mass of $y$ is $\mu\rho$, its one-based rank is at most $1/(\mu\rho)$. The code for rank minus one needs at most $\lceil-\log_2(\mu\rho)\rceil$ bits, with a zero-length payload allowed for rank one. Self-delimited $q,a$ and the rank length cost $O(\log(q+2))$ since at most $2^{q+1}-1$ short outputs exist. The actual decoding time is $B\,\mathrm{poly}(q+2)$ after literal compilation. This proves (1), including the case $\rho=0$.

Consequently the soft description cost obeys the unconditional bound
$$
 C_t^V(y)\le -\log_2\mathbb E\!\left[{\bf 1}_{E_y}
                  \min(1,t/\max(1,H))\right]+O(\log(q+2)).
 \tag{2}
$$
Indeed split $H$ at thresholds $t2^a$ for $0\le a\le q$. On the first bin its conditional discounted contribution is at most $(q+2)^{O(1)}2^{-G}$ by (1). Each later bin costs at most twice that bound since its discount is at most $2^{1-a}$. The remaining tail contributes at most $2^{-q}$ conditionally. A literal code of length at most $q+O(\log(q+2))$ shows $G\le q+O(\log(q+2))$, absorbing that tail. Multiply the resulting conditional expectation by $\mu$. This proves (2) for one genuine ordinary sampler. It differs from [the existing reciprocal physical-time prior](discounted-program-mass.md) in how it charges instructions taken after random bits have been read. Schmidhuber’s earlier GUESS construction also divides a computation budget on each new input bit. Its cutoff compares total elapsed steps against the current divided deadline. Here each previously executed step keeps the charge from the bit depth at which it occurred, which permits the late-randomness bound below. [Schmidhuber, The Speed Prior](https://people.idsia.ch/~juergen/speedprior/)

## Conditioning on an efficiently produced prefix

Fix a finite string $w$ generated by an exact $V$ program of length $d$ in time $t$. Supply $w$ to $S$ before drawing fresh fair bits. Define $H_w$ by charging only for bits read *after the supplied prefix*. Let $\rho_w$ be the conditional probability, given $E_y$ on the original fair tape, that the tape begins with $w$ and $H_w\le t2^a$. On that prefix the retained mass of $y$ is $2^{|w|}\mu\rho_w$. Decode the exact name for $w$, then search the associated tree for the rank of $y$. The forcing phase also counts each virtual step, with residual depth zero. The same argument gives
$$
 G\le -\log_2\rho_w +d-|w| +a+O(\log(q+2)) \qquad (\rho_w>0). \tag{3}
$$
The headers may precede the self-delimiting prefix-generator name. Its output fits in the available clock up to the native word-output factor; the simulator only needs to serve bits requested by $S$. Taking $w$ empty recovers (1) to constant precision. Equation (3) can make a very thin prefix cylinder relevant when it has a short timely description.

This search also yields a two-sided characterization on $S=V$. At a secondary budget $B=2^{q+a}$ allow the prefix generator and the interpreter up to $B$ steps each, and retain executions of the interpreter with residual charge $H_w\le B$. For a program $p$ generating $w$ by this deadline write $m_{p,a}(y)$ for the retained output probability conditional on that forced prefix. For $0\le a\le 2q$ define
$$
 M_t(y)=\max_{a,p}\ 2^{-a-|p|}m_{p,a}(y).
$$
Take ineligible programs to contribute zero. Then for all sufficiently large $q$ and $|y|\le q$,
$$
 C_t^V(y)=-\log_2 M_t(y)+O(\log(q+2)). \tag{4}
$$
For the upper bound on $C_t$, the generator code, rank in its tree, and secondary time allowance cost $|p|-\log_2m_{p,a}(y)+a+O(\log(q+2))$ using the preceding construction. For the other direction take a program $v$ minimizing $C_t^V(y)$ and set $a$ to its time excess. The short literal guarantee gives $|v|+a\le q+O(\log(q+2))$, hence $a\le 2q$ at all large $q$. A literal printer produces the bits of $v$ in time $\mathrm{poly}(q)$ using $|v|+O(\log(q+2))$ bits. Forcing $w=v$ makes the reference publish $y$ by $B$ without consuming any residual fair bits. Its retained probability is one. This establishes the claimed reverse bound. The maximization includes arbitrary short descriptions of useful tape portions; a maximizing description need not encode the entire original publication name.

## Testing two candidate constructions

A shared expensive deterministic precomputation followed by at most $b$ instructions and $r$ random reads on every path has $H\le t+b2^r$. Thus $r+\log_2(b+1)\le q+O(\log(q+2))$ suffices for the coding bound on every short output, regardless of the distribution generated by the final instructions. This includes order-$q$ fresh bits in a short final computation. A similar conclusion for an individual output follows if a polynomial fraction of its successful tapes has this property.

Conversely, draw $q$ bits immediately, ignore them all, and then wait $\Theta(t)$ deterministic steps before a fixed simple output. After supplying an epoch parameter this costs $\Theta(t)$ physical time and gives $H=\Theta(t2^q)$ on every run. A fixed program prints the same word promptly. This defeats using a large median $H$ as a sufficient condition for a cost gap. What remains is to produce excess *actual deterministic description cost* along with a large raw sampling probability, even when every accessible prefix and work-limited completion search is allowed.

## Merging full RAM configurations

There is a second search that survives the discarded-bits example. At each virtual instruction count, merge histories giving the same live configuration. Keep at most $W=2^a$ live configurations after the merge, ordered by a deterministic approximation to their retained probability, with deterministic ties. Record terminal publications separately. If $\sigma$ is the fraction of successful tapes for $y$ that survive every truncation until publication, then
$$
 \sigma\le (q+2)^{O(1)} W\,2^{-G}. \tag{5}
$$
This statement uses the actual retained probabilities under the truncations performed by the specified deterministic search. Configurations include the control registers, sparse work memory, any exposed input-head position, and output state. A one-way fair source has independent unused suffix bits even when histories with different consumed inputs merge. Output that has already exceeded $q$ bits can be dropped if publication is append-only. A reusable writable output area, if present, is part of the ordinary work memory.

To compare large memories exactly, store each as a persistent binary trie on the $O(q)$-bit address. Give zero subtrees a fixed identifier. Intern each nonzero leaf value and each tuple of tree level and child identifiers in a deterministic balanced dictionary. A node and its children then have the same identifiers in two snapshots precisely when the represented subtrees are equal. An update creates or looks up $O(q)$ nodes. At most $O(tW\,\mathrm{poly}(q))$ nodes and dictionary entries arise, so search, update and comparison take $\mathrm{poly}(q)$ time per virtual instruction. Zero-initialized memory is represented by the empty root. This is exact sharing and requires no probabilistic fingerprint or bound on live workspace beyond the usual time and word-width limits of each execution.

At each layer propagate the retained state's weight to one deterministic successor or equally to two fair successors. Combine weights for equal configuration keys before keeping the $W$ largest approximate weights. Sum the terminal short-output weights in the same way, retaining every observed output key. Store a nonnegative dyadic floating-point lower approximation with $m=3q+16$ significant binary bits, zero represented separately. Division by two shifts the exponent exactly. Every downward-rounded addition retains at least $1-2^{1-m}$ of the unrounded positive sum. One can implement the operation by aligning at most $m+O(1)$ leading bits; for a sufficiently separated smaller exponent the lower-rounded sum is simply the larger floating-point operand. The number of additions along the entire search is at most $4(t+1)(W+1)$ since at most two outgoing edges per retained state are inserted at a time. With $a\le q$ the product of all these rounding factors is at least $1/2$. Induction over the additions shows that **each** computed weight lies between half and all of the true weight of the histories surviving those very same truncations. Truncation only deletes entries. The smallest positive true mass is at least $2^{-t}$ because each contributing path has read at most $t$ bits. Thus the signed exponent needs $O(q+1)$ storage bits even when the represented mass is exponentially smaller than the available precision in a fixed-point representation.

The search takes $tW\,\mathrm{poly}(q+2)$ time. Sorting all recorded outputs by their approximate masses gives $y$ rank at most $2/(\mu\sigma)$ whenever $\sigma>0$, because their sum is at most one. The same prefix-free rank code proves (5). In particular, if all live configurations at each layer number at most $\mathrm{poly}(q)$, the search covers every successful tape with a polynomial width; arbitrarily many fair bits may have been read and merged.

One can estimate its total loss from the unpruned process without knowing $y$. At layer $i$ write $m_i(c)$ for the unconditional mass of live full configuration $c$, and $\delta_i$ for its total mass outside a heaviest $W$-element set. The approximate live weights prior to truncation are bounded above by $m_i(c)$. Their sum on configurations discarded by the search is at most $\delta_i$, since keeping its own heaviest $W$ achieves at least the approximate mass on any other $W$-element set. The factor-two relative guarantee shows that the *actual* retained histories discarded at this layer have total mass at most $2\delta_i$. Charging each run only at its first discarded state gives
$$
 \mu(1-\sigma)\le 2\sum_{i=1}^t\delta_i.
$$
Together with (5), this puts a necessary lower bound on cumulative configuration-mass tails for any substantial high-excess output. Programs can also produce an easy output through enormously many distinct configurations. The converse required for a SAT lower bound remains unknown.
