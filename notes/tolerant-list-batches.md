# One verdict for a batch with many defective lists

Let $N=2^w$. A good block is a list of $N$ distinct $2w$-bit records. Fix a finite field $k$ and a constant $0\le\delta<1$. A tester takes $t$ lists and returns one when every block is good and zero when more than $\delta t$ blocks are defective. In between, its value may be **any element of $k$ depending on all the raw input records**, even on their order. For all sufficiently large $w$ and all $t$ satisfying

$$
t\lceil\log_2(2t)\rceil\le 2^w,
$$

every trivalent bit tensor network implementing such a tester has volume $\Omega_\delta(tNw^{1+\sigma})$, where $\sigma>0$ is the list-distinctness exponent for $k$. In particular the bound holds for every polynomial batch size in $w$. It also holds for bounded-fan-in Boolean circuits, with circuit size counting gates and wires. The external input is the November 24 preprint's volume theorem for the **exact** product of $m$ list-distinctness bits, uniform for $1\le m\le 2^w$. The reduction below preserves that lower bound even when the tester need only recognize a fixed positive fraction of defective blocks. [Preprint, *Volume of list distinctness*](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/obstruction.tex)

## Correcting one test

Write $G(x)$ for the good-block indicator, $P$ for the number of bits per block, and $T$ for the given $t$-input tester. A known good block $x_+$ will supply padding. To test a group of $g\le t$ blocks, feed each to $T$ either $\lfloor t/g\rfloor$ or $\lceil t/g\rceil$ times, filling its $t$ slots. Put $\rho=(1+\delta)/2$ and $e_g=\lfloor\rho g\rfloor$. If the group has $d>e_g$ defects, its good blocks occupy fewer than $(1-\rho)g(2t/g)=(1-\delta)t$ slots. Thus this call returns zero. It returns one when $d=0$.

Multiply this call's answer by

$$
\sum_{\substack{A\subseteq[g]\\|A|\le e_g}}
    (-1)^{|A|}\prod_{i\in A}(1-G(x_i))
 =\sum_{r=0}^{e_g}(-1)^r\binom dr .
$$

The multiplier is one when $d=0$ and zero whenever $1\le d\le e_g$. For larger $d$ the tester already returned zero. The product is exactly $\prod_i G(x_i)$. This uses no assumption about the tester's value on a partially defective input.

One selector flag per group position specifies $A$ uniquely. Discard choices with $|A|>e_g$ and attach a factor $-1$ per marked position. For each marked position make a second independent switch, contributing $1$ on the good padding block and $-1$ on the real block. The sum on that switch represents $1-G(x_i)$. Unmarked positions force the switch to zero. Compact the marked records to the front, carrying their flags, and fill the remaining slots among the first $e_g$ with $x_+$. An exact product on these $e_g$ slots thus supplies the displayed multiplier after contraction. The compactor need not maintain input order because the product is symmetric. It is a deterministic circuit, so its internal wires have one consistent evaluation per choice of flags and switches. When more than $e_g$ flags are marked, the first flag after those slots detects the excess.

One-bit-key compaction on $g$ records of payload length $P$ costs $O(gP)$ bounded-fan-in gates and wires when $P\ge g$. Here $g\le t\le N$ and $P=2wN$. Copying the group to the tester's $t$ input slots costs $O(tP)$ per group. All Boolean checks and switches translate into trivalent tensors over $k$. For $t$ polynomial in $w$, even a bitonic sorting network on flagged whole blocks suffices, since its factor $O(\log^2(2t))$ is $o(w^\sigma)$. [Asharov, Lin and Shi, Theorem 1.2 and footnote 3](https://arxiv.org/pdf/2010.09884)

## Sharing the next exact product

Start with $m=t\lceil\log_2(2t)\rceil$ independent raw blocks. At any level with $u>0$ current slots, partition them into $\lceil u/t\rceil$ nonempty groups of size at most $t$, filling groups in order. Use one copy of $T$ per group. Concatenate the correction slots of every group and pass them to **one** exact product at the next level. Their count is $u'=\sum_g e_g\le \rho u$, independent of every data bit and switch setting. All signed sums for different groups distribute over that next product. The empty product at $u=0$ has value one, so the construction terminates. Induction on $u$ proves exactness for every assignment of all exterior bits.

The total number of tester copies across the levels is $O_\delta(m/t+\log(2m))=O_\delta(m/t)$. Indeed the sum of all lengths $u$ is at most $m/(1-\rho)$ and there are $O_\delta(\log(2m))$ nonempty levels. The overhead including duplication, compaction and exterior wires is $O_\delta(mP)$. If the tester has volume $V$, the resulting exact network therefore has volume

$$
O_\delta\bigl((m/t)V+mP\bigr).
$$

The source lower bound exceeds $mP w^\sigma$ on the selected $m\le 2^w$. This gives the claimed bound on $V$. Running a separate recursion for every group would repeatedly pay for nearly empty testers. Pooling the correction slots before the next level pays for only one final partial group per level.

## SAT and the cost on a RAM

The same argument works for every raw block predicate with a known good input and the stated exact-product bound. In the journal's unit-CNF family a block consists of two lists of units with opposite signs and distinct names within each list. It is good when it is satisfiable. The signed two-list reduction supplies the required exact-product lower bound with $P=\Theta(Nw)$, on this promise alone. Copies and public padding remain legal blocks, including at every recursive level. A circuit that accepts when all $t$ formulas are satisfiable and rejects when more than $\delta t$ are unsatisfiable thus needs the same volume. This includes a circuit acting on their single serialized conjunction after tagging each block's variable names. All tags cost $O(\log(2t))=O(w)$ bits per occurrence. Each unit can also be written as four ordinary three-literal clauses using all signs on two fresh variables, with the same asymptotic bit cost. [Exact unit-SAT product on the two-list promise](matrix-list-unit-sat.md#one-sat-answer-tensor-with-two-ordered-lists-of-literal-positions)

There is a dense-identifier version with the opposite SAT convention. The journal's $O(Nw)$-bit dense 3-CNF is satisfiable exactly when a raw list contains a duplicate. Wiring one such input per block costs $O(mNw)$ for the original exact tests, or $O(tNw)$ at one tolerant tester. Thus the one-bit promise “accept when all are unsatisfiable, reject when more than $\delta t$ are satisfiable” already has the lower bound on these explicit dense 3-CNFs. [Dense 3-CNF construction](matrix-list-unit-sat.md#a-direct-reduction-to-3-sat-with-dense-identifiers)

A logarithmic-word RAM radix-sorts each list or marks its addresses and gives the exact verdict on the raw lists in $O(tN)$ word operations. The promised unit formulas permit the same direct marking algorithm. Even tolerating nearly all blocks being defective leaves the tensor lower bound in force, while this particular family admits a fast exact RAM computation.

The finite audit exhausts 16,380 raw batches with two distinct records of each status, including different tester values for identical vectors of verdict bits. It checks the full recursion, forced padding, signed switches and the grouping of correction slots over the integers. [Executable audit](../audits/tolerant_list_batches_audit.py)
