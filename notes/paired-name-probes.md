# How many raw name bits expose a paired computation?

**Research journal, 24 November 2026.** There is a plain universal decoder with two names per simulated input on which a depth-$t$ adaptive selector separates at most $\min(1,t/B)$ of the pairs at each length. For each depth, parity of a fixed set of data bits attains the bound. This distinction matters for the [program-fiber parity test](parity-of-program-fibers.md), since its selected output can cancel even when the underlying program has a unique result.

## Two names with identical timed behavior

Start with an efficient length-aware plain universal interpreter $V$. For a new name of length $m\ge1$, let $B=2^s$ be the largest power of two satisfying $2B-1\le m$. The first $B-1$ bits are controls $c_a$, indexed by the nonzero vectors $a\in\mathbb F_2^s$. The next $B$ bits are data indexed by all the vectors, including zero. Any remaining bits form a suffix. Form

$$
j(c)=\bigoplus_{a\ne0}c_a a .
$$

Delete the data bit at $j(c)$ and run $V$ on the resulting $m-1$ bits. Leave the empty new name undefined. Every old name has exactly two preimages, obtained by inserting either bit at the indicated position. The new interpreter skips that position without branching on its contents. Both names therefore have identical decoding time, simulated input, output and halting time. Computing the address and copying the remaining bits takes $\mathrm{poly}(m)$ time before an ordinary simulation. The pair survives or misses any specified time window together, including a delayed start. No identification between the old and new physical deadlines is needed.

The compiler first forms the old name, then inserts one bit. This gives additive one-bit length overhead for simulating $V$. The wrapper cannot implement all native functions by literal fixed headers followed by untouched payloads. For any fixed prefix $h$, sufficiently long names have at least $|h|$ controls, so every pair beginning with $h$ has two different payloads and identical behavior. A native routine printing its payload distinguishes them. In contrast, on a strict literal-header interpreter a selector can recognize an exact branch at a prescribed length by testing the padding, length marker and header. When the padding and header are fixed, this takes constantly many probes. [Literal-name framing and timed branch identity in Lean](../lean/LiteralBranchParity.lean)

## The exact adaptive bound

At a leaf of a deterministic raw-bit decision tree on a uniformly chosen length-$m$ name, the unread controls remain independent fair bits. The leaf fixes individual control, data and suffix bits, regardless of the order in which the tree chose them. After probing $c$ distinct controls, the hash is uniform on an affine coset of the span of the unseen columns. Its size $M$ is at least $B-c$, since that span contains zero and each of the $B-1-c$ distinct unseen columns.

The mate follows the same transcript until the tree queries the deleted bit. If the leaf used $t\le B$ probes including $c$ controls, at most $t-c$ data addresses were queried. Its conditional chance of a split is at most

$$
\frac{t-c}{M}\le\frac{t-c}{B-c}\le\frac{t}{B}.
$$

Uniform names induce uniform unordered pairs. Parity of any $\min(t,B)$ fixed data positions gives different outputs exactly when the hidden position is in that set, attaining the stated optimum at every depth. For a tree using $Q$ probes on its actual path, the same calculation at each leaf gives $\Pr[\mathrm{split}]\le\mathbb E[\min(1,Q/B)]$. This also holds for a randomized selector using the same random tape on both names, by conditioning on that tape. [Hash multiset symmetry, support size and leaf inequality in Lean](../lean/PairedProbeBudget.lean)

## Weighted sums and the output clock

For a $q$-bit output, let a selector return weights in any field of characteristic two. A pair with equal weights contributes zero to its output-cell sum. One may also multiply both weights by an arbitrary common coefficient depending on the decoded name or its timed computation. If $Q_{q,m}$ is the number of selector probes on a uniform name of length $m$, the number of nonzero output cells from all eligible lengths satisfies

$$
\#\{\text{nonzero cells}\}\ \le\
\sum_{m=1}^{q-2}2^{m-1}\,\mathbb E\!\left[\min(1,Q_{q,m}/B_m)\right].
$$

For randomized selectors the same right side bounds the expected support size, with the expectation also averaging the tape. The bound counts all split pairs irrespective of timing, so it applies for every deterministic cutoff and every start time common to mates. Since $B_m>(m+1)/4$, an average of $o(q)$ raw probes over all eligible names gives $o(2^q)$ nonzero cells. Indeed lengths $m\le q/2$ account for $O(2^{q/2})$ pairs, and on longer lengths $1/B_m<8/q$. The zero matrix is then a rank-zero approximation on all but $o(2^q)$ cells for each deterministic selector satisfying that average.

A single parity query to the entire encoded name splits every pair, because the mates differ in exactly one position. If $V$ has a literal branch, multiplying this parity by that branch’s length and prefix test selects exactly one representative of each targeted pair once the controls contain that header. This recovers the selected branch's image parity at the wrapper's actual cutoff. The raw-probe lower bound concerns the selector on this modified decoder. It gives no SAT running-time lower bound.

The exhaustive experiment checks all 1,023 decoded pairs through name length ten. For $B=4$ it optimizes over adaptive trees on seven bits, visiting 5,104 partial-assignment/depth states. From zero to seven probes the maximum numbers of separated pairs out of 64 are $0,16,32,48,64,64,64,64$. [Reproduce the finite check with Python](../audits/paired_name_probes_experiment.py)
