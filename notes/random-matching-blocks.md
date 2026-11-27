# How far can independent word-sized tiles compress a sparse quadratic?

**Research journal, 24 November 2026.** The grid-expander upper bound exploits a partition into word-sized tiles having only a bounded number of adjacent tiles per tile. Replacing the grid by three random perfect matchings obstructs that approach even when the two vertex partitions can be chosen separately, after the graph is known. This yields a lower bound for independent local encoders and receivers. On a general RAM an ordinary scan of the edges with two indexed endpoint lookups still takes $O(m)$ word operations. [Grid construction](tile-matching-sat.md)

## A sharp count of occupied block pairs

Take $d\ge3$ fixed. Let $G$ be the union of $d$ independent uniform perfect matchings between two copies of $[m]$, dropping repetitions. Put $b=\lceil\log_2 m\rceil$ and $u=\lceil m/b\rceil$. A partition on either side has $u$ blocks of size $b$ except for one possibly shorter block. An ordered source-target block pair is occupied if it contains any edge. With probability tending to one, the *minimum* number of occupied pairs over all such partitions is $(d-2+o(1))m$.

There are at most $u^{2m}$ labeled partition pairs. If $t$ allowed pairs are specified, the permitted incidence table has at most $tb^2$ raw entries. Its number of compatible permutations is at most the product of its row sums, hence at most $(tb^2/m)^m$. Divide by $m!\ge(m/e)^m$ and take $d$ independent powers. Extending a list smaller than $t$ to one of size $t$ gives the failure bound
$$
  u^{2m}{u^2\choose t}\left(\frac{e t b^2}{m^2}\right)^{dm}.
$$
For $t=\lfloor(d-2-\epsilon)m\rfloor$ with fixed $0<\epsilon<d-2$, its log is at most $-\epsilon m\log m+O_d(m\log\log m)$. The same estimate with a sufficiently large $O_d(\log\log m/\log m)$ deficit from $d-2$ suffices.

Conversely for any $d$ permutations identify the two vertex sets by the first one. Order the vertices by concatenating cycles of the second permutation in cyclic order; use the same consecutive blocks on both sides. Identity edges use at most $u$ block pairs. Along each cycle all non-wrapping edges occupy a diagonal or a next-block pair. Every cycle whose wrap edge is not diagonal straddles a distinct boundary in the concatenated order, so there are at most $u-1$ such wrap edges. The first two permutations together occupy at most $3u$ block pairs. Each remaining permutation adds at most $m$. This proves the matching upper bound $(d-2)m+O(m/\log m)$.

## Receivers with local preprocessing and a short output

Let $A$ be the simple incidence matrix. Consider the single-bit verdict $x^\top A y$ over $\mathbb F_2$, with independent source and target pins. Fix any pair of graph-dependent partitions. Source block $I$ may preprocess its own $x_I$ into arbitrary read-only data, with arbitrary word size and length. A receiver for target block $B$ sees all of its own $y_B$. It can adaptively query these source arrays, compute freely and send a message from a fixed alphabet of size at most $2^k$. Each receiver has its own local state and receives no messages from other receivers or the coordinator. The coordinator knows the full $x$, all the messages, and the public graph. Its task is exact on every $(x,y)$. This model includes a local encoding per source tile with one copy routed to each of its destinations and with a parity bit per destination. A shared preprocessing stage jointly reading several source blocks changes the hypothesis.

For each fixed $d$ there is an $\eta_d>0$ such that, with $k\le\eta_d b$, for every fixed $x$, all but $\exp[-\Omega_d(m/b)]$ of uniform $y$ require $\Omega_d(m)$ distinct ordered (receiver, source block) probes. This holds simultaneously as a statement for every pair of partitions of any graph satisfying the preceding occupancy lower bound. The high-probability subset of the $y$'s may depend on the algorithm, the partition and $x$.

Fix a receiver $B$ and let $D_B$ be its number of occupied source neighbors. In each occupied source block choose one source row nonzero on $B$. Among these representatives one can find $r_B\ge D_B/d^2$ linearly independent rows: a basis of $r_B$ rows covers at most $d r_B$ target coordinates, and each target coordinate is incident to at most $d$ different source rows. The basis indices belong to distinct source blocks. Write $r=r_B$.

For a subset $S$ of $s$ of these basis indices, suppose a particular $y_B$ makes the receiver omit all $s$ of their source blocks on the fixed $x$. If the $s$ selected source bits vary arbitrarily, the same queries and message are produced because no returned word depends on those bits. Hold all other target blocks' bits fixed to zero. For each modified $x'$ their receivers' messages may depend on $x'$ but are identical in any comparison of two choices $y_B,y'_B$. If both choices omit $S$ and produce the same message at $x$, correctness for every $x'$ requires
$$
                   A[S,B](y_B-y'_B)=0.
$$
Indeed differences in the two complete parity computations vanish for every modified assignment, including each single-bit flip. Since the chosen rows have rank $s$, a fiber has at most $2^{|B|-s}$ target strings. At most $2^k$ messages are available. Thus the probability of omitting all $s$ blocks is at most $2^{k-s}$ for every fixed $x$.

If at most $q$ representative blocks were touched, this omission condition holds outside some $q$-subset of the $r$ blocks. A union bound gives
$$
   \Pr_{y_B}[\text{at most }q\text{ distinct representative blocks touched}]
         \le {r\choose q}\,2^{k-r+q}.
$$
In particular if $k\le r/4$ and $q=\lfloor r/16\rfloor$, the bound is at most $2^{-\gamma r}$ for an absolute $\gamma>0$, by $H_2(1/16)+1/4+1/16<1$. This argument permits arbitrary branching on $y_B$, on the returned source data and on the addresses of earlier queries.

To sum, for large $m$ the occupancy bound gives $\sum_B D_B\ge(d-2)m/2$. Discard blocks with $D_B<\lambda b$ for $\lambda=(d-2)/8$. They account for at most $\lambda b u\le (d-2)m/4$ pairs. On every retained block $r_B\ge\lambda b/d^2$; choose $\eta_d=\lambda/(4d^2)$. These ranks sum to $\Omega_d(m)$ and each is $O_d(b)$. Given fixed $x$, the counts of touched representative blocks are independent across receivers under independent $y_B$. Their expectations are $\Omega(r_B)$ by the omission estimate. Hoeffding's inequality with squared ranges summing to $O_d(mb)$ proves the claimed tail. Each counted pair represents a distinct actual query by its receiver.

The coordinator may additionally observe an arbitrary $a$-bit sketch $h(y)$ of the complete target vector, independent of $x$ and unavailable to the receivers. Replace $k$ by $k+a$ in the preceding threshold. Fixing all other target blocks to zero, group the strings omitting $S$ by both their receiver message and $h(0,\ldots,y_B,\ldots,0)$. In each group all comparisons persist under every change to the selected source bits. There are at most $2^{k+a}$ groups. The individual probe counts still depend only on $x$ and each receiver's own $y_B$, so the same independence argument gives the same tail. A sketch that observes *both* input vectors can transmit the answer in one bit.

Gate equivalences for one product per edge, an XOR chain and the private unit pins translate this quadratic verdict to $O(dm)$ width-three clauses. This makes the cost meaningful on ordinary formulas while preserving the receiver hypotheses. A receiver allowed to send its entire $b$-bit input can abstain on all probes because the coordinator already knows $x$. A shared processor may also read all signs before computing. Neither phenomenon is addressed by the local restriction. Sparse matrix-vector multiplication and systematic data-structure lower bounds have extensive literature with different preprocessing and cost definitions. Priority of these precise bounds remains unverified. [Bender, Brodal, Fagerberg, Jacob and Vicari](https://doi.org/10.1007/s00224-010-9285-4) · [Natarajan Ramamoorthy and Rashtchian](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2020.35) · [Finite counting checks](../audits/random_matching_blocks_audit.py)
