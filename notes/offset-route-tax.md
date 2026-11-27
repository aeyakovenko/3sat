# One unknown offset can use the full packet-routing overhead

Consider a fixed bounded-fanout routing graph used to certify a native RAM trace. It routes entire access records to designated output ports in increasing address and then time order. Paths occupied by different packets are vertex-disjoint, or have constant congestion. One can let a public selector choose among $K$ different graphs before routing. Even when a single word determines **all** the varying memory addresses, the number of bits of that word available for choosing the graph determines the worst full-packet cost. The RAM computation below also has a linear word-time direct checker. Its time complexity is distinct from the cost of this one compilation method.

## The workload and its actual reads

Put $q=2^\ell$, choose an offset $0\le u<q$, and take arrays $A$ and $B$ of $q$ arbitrary payload words each. The work bank starts blank. A first scan writes $A_i$ at $u+i$ for $0\le i<q$. The second scan writes $B_j$ in increasing order in the complement of this interval within $[0,2q)$. Its address is $j$ when $j<u$, and $q+j$ otherwise. A final scan reads the work bank at every address in order, comparing the reply with a public target word. The machine accepts if all comparisons pass. For fixed $u$ every one of the $2q$ writes supplies a later checked read, and every payload is arbitrary on accepting instances. A constant-register word RAM can do this in $O(q)$ steps.

Among the designated work-bank records in address/time order, the write from left input $i$ always occupies position $2(u+i)$. The subsequent record is the read from the same address. Immutable input accesses may be wired directly, or placed in a separate part of the chart with a fixed number of slots. Consequently the left input $i$ has $q$ possible output ports as $u$ varies. Only $q$ distinct permutations occur altogether. Lean verifies the destination formulas and the binary terminal-prefix capacity bound. [Finite routing checks](../lean/OffsetPacketRoutes.lean)

## A bound on the number of inexpensive offsets

Fix a graph with maximum fanout $\Delta\ge 2$ and distinct terminal output ports. At each vertex assign different digits to the outgoing edges. For a fixed source, the digit strings of paths to distinct terminal ports form a prefix-free code. This is true for any choice of one path per destination even if many nondeterministic routes reach that destination. For each valid offset choose any successful graph and routing. Write $h(u)\in[K]$ for the chosen graph, $l_{i,u}$ for the length of its path from source $i$ and $D_u=\sum_{i<q}l_{i,u}$. For every source and every chosen graph, Kraft's inequality gives
$$
 \sum_{u:h(u)=h}\Delta^{-l_{i,u}}\le 1 .
$$
For a finite family this follows by padding each code to the largest path length in all possible ways. The padding sets for different terminals are disjoint. Taking the arithmetic mean over the sources bounds their geometric mean, so
$$
 \sum_{u<q}\Delta^{-D_u/q}
 \le {1\over q}\sum_{i<q}\sum_{u<q}\Delta^{-l_{i,u}}
 \le K .
$$
In particular at most $K\Delta^r$ offsets can have $D_u\le qr$. This applies if a different successful witness chooses its own preferred graph or paths. Choose minimum total length separately for each offset to measure its cheapest realization. For $K=1$ all but at most $q^\gamma$ offsets cost more than $\gamma q\log_\Delta q$ traversals, for any fixed $0<\gamma<1$. Jensen's inequality, or the arithmetic/geometric mean inequality on the $q$ terms on the left, gives $\mathbb E_u D_u\ge q\log_\Delta(q/K)$.

In a vertex-disjoint packet network these traversals occupy that many nonterminal vertices on the chosen instance. A constant capacity per vertex changes the bound only by its factor. For $b$ exposed selector bits, $K\le 2^b$. For constant fanout some successful offset therefore costs $\Omega(q(\ell-b))$ packet slots when $b\le\ell$. Terminal or source slots add $\Omega(q)$ even if $b=\ell$. These statements charge paths that are actually occupied. Adding unused graph capacity, offering many existential switch settings, and observing correlations among all the addresses leave the prefix argument valid.

## Matching packet cost and the explicit SAT representation

Expose the top $b$ bits of $u$. Route the $q$ left packets, initially in slots $0,\ldots,q-1$ of a $2q$-slot bank, to slots $u+i$. The shift by the exposed multiple of $2^{\ell-b}$ is a fixed wire permutation. A barrel shifter on $2q$ slots implements the remaining $\ell-b$ conditional offsets with $O(q(\ell-b))$ packet slots. It may use cyclic shifts, since the occupied portion never wraps after the full shift. A switch at $j$ places $B_j$ in $j$ or $q+j$. Merge the unique occupied lane for each output address with its designated read port. Equivalently use complementary selectors and local multiplexers. Each layer consists of a fixed number of bounded-fanout choices per lane. This uses $O(q(1+\ell-b))$ packet slots and yields the exact output on every allowed offset.

In an ordinary packet tableau that gives each occupied slot its own $\Theta(\log q)$ Boolean payload variables and mentions them in fixed-width 3-CNF literal fields of $\Theta(\log q)$ bits, this gives a tight worst-case
$$
 \Theta\big(q(\log q)^2(1+\ell-b)\big)
$$
bit bound for this representation. The lower bound applies to full-slot encodings, including all the designated payload fields. The upper bound checks the shared shift bit at each gate and can compute $j<u$ with $O(\log q)$ Boolean gates per $j$. The workload uses only additions, comparisons and fixed simple control. Each remaining operation has an $O(\log q)$ gate implementation. All sizes permit constant-factor power-of-two padding for local clause access. With $b=\ell$ the explicit equality checks link each public word to the right target word. A generator can read $u$ once, after which determining those links costs $O(1)$ word operations per request. With a physically unknown value computed inside a trace, using it as an external selector would require an independent way to obtain it.

This explains why a low-entropy distribution of memory layouts alone cannot remove the third logarithm of the standard packet compiler. A single cyclic shift is already a classical difficult example for routing graphs, and optimal bounds for full merging networks are known. The application here quantifies the inexpensive offsets for a list of selectable topologies and embeds the shift in an ordinary RAM trace with every transferred value checked. General nondeterministic Boolean circuits may certify the same relation by other means. In particular the short-arithmetization literature explicitly asks about permutation CSPs beyond path routing. The unrestricted compiler and the unrestricted SAT time lower bounds remain open. [Yuan Li, chapter on conservative circuits and cyclic shifts](https://knowledge.uchicago.edu/record/906/files/Li_uchicago_0330D_13897.pdf) · [Miltersen, Paterson and Tarui on merging networks](https://wrap.warwick.ac.uk/id/eprint/60905/) · [Shorter Arithmetization of Nondeterministic Computations, appendix A](https://zeyuan.allen-zhu.com/paper/2015-arithmetization.pdf) · [Existing packed compiler](packed-band-transfer.md)
