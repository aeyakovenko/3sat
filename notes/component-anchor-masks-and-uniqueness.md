# How many component-anchor tests distinguish an edgeless graph?

In the signed-graph transfer, each consistent connected component has a free choice of orientation. Pinning one vertex of each component removes that choice. A partial root set $R$ can itself be tested using only evaluations on zero-or-one-model formulas. Over $\mathbb F_2$, guess a full binary coloring, pin every vertex to its guessed bit, impose unsigned equality on the edges, and require the vertices in $R$ to be zero. Each fixed coloring gives a formula with at most one model. The parity of its SAT bit over colorings equals
$$
    M_\lambda(R)=[R\text{ meets every block of }\lambda],
$$
where $\lambda$ is the component partition. Indeed the number of colorings is two raised to the number of components missed by $R$. Every vertex can be named densely. Proper ternary padding uses fixed false variables. Multiplying this contraction by a separate SAT call on the signed graph pinned at $R$ kills the function value of the second circuit on all unanchored graphs, regardless of how it answered those potentially ambiguous files. On anchored graphs the signed formula already has at most one model. [Signed-graph list transfer](matrix-list-parity-graphs.md)

There is an exact limitation on using repeated root tests alone to recover the discrete partition. On all partitions $\lambda$ of $[m]$, allow $k$ copies of $M_\lambda$, on independently specified subsets, followed by an arbitrary joint $\mathbb F_2$-linear functional of their tensor product. Equivalently, for an unrestricted function $W$ independent of the graph, the answer is
$$
  \sum_{R_1,\ldots,R_k} W(R_1,\ldots,R_k)\prod_{j=1}^k M_\lambda(R_j).
$$
The minimum $k$ giving $[\lambda\text{ is discrete}]$ is $\lceil\log_2 m\rceil$ for $m\ge1$.

To see this, use $u_v=1+[v\in R]$ at every vertex. The unique multilinear representation of one root test is
$$
     M_\lambda=\prod_{B\in\lambda}\left(1+\prod_{v\in B}u_v\right).
$$
The coefficient at $\prod_{v\in U}u_v$ is one exactly when $U$ is a union of blocks. Evaluation on Boolean inputs and extraction of multilinear coefficients are invertible linear changes of the $2^m$ coordinates. After performing the same change on each copy, a coordinate of the product tensor is indexed by $k$ subsets $U_j$, or a coloring $c:[m]\to[2^k]$ given by the membership bits. That coordinate is $[\lambda\preceq\ker(c)]$, where $\preceq$ means refinement. Thus the available span consists precisely of the partition-poset zeta columns indexed by partitions with at most $2^k$ blocks. All the zeta columns are linearly independent because a linear extension makes their matrix triangular with diagonal one. The discrete-partition indicator is the column indexed by the discrete partition itself. It enters the span exactly when $2^k\ge m$. An injective coloring then gives the required coefficient directly.

All component partitions occur in the one-chunk tagged graph, even with tags $p_i=i$ and strictly increasing targets $c_j=j$. For each $i$ choose the source payload $a_i$ to be a representative of $i$'s block. After contraction of the left edges, the right edges join each $i$ to its representative. This realizes the specified partition on the value vertices. The exact logarithmic cost is therefore relevant to this instance family. The bound allows completely arbitrary graph-independent weights. A circuit that inspects the original graph by additional means, or a different reduction to zero-or-one-model SAT, lies outside the statement. [Construction of the tagged graph](matrix-list-parity-graphs.md)
