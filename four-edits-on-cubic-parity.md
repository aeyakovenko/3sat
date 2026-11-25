# Four literal changes can recover an unsatisfiable cubic parity formula

Let $G$ be a simple, 3-vertex-connected cubic graph. Give each vertex a prescribed parity for its three incident edge bits and suppose the XOR of the prescribed parities is one. Encode every vertex by the four proper clauses forbidding its four incorrect local rows. Select one, two or three distinct vertices. At each selected vertex flip one literal sign in exactly one of its four clauses. **Every resulting formula is satisfiable.** Four changed vertices suffice for an unsatisfiable example on $K_4$.

One sign flip replaces the forbidden local triple $b_v$ by $a_v$, differing on the corresponding incident edge. Thus $b_v$ is newly admitted and violates the original parity, while $a_v$ is newly forbidden and satisfies the original parity. This distinguishes the edit from deleting a clause, which admits $b_v$ without withdrawing any row. Minimality under ordinary clause deletions is a known property of unsatisfiable Tseitin formulas on 2-connected graphs. [Itsykson, Riazanov and Smirnov, Lemma 2.18](https://drops.dagstuhl.de/storage/00lipics/lipics-vol236-sat2022/LIPIcs.SAT.2022.6/LIPIcs.SAT.2022.6.pdf#page=8)

## One original parity violation

At a selected vertex $u$ fix all three bits to $b_u$ and impose the original parities at all other vertices. The graph $G-u$ is connected. The residual charges sum to zero, since $b_u$ has the opposite of the prescribed parity. A spanning tree extends the pinned values to a solution. Sample uniformly among those extensions. Every selected vertex $v\ne u$ now satisfies its edited clauses unless its local pattern equals $a_v$.

For $v$ nonadjacent to $u$, each of its four original good triples occurs with probability $1/4$. For $v$ adjacent to $u$, its shared edge is fixed and its two consistent good triples each occur with probability $1/2$. To verify the counts, fix any consistent good triple at $v$ and remove $u,v$. The remaining graph is connected, and summing the adjusted charges gives zero. Each resulting affine system has the same homogeneous solution space on the remaining edges, independently of the prescribed bits. Thus all the stated triples have equal positive extension counts.

For one or two edited vertices, the chance of a newly forbidden triple elsewhere is at most $1/2$. For three vertices which do not form a triangle, choose $u$ adjacent to at most one of the others. The union bound is at most $3/4$. In each case a satisfying extension exists. The same argument shows that four edited vertices including one isolated in their induced subgraph always give SAT.

## Three vertices forming a triangle

Suppose every choice of $u$ as the sole original violation fails, and denote the other two vertices by $v,w$. Each of the two failure events has probability at most $1/2$. To cover all extensions, each must have probability exactly $1/2$ and they must be disjoint. In particular $a_v(uv)=b_u(uv)$ and $a_w(uw)=b_u(uw)$. These equalities hold for every ordered pair of distinct triangle vertices by varying $u$.

With $b_u$ fixed, the shared edge $vw$ takes both values. Its value and the fixed edge $uv$ determine the whole good triple at $v$, by parity. The same holds at $w$. The two failure events are therefore exactly the two restrictions on $vw$ to the bit in $a_v$ or $a_w$, respectively. Disjointness implies $a_v(vw)\ne a_w(vw)$. The ordered-pair equalities already give $a_w(vw)=b_v(vw)$, so $a_v$ and $b_v$ differ on $vw$. Repeating the argument with the other possible outsider shows that $a_v,b_v$ also differ on $vu$. This contradicts a single flipped literal. Some choice of $u$ must succeed.

## Exact exhaustion on the four-vertex complete graph

Use vertex order $0,1,2,3$, charges $(1,0,0,0)$, and edge order $01,02,03,12,13,23$. In a vertex's local triple, its neighbor positions are in increasing order with the first being the least significant bit. A failing example re-admits $b_v$ and withdraws $a_v$ as follows.

| Vertex | Newly admitted $b_v$ | Newly forbidden $a_v$ | Flipped edge |
| --- | ---: | ---: | --- |
| 0 | 0 | 1 | 01 |
| 1 | 1 | 0 | 01 |
| 2 | 4 | 5 | 02 |
| 3 | 4 | 6 | 13 |

Undoing the edit at vertices 0, 1, 2, 3 in turn yields respectively 3, 3, 1, 1 satisfying assignments. The assignment integers 1, 0, 39, 56 give respective witnesses in little-endian edge order.

| Changed vertices | Labeled choices | UNSAT | SAT |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 48 | 0 | 48 |
| 2 | 864 | 0 | 864 |
| 3 | 6,912 | 0 | 6,912 |
| 4 | 20,736 | 96 | 20,640 |

Every four-edit UNSAT formula in this table is minimally unsatisfiable. The checker tested each of the 16 single-clause deletions on each of the 96 examples. For each graph it enumerates every labeled edge assignment, records its local triple at each vertex and intersects the exact sets of surviving assignments for every edit choice. Each edited site has twelve options, given by its four original forbidden triples and three incident edges. On both the triangular prism and $K_{3,3}$ the same checker finds SAT in every one of the 311,040 four-edit choices and every choice with one through three edits. [Census](four_cubic_edits_audit.py)

The [Lean check](FourCubicEdits.lean) independently evaluates all 64 assignments for the displayed example in the kernel, verifies an explicit satisfying assignment for each clause deletion, and checks the final logical implication in the triangle case. The connectivity and distribution argument for arbitrary graphs is given above. The theorem concerns a satisfiability transition under edits. It supplies no superlinear RAM time bound. Priority for the edit threshold is unestablished.

## Why the four-edit exception requires exactly four vertices

**Among all simple 3-vertex-connected cubic graphs, only $K_4$ admits an unsatisfiable formula after exactly four such edits.** The reduction to the following finite census uses the connectivity of the actual graph. Let $M$ consist of the four edited vertices. The union bound above handles the case in which one has no neighbor in $M$. Otherwise each of the four vertices has at most two edges leaving $M$.

Contract every connected component of $G-M$ to a pure parity vertex. Its new charge is the XOR of its vertex charges. The boundary bits extend internally exactly when their XOR equals that charge, by tree elimination. Keep parallel boundary edges as distinct variables. Each such component must meet at least three distinct vertices in $M$. Removing fewer endpoints would otherwise separate that component from the surviving marked vertices. There are at most eight boundary ports altogether, hence at most two pure components. Deleting any two marked vertices leaves the quotient connected, since it is a contraction of a connected graph. On the connected quotient, negating an edge variable toggles both endpoint charges and transports the twelve possible edits bijectively. Spanning-tree elimination therefore makes it sufficient to test the odd charge at vertex zero alone.

The [quotient census](four_cubic_quotients.py) takes all $2^6$ simple internal graphs on the four marked vertices and discards those with an isolated vertex. For internal degree $d_i$, it assigns each of the $3-d_i$ remaining ports of vertex $i$ to a pure component. It checks the three-distinct-neighbors condition and connectedness after deleting every pair of marked vertices, then identifies graphs under permutations within the two vertex classes. This generates a superset of the quotients realized by the graph theorem. The numbers of types with zero, one and two pure components are $1,5,5$. For each type, enumerate all its edge bit assignments satisfying the pure vertices and all $12^4$ edit choices on the marked vertices. The ten types with a pure component have no unsatisfiable edit choice. The one type without a pure component is $K_4$ and gives the 96 cases above.

## A radius that grows with girth

Let a connected simple cubic graph have $N$ vertices, girth $g$, and positive edge expansion $h$. Thus any set of at most $N/2$ vertices sends at least $h$ times its size in edges to its complement. For any odd reference charge, *every* nonempty choice of $k$ edited sites with $k<hg/(3+h)$ is satisfiable.

Let $M$ be the edited sites. Among the components of $G-M$, all those of size at most $N/2$ together have at most $3k/h$ vertices. Indeed all their outgoing edges enter $M$. Since $g\le N$ and $k(1+3/h)<g$, some component $B$ has more than $N/2$ vertices. The set $S=V(G)\setminus B$ has size at most $(1+3/h)k<g$ and induces a forest.

Root one tree at an edited vertex $u$ and fix its local bits to $b_u$. Root every other tree arbitrarily. In parent-first order, every other vertex has at most one incident edge already set, so it has at least two available original good triples. Choose one avoiding its withdrawn triple if it is edited. This assigns every edge incident to $S$. Exactly one original vertex parity has been violated there. Since the original total charge was odd, the residual total charge on the connected component $B$ is zero and tree elimination completes the assignment. This proves a growing interval of satisfiable positive perturbations whenever $hg/(3+h)$ grows. An algorithm on the promised interval can return SAT immediately when a nonempty edit is promised, so the interval supplies no RAM running-time lower bound.
