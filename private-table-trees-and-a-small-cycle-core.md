# Gluing private SAT tables around a small number of cycles

Attaching many independent pieces to a common SAT instance can require new input reads while allowing one computation to serve all the attachments. Here the pieces have explicit Boolean truth tables. Even an unbounded number of pieces meeting one large table at different sets of ports can be processed in a single packed scan for fixed port width. The same scan removes trees and long paths from a cyclic instance. The remaining search depends on the number of independent cycles.

Let a finite connected simple graph have a Boolean table at vertex $v$ on $k_v$ local coordinates. An edge specifies equalities between matching ordered lists of at most $r$ coordinates at its endpoints. An assignment selects an allowed table row at every vertex and respects each wire equality. With globally named variables this is ordinary conjunction when each variable's occurrences are connected by edges carrying that variable. The local-coordinate formulation also permits arbitrary supplied wiring. Fix $r$. Tables are supplied densely in binary row order on a RAM with $w=\Theta(\log N)$ bits per word, where $N$ is the total encoded length. Write $M$ for the word cost of reading the graph and its coordinate maps, including one unit per vertex and edge. Put
$$
  P=M+w^2+\sum_v\left\lceil 2^{k_v}/w\right\rceil,
  \qquad \beta=|E|-|V|+1 .
$$
The one-time $w^2$ term suffices to build the short tables of bit masks and binomial coefficients used for indexing. Already packed tables may begin at arbitrary bit offsets. A block of at most one word then takes at most two loads.

**Theorem.** For a tree the decision takes $O_r(P)$ deterministic word instructions. For $\beta\ge1$ the time is
$$
    O_r\bigl(P+\beta^2 2^{r(2\beta+1)}\bigr)
$$
when the intermediate tables are addressable. There is always a polynomial-space implementation in $O_r(P+\beta 2^{3r\beta})$ time on the logarithmic-word RAM. In particular, the first bound fits $O_r(N)$ time if $M=O(N)$ and $2r\beta\le\log_2 N-3\log_2\log_2 N$ for sufficiently large $N$. Its intermediate tables then fit in linear space. Table entries and metadata both count as input. An implicit constant-true table on arbitrarily many coordinates would change this accounting.

## Filtering many neighbors during a packed scan

At a bag with $k$ coordinates, suppose the children have already returned their possible row projections onto their incident edges. Each forbidden child tuple is a conjunction of at most $r$ prescribed bit values. Reject a local assignment if it matches any of these conjunctions. There are at most $2^r$ conjunctions to import per child. A repeated pin with inconsistent prescribed values makes that particular conjunction empty.

Let $q=\min(k,\lfloor\log_2 w\rfloor)$ and put the $2^q$ assignments of the lowest coordinates in one word. Call each of the remaining coordinates high. For every signed pattern on at most $r$ high coordinates store a word whose set bits are the low assignments forbidden by imported tuples with that high pattern. A tuple contributes the intersection of at most $r$ public bit masks. Combining it with the stored word takes one OR. Empty high patterns are allowed.

Branch on each high coordinate in order. In each branch delete incompatible patterns, remove the decided bit from compatible patterns, and OR words with equal remaining patterns. After the last high bit, a single forbidden word remains. AND its complement with the relevant packed block of the input table. This gives all feasible low assignments for that high prefix.

There are $A(j,r)=\sum_{i=0}^{\min(j,r)}2^i\binom ji$ possible patterns on $j$ high coordinates. Copying and updating both branches costs $O_r(A(j,r))$ at their parent. A deterministic index consists of the cardinality, the combinatorial rank of the ordered subset and its sign bits. Each calculation uses at most $r$ coordinate positions and precomputed binomial coefficients. Folding all the levels at a bag with $h=k-q$ high coordinates costs
$$
  O_r\!\left(2^h\sum_{j=0}^h 2^{-j} A(j,r)\right)=O_r(2^h).
$$
Indeed $\sum_{j\ge i}\binom ji 2^{-j}=2$ for each $i$, by the negative binomial series. The bound includes the initialization of the pattern array. For $k\ge q$, $2^h=O(\lceil 2^k/w\rceil)$ with the choice of $q$ above.

Project the feasible rows onto any requested set of $u$ local coordinates. During the high-coordinate traversal, carry the index of the selected high bits and OR the feasible word into an accumulator at that index. Only after all high prefixes have been processed, test each accumulator against masks for the assignments to the requested low bits. Build those masks by repeatedly splitting the previous list on one selected coordinate. The number of resulting tests across all accumulators is $2^u$. Thus projection adds $O(1+2^u)$ to the scan, even when $u$ is large. The output order can be arbitrary by carrying the contribution to its output index when a bit is set. An ordered list of repeated ports can be read from the resulting projection on distinct coordinates.

Postorder tree processing now gives the first bound. Each child message has at most $2^r$ bits and each bag scans its own table once, independently of its degree. The proof uses the classical acyclic join projection principle. The word bound above makes the dependence on the dense table format and unbounded branching explicit. [Yannakakis, *Algorithms for Acyclic Database Schemes*](https://www.vldb.org/dblp/db/conf/vldb/Yannakakis81.html)

## Removing the long tree paths

Choose a spanning tree and mark the endpoints of its $\beta$ omitted edges. Peel its unmarked leaves, passing the preceding projection to the next vertex. The remaining tree is the minimal subtree containing the marked vertices. Keep every marked vertex and every branching vertex of this subtree. If there are $p$ distinct marks, there are at most $p-2$ unmarked branching vertices when $p\ge2$. Thus at most $4\beta-2$ vertices remain special for a simple connected graph with $\beta\ge1$.

At every surviving vertex compute its feasible relation after all previously peeled children have imposed their constraints. Project onto the union of the ports to its remaining neighbors and to any omitted edges. An unmarked degree-two vertex has at most $2r$ such coordinates. Compose its binary relation along its path with those of other degree-two vertices. Trying every incoming port tuple and carrying the set of feasible outgoing tuples costs $O_r(1)$ per vertex. A path consisting of a single tree edge transfers its tuple by identity. The special vertices are now joined by a tree of binary transfer relations, in addition to the omitted edges. This replacement preserves satisfiability in both directions: path interiors and peeled subtrees have disjoint local variables, and their messages record precisely when the adjacent choices extend.

At a special vertex every incident branch of the minimal subtree contains at least one marked endpoint occurrence away from that vertex. Those branches are disjoint. Adding its own endpoint occurrences gives at most $2\beta$ incidences in total. Hence a special table has at most $2r\beta$ projected coordinates. All the projection work beyond the scan totals $O_r(\beta 2^{2r\beta})$. Each actual special table has at most as many entries as its original input table.

One algorithm assigns the tuples of the $\beta$ omitted edges by depth-first enumeration, using at most $2^{r\beta}$ trials. For each trial, pin the corresponding local coordinates and solve the tree of special vertices and transfers from the leaves. Each local row can be tested in time proportional to the number of its incident relations, with constants depending on $r$. The sum of these degrees is $O(\beta)$. A trial thus costs $O_r(\beta 2^{2r\beta})$. It stores the original projections and tree messages, and never allocates a table indexed by all omitted-edge tuples. This gives the polynomial-space bound.

Contraction orders and their edge boundaries are classical in tensor-network algorithms. Here the factors use Boolean conjunction and existential projection. [Markov and Shi, *Simulating quantum computation by contracting tensor networks*](https://arxiv.org/abs/quant-ph/0511069)

For the smaller exponent, install a degree-two factor vertex for every path transfer, with a distinct edge to each endpoint. Each original omitted edge still carries one shared tuple. The resulting connected factor graph has $O(\beta)$ vertices, minimum degree at least two and cycle rank $\beta$. An assignment now gives one tuple to every edge and satisfies the incident factor at every vertex. If two ports of the same factor refer to one local bit, the two edge labels must agree there; this check is part of that factor.

Contract vertices in any connected order. For a connected prefix $S$, keep the feasible tuple table on its edge boundary $\partial S$. The induced subgraph on $S$ has cycle rank $\beta(S)$ and
$$
 |\partial S|=2+\sum_{x\in S}(\deg(x)-2)-2\beta(S).
$$
When adding an adjacent vertex $v$, its incident edges and the existing boundary have at least one edge in common. Their union therefore has size at most $3+\sum_{x\in S\cup\{v\}}(\deg(x)-2)\le 2\beta+1$. Here nonnegativity of every summand and total excess $2\beta-2$ are essential. Enumerate tuples on this union, retain those accepted by both factors and project to the new boundary. Each union has at most $r(2\beta+1)$ bits. Evaluating and projecting a tuple in $O_r(\beta)$ operations suffices. The resulting boundary table has at most $2^{2r\beta}$ entries. The number of contractions is $O(\beta)$, as required. For larger parameters polynomial-space conditioning avoids any assumption of exponentially many addressable cells.

## What this tests on actual SAT inputs

The private-table conjunction has an ordinary proper 3-CNF realization. Give each local port its own variable and encode each edge equality by two implications. Within a bag use a binary multiplexer tree selected by its $k_v$ port variables. Pin its $2^{k_v}$ leaves to the supplied table values and require the output true. Constant-size Tseitin clauses per gate suffice. Pad binary and unit clauses to proper ternary using local fresh variables and all required sign choices. Auxiliary variables at different bags are private. The resulting formula is satisfiable exactly when the tables and wires are consistent. On a canonical layout whose graph description is supplied, the rows can be rendered or compared in time linear in the spelled-out DIMACS length, then fall back to a general solver on a mismatch. The displayed packed bound applies to the underlying supplied dense tables; recognizing an arbitrary unrelated DIMACS decomposition has a separate cost. [Earlier construction for two glued tables at high bit density](doubling-a-glued-sat-interface.md)

One cycle already includes tripartite triangle detection when its port width grows. Take three tables on coordinate pairs $(X,Y),(Y,Z),(Z,X)$, with each symbol an $r$-bit label, and make the three equalities into a cycle. Feasibility is exactly a triangle in the three bipartite graphs, on an explicit input of $3\cdot 2^{2r}$ table bits. Thus the fixed-width and small-cycle bounds identify a class of amplifications absorbed by one scan plus a bounded residual computation. An unrestricted SAT time lower bound is still missing. [Triangle queries in the SAT journal](affine-batches-of-butterfly-queries-and-triangle-parity.md)

The reproducible audit checks all 4,096 one-bit triangle instances against direct enumeration and both core algorithms. On 500 seeded connected instances of cycle rank zero through three it tests three choices of lane width and all global assignments. It also tests connected contractions on 478 of these instances; the audit skips brute contraction tables above twelve bits. The code checks the mathematical reductions, rather than benchmarking the RAM cost of Python integer operations. No priority claim is made for these bounds. [Audit program](private_table_cycle_core_audit.py)
