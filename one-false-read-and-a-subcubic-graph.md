# Can one fewer input edit make a false RAM read genuine?

Consider a graph with one light and one switch at each vertex. Flipping a switch toggles the lights at its neighbors, leaving its own light alone. All lights start off. The requested final state has exactly one light on at a designated leaf. The input includes a switch set that achieves the request. Can any smaller set do so?

**Theorem.** On connected simple bipartite graphs of maximum degree three, explicit DIMACS 3-SAT reduces to this problem in linear time and encoded length. On every output, the supplied set is either optimal or exactly one switch larger than optimal. The latter occurs exactly when the source formula is satisfiable. On graphs of maximum degree two, the same single-light optimum is a shortest-path distance and is computable in linear time, including detection of infeasibility.

Graph adjacency can describe exactly which switch bits affect each final work-read value of a fixed, globally correct DIMACS SAT solver. Each editable switch occupies one ASCII bit of its input. Deciding whether one fewer edit realizes a specified accepting continuation has the linear, quadratic and cubic time questions of explicit SAT. Executing that solver on any of the files in this construction takes linear time. The distinction is between finding an input that induces prescribed replies and running the machine on a given input.

## From many odd rows to one lit leaf

Work over the binary field and write weight for the number of ones in a vector. Use the earlier linear-size compiler from explicit DIMACS to two permutations on q elements. In row notation the three positions are i, P(i), Q(i), using inverse arrays if the permutations were supplied as forward maps. The compiler produces distinct positions in each row, q divisible by three, and an identified column h with the following properties. Put a=q/3.

* Selecting exactly one position in every row is possible exactly when the source formula is satisfiable.
* Every exact cover uses a positions and leaves h unselected. Here h is the column H₀ in the six-row attachment. Summing the six integer equations forces the exchanged bits to agree. The two local exact covers are then {D,Z₀} and {D,Z₁}.
* The compiler supplies an odd-row vector w of weight a+2 with w_h=1. It is the reduction modulo two of the supplied integer solution with one entry equal to −1. Every odd-row vector x has weight a or at least a+2. Indeed, if t rows have three selected entries, the incidence count gives 3|x|=q+2t. Equality at a is precisely exact coverage.

The reduction from exact cover to general syndrome decoding is classical. The distinguished column and the supplied word from the six-row attachment are important to obtaining a gap of one here. [Source compiler and marker equations](two-permutations-and-the-explicit-sat-clock.md) · [Weight-gap proof](code-weight-and-sum-of-squares-for-one-negative-covers.md) · [Berlekamp, McEliece and van Tilborg](https://doi.org/10.1109/TIT.1978.1055873)

Introduce four banks of q binary switches x,v,u,t and one further switch b. The incidence graph has one vertex for each switch and one vertex for each equation below. The edge relation is occurrence. Right hand sides are zero apart from the first equation.

| Equations | Indices |
| --- | --- |
| t₀=1 | the target leaf |
| tᵢ₋₁ ⊕ tᵢ=0 | 1 ≤ i < q |
| vᵢ ⊕ xᵢ=0 | 0 ≤ i < q |
| uᵢ ⊕ x_P(i) ⊕ x_Q(i)=0 | 0 ≤ i < q |
| uᵢ ⊕ vᵢ ⊕ tᵢ=0 | 0 ≤ i < q |
| b ⊕ v_h ⊕ t_(q−1)=0 | one final equation |

The t path fixes every t to one. Next v=x and u is its coordinatewise complement, and the remaining equations on x say exactly that each source row has odd weight. The last equation fixes b=1−x_h. Hence every source solution has a unique lift on the switch side, of weight
```
2q + |x| + (1 − x_h).
```
The q complementary pairs contribute q, and the t bank contributes q. At R=2q+a+1 an exact cover has lifted weight R. Every other vector costs at least R+1. The supplied w lifts to weight exactly R+1 whether or not an exact cover exists.

Each x is in one copy equation and occurs once through each permutation. Each interior t is in two chain equations and one other equation. The initial t also has the root incidence, the final t has the marker incidence, and their missing chain neighbors leave room. The vertex v_h has exactly three incidences. All other degrees are at most three. Every position connects to its t vertex through its local equations, so the graph is connected. It has 4q+1 vertices in each part.

Let H have the equations as rows and the switches as columns. Allowing flips at *every* graph vertex imposes Hz=e_root on the switch bank and Hᵀy=0 on the equation bank. Taking y=0 attains any feasible switch weight. Any additional selected vertices cost their number in the other bank. Thus the undirected graph has precisely the stated minimum. The arrays, graph and supplied set all take O(q log(q+1)) bits and deterministic construction time, bounded by the source length up to a constant by the compiler.

Conversely, guess a switch value at every graph vertex, impose the neighbor parities and compare their total weight with the supplied radius. A bounded-fan-in adder tree costs O(V) gates on V bits, since height j costs O(j) gates per block of size 2^j. Encode it and the parity checks by gate clauses with fresh names. This costs O(V log(V+1)) bits and construction steps for bounded degree, linear in the graph encoding with fixed-width adjacency slots. It proves the reverse deterministic clock transfer for explicit encodings and time exponents at least one. The promise only concerns which graphs an algorithm must answer correctly.

## Every improvement can be far from the supplied set

The one-unit benefit can require replacing a linear number of supplied switch choices. Fix L≥1. In the marker equation replace its use of the final t by a fresh s and impose s=t_(q−1). Thus s is one and has a free incidence. From b grow a chain of L fresh equal copies of b. Start a second chain of L fresh switches at c by imposing c ⊕ b ⊕ s=0, and let each successive switch equal c. Now b has three incidences, s has three and every new equation has at most three.

All feasible switch-side solutions extend uniquely and pay exactly L+1 extra units of weight. The two chains together always contain L ones. The remaining one is s. In the supplied solution h is one, hence b=0. Every shorter solution must have an exact cover, so h=0 and b=1. It therefore differs from the supplied solution at **all 2L new chain positions**, in addition to b. This still holds when flips on both sides of the bipartite graph are permitted. An improvement must attain the global minimum and spend zero flips in the equation bank.

For L=q the graph still has O(q) vertices, so every improvement needs Ω(q) changed choices relative to the supplied set, or Ω(N/log N) physical positions in the explicit template below. This rules out testing a bounded Hamming neighborhood of the supplied set as a general way to decide optimality. Reading the public graph can still reveal these correlated changes without searching that neighborhood.

## The boundary at two incidences

More generally let H be any binary response matrix whose columns have at most two nonzeros. Take its rows as vertices and add a ground vertex. A column of weight two is an edge between its two rows. A column of weight one is an edge to ground. Drop zero columns. A selection with syndrome e_root has odd degree at the root and at ground. These two are in the same selected-edge component by the handshaking lemma. A shortest path uses no more flips than the selection. Conversely every root-to-ground path gives the required syndrome. Breadth-first search therefore computes the optimum, with infinite distance for an unreachable ground. Edge and vertex lists suffice to compute it in linear time. In the special undirected graph problem, connectedness, degree at most two and a target leaf force the graph to be a path. Number its vertices starting at one at the leaf. Its equations force all even-numbered switches on, while the last endpoint equation rules out odd path order. At even order every odd-numbered switch must be off. Thus whenever a solution is supplied on such a path, it is unique.

If instead the rows have arity at most two, a row specifies a value or a pairwise XOR. Propagate one starting value through each component of the variable graph and check consistency. Pins determine the component assignment, and on an unpinned component one takes the lighter of the two complementary assignments. This is also linear. The reduction reaches degree three on both sides simultaneously. The adjacency rule here is the open-neighborhood or non-reflexive version of Lights Out. Minimum-weight decoding and the graph game have substantial prior literature. Priority for the single-leaf, supplied-one-away, subcubic conjunction is unestablished. [Berman, Borer and Hungerbühler, *Lights Out on graphs*](https://doi.org/10.1007/s00591-021-00297-5)

## Smallest seeds for an improvement of exactly one

Seven vertices are necessary and sufficient in a connected simple bipartite graph with a target leaf to have solutions of weights d and d+1, where d is the minimum. In the switch bank opposite the target, both solutions must include its one neighbor. They differ on an odd kernel vector of weight at least three, since a connected graph with at least two vertices has no zero column. Both solutions use zero switches in the target's own bank: a nonzero homogeneous selection in that bank would add at least two to the opposite bank's minimum. The opposite bank therefore has at least four vertices. If the target's bank had at most two, all switches in the odd difference would miss the leaf and have precisely the same single remaining neighbor, or none. Connectedness and odd parity preclude a kernel vector in either case. This proves the seven-vertex lower bound without an enumeration.

The following two degree-three trees on vertices 0 through 6 start the two verdicts with the same supplied cost. Each listed pair denotes an undirected edge.

| Target | Edges | Supplied set | All minimum sets |
| --- | --- | --- | --- |
| 5 | 01, 13, 14, 26, 36, 45 | {2,3,4} | {0,4} |
| 3 | 04, 12, 13, 14, 25, 26 | {0,1,5} | {0,1,5}, {0,1,6} |

Without bipartiteness the minimum is five vertices, still at degree three. The target and its neighbor are fixed to zero and one respectively in every solution, by the alternating-form identity below and the leaf equation. An odd kernel difference cannot have weight one on a connected graph, so three further vertices are needed. Edges 01, 13, 14, 23, 24, 34 with target 0 have precisely the solutions {1,2} and {1,3,4}.

## The exact successor and the failed one-edge version

Let A be the adjacency matrix of any simple graph and r a distinguished vertex. If Ax=e_r then x_r=xᵀAx=0 since each selected edge contributes twice. Attach a path r—s—t with fresh vertices and move the target to t. The t equation forces x_s=1. The s equation gives x_t=x_r. The remaining equations are exactly the original Ax=e_r, hence x_t=0. This bijects *all* old and new solutions and increases every weight by exactly one. A target leaf stays a leaf at the new end, the maximum degree stays at most three on the constructed family, and a supplied near-optimal solution lifts explicitly. Repetition sends (R,R+1) to (R+j,R+j+1) for every j.

A single pendant edge behaves differently. Attach only s to r and designate s. Its equation forces x_r=1, and the old part satisfies Ax=x_s e_r. Alternation forces x_s=0. Thus the feasible sets are exactly kernel vectors of A with r selected and with the new switch off. Such a vector exists precisely when e_r is outside the image of A, by symmetry and kernel/image orthogonality. A one-edge extension actually reverses feasibility. These calculations use arbitrary simple graphs, including graphs with cycles of odd length. Starting from the two seven-vertex trees gives opposite answers at every supplied cost 3+j. Their optima are 2+j and 3+j. There is a uniform linear-time decision on this entire infinite family, even after relabeling. Starting at the designated leaf, delete its final two-edge extension, accumulating one forced switch per pair, until the two constant-size seeds can be checked directly. In the densely indexed graph, adjacency and degrees need one initial scan. A complete fallback handles graphs outside the family. The two-edge operation gives a successor for minimum edit distance. It gives no lower bound on the number of executed RAM instructions per encoded bit.

## An ordinary SAT input and one erroneous work read

Here are the input bits whose edits count. The public part is a canonical DIMACS template. It contains the graph and its root in ordinary comments and represents each switch j by two complementary variables with decimal names 10(j+1) and 10(j+1)+1. A positive pin selects one name. Only the final ASCII 0/1 of that occurrence is editable. Choose the second name for value one. The complement relation fixes the value of the second variable accordingly. Each switch costs exactly one physical bit to flip, even if other copies of its name occur in the file.

For every vertex impose that the XOR of its neighbors' second variables equals the target bit. At arity three one proper ternary clause forbids each wrong three-bit pattern. Use the same construction at lower arity and pad short clauses with distinct false anchors. Seven proper clauses on three fresh anchors pin them jointly to zero. A constant false constraint, if needed, is the positive clause on those three anchors. Use fresh names above the switch region for the anchors. Pin unused declared names to zero with the same anchors if dense naming and uniqueness on declared names are desired. Complement relations and switch pins likewise use padded clauses. This yields proper formulas of O(V log(V+1)) bits. For each fixed graph all switch settings give valid files of identical length, and each satisfying one has a single assignment under the dense convention.

One fixed SAT program parses the public graph and the selected pins, checks that the rest of the file is precisely the prescribed DIMACS encoding, and uses a complete decision procedure if recognition fails. A comment alone is never accepted as evidence of the formula's clauses. On recognized files it computes each neighbor parity, stores it as a separate word, resets all switch-dependent architectural registers, retaining only public bank pointers and counters, and then reads all parity words once in a fixed order starting at the root. It compares their vector to the singleton target and returns the result. The suffix is read-only, with a fixed address sequence and no early exit. Scanning, regenerating clauses for comparison, and forming the parity words take O(N) native steps in the encoded length N. This can be done by scanning the decimal characters of each field; the names and regenerated indices fit in logarithmic words.

On the all-zero switch file the genuine suffix reads all zeros. Change only the first reply from zero to one and this continuation accepts. Deciding whether at most R allowed edits to the original file make exactly this suffix genuine is precisely the graph problem above. A supplied R+1 edit set always works. Prefix stores change on the edited file. The fabricated full execution on the old file cannot itself become a valid execution while retaining its disagreeing store history.

There is also a version requiring the SAT verdict to stay fixed under all edits. Give the recognizer a second public template with the same pinned switches and graph comments, omitting the row parity requirements. Every such file has a unique model. Perform the same parity computation, reads and comparison, then return true in this mode. The exact same optimization problem now realizes the specified *internal* continuation exclusively on satisfiable inputs. These constructions identify the difficulty of searching for a continuation even when the actual solver handles the whole template quickly. A time lower bound would need a property that forces expensive actual runs on some inputs for every correct solver.

## Checks

The finite audit solves the binary systems by independent elimination. It checked 662 cubic systems, including 93 with a one-negative witness. Three explicit two-patch marked graphs have supplied weight 30 and optima 30, 29 and 29. The audit also rendered both DIMACS templates for the marked examples, checked properness, audited their pinned valuations, and counted changed physical bits. Running the audit with `--picosat` independently found the expected zero or one models for each of the 30 serialized cases. Exhaustion of all 5,405 labeled rooted simple graphs on one through five vertices checked the entire solution-set bijection under two-edge extension. The 1,458 degree-at-most-two cases also matched shortest-path distances, including infeasible targets. Lean proves the unique lift, its weight, the marked one-unit gap the root-equation successor, and its two-edge form for every simple graph. The native program, cost accounting and full reduction are manuscript proofs. [Finite audit](one_false_read_syndrome_audit.py) · [Lean lemmas](OneFaultSyndrome.lean)
