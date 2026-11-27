# A seven-variable formula that needs three independent cycles

For the fixed positive formula
$$
 F=(x_1\lor x_2\lor x_3)(x_1\lor x_2\lor x_4)
 (x_3\lor x_4\lor x_5)(x_1\lor x_5\lor x_6)
 (x_3\lor x_6\lor x_7),
$$
the minimum feedback-edge count of a Boolean network of arity at most three representing $F$ on all assignments is exactly **three**. There is one external terminal for each input. Internal edges are existentially quantified and vertex tables are arbitrary. Swapping $x_3,x_4$ gives the same result for the other choice of last clause. The four-variable prefix has a tree representation. Adding each subsequent clause forks two old terminal wires and costs at most one extra cycle, giving the upper bound. The successive optimal counts at four, five, six and seven variables are $0,1,2,3$. [Definition and forest compression](cycles-needed-to-represent-a-ternary-formula.md) · [Prefix bounds and successor operation](one-clause-successors-that-force-an-extra-cycle.md)

## Reducing two cycles to three paths

A cut through $k$ Boolean edges covers the assignment relation by at most $2^k$ rectangles across the two sets of terminals. Fix the cut-edge values and independently choose the internal extensions on each side. A set of $s$ accepted entries, each two of which have a rejected crossed entry, needs at least $s$ rectangles. Checking the 128 assignments of $F$ gives the following.

* All 21 cuts of two terminals against five have three such accepted entries.
* For 34 of the 35 cuts of three terminals against four, there are five such entries. The exceptional three terminals are $x_3,x_6,x_7$.

One may connect terminal-bearing components by subdividing one edge in each with an equality-through vertex that ignores a new port and joining the new ports. This preserves the represented relation and the feedback-edge count. Discard terminal-free components after evaluating them. Prune empty branches and compose degree-two path tables. A tree has a two-leaf cherry, which would give a one-edge cut of those terminals. If a cyclic core has a hanging tree with two or more terminals, a deepest branching subtree in the hanging tree gives such a cut. Thus each hanging tree supplies at most one terminal. Its binary relation between that terminal and the attachment port can be absorbed into the attached table.

A single cycle would have seven terminals in circular order. Its consecutive triples give distinct cuts through two edges, contrary to the single exception. With two cycles the connected core of minimum degree two has exactly two degree-three hubs, by the degree sum. Suppressing its degree-two paths gives either three paths between the hubs or two loops joined by a bridge. Terminals occur at degree-two sites along the three paths, counting a loop as a path from its hub to itself. Four terminals on any path would yield two different consecutive triples, each isolable by two edges. The path lengths in terminal sites must therefore be $3,2,2$. In the two-loop case one loop has exactly two terminals and can be isolated across the bridge path by a single cut. This excludes the two-loop case. On the remaining graph the longer path must carry precisely the exceptional triple.

## What the three-site path can transmit

Use the order $x_3,x_6,x_7$ for the three bit positions within an assignment to the exceptional triple, least significant first. A column is an eight-bit mask of the assignments accepted at a fixed value of all other terminals. In little-endian order on $x_1,x_2,x_4,x_5$, the sixteen columns are
$$
(0,170,136,170,136,254,204,254,0,254,254,254,170,254,254,254).
$$
For a fixed external bit at one site, its local table is a $2\times2$ Boolean matrix on the adjacent path wires. Multiplying the three matrices over OR and AND gives four eight-bit masks $Q_{ij}$, indexed by the left and right ends of the path. When the outside terminals are fixed, their column must be the union of those $Q_{ij}$ for which the rest of the graph permits $(i,j)$. A column $c$ can be such a union exactly when the union of all $Q_{ij}\subseteq c$ is $c$.

Enumerating all $256$ ternary tables at each position gives 288 distinct compatible ordered tuples for the order $x_3,x_7,x_6$ and 288 for the reverse. The other four orders yield none. An example of a compatible tuple is $(16,34,68,136)$. Thus a four-rectangle bound alone permits the long path. The 576 tuples give 72 classes after independent flips of the two endpoint bits and transposition. Flips can be absorbed into the adjacent hub tables. Transposition interchanges the two hubs and reverses the short paths, whose orders are included in the next check.

## Excluding the remaining hubs and short paths

Choose the order of the other four terminals on two ordered paths of length two. There are twelve cases after interchanging the short paths. For each case the finite search chooses two arbitrary ternary hub tables and four arbitrary ternary site tables. For each four-bit assignment $z$ to the outside terminals let $A_z,B_z$ be the two products of the short paths' site matrices. The relation between the long path's endpoints through this side is
$$
 O_z(a,b)=\bigvee_{i,j,u,v\in\{0,1\}}
      H_L(a,i,j)\land A_z(i,u)\land B_z(j,v)\land H_R(b,u,v).
$$
Every site or hub table in this equation has one shared set of truth-table entries for all sixteen choices of $z$. The finite proposition asks whether, simultaneously for all $z$, the union of the $Q_{ab}$ with $O_z(a,b)=1$ equals the prescribed column, for some one of the 72 compatible path signatures. Every one of the twelve propositions is false.

The audit generates the AND/OR equalities as CNF and obtains a CaDiCaL refutation for each case. A separate implementation validates each added clause by replaying its supplied unit-propagation hints and checks that an empty clause is derived. A positive control fixes all six tables and verifies that targets obtained by direct enumeration of the eight outside wire values are accepted. No external certificate archive is needed to reproduce the checks. The topology reduction above is a manuscript proof; the finite search checks the normalized graph. The formula itself is satisfiable by setting every input to one. [Reproducible search and proof checker](seven_terminal_theta_audit.py)
