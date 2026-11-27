# Which minimal SAT obstructions survive one more clause?

For proper 3-CNF, where each clause contains three distinct variables, eight is the first possible number of clauses for UNSAT. At four variables there are 272 distinct eight-clause UNSAT cores and 9,408 inclusion-minimal nine-clause cores. Among the latter, exactly 384 require replacing at least two clauses of *every* eight-clause core on the same four names. Replacing two with three suffices for all 384. A different operation that introduces a fresh variable reaches 192 of the 9,408 starting from three variables. It has the advantage that its preservation of minimal unsatisfiability can be proved for *every* size.

Counts here distinguish variable names and signs, ignore clause order, and count each set once. Minimal means deletion of any one clause makes the formula SAT. Repeated copies cannot occur in a minimal core.

## Eight clauses at any number of variables

Each clause forbids exactly one eighth of the assignments. Eight cover the cube exactly when their forbidden subcubes partition it. In a partition of the binary cube into $m$ coordinate subcubes, at most $m-1$ coordinates are fixed somewhere. Indeed for each such coordinate $i$ form the vector of conditional means of its random sign $(-1)^{x_i}$ on the $m$ parts, with inner product weighted by part probability. This vector is nonzero and perpendicular to the constant vector. Vectors for distinct coordinates are perpendicular because the coordinates are independent within each subcube and their unconditional sign product has mean zero. This limits the number of nonzero vectors to $m-1$.

Consequently checking at most seven variables suffices for all eight-clause cores, even if the original input uses arbitrarily large variable names. To count exact partitions, take the first uncovered assignment, branch on every disjoint clause that forbids it, and recurse. Each unordered partition is visited once. Classifying by the number of used variables gives the count on $v$ available names
$$
 A(v)=\binom v3+268\binom v4+3030\binom v5+7800\binom v6+5040\binom v7.
$$
Our code recovers the coefficients from $v=3$ through 7, then checks the formula separately by complete enumeration at $v=8,9$. In particular $A(v+1)-A(v)$ is obtained by lowering each lower binomial index by one, counting exactly the cases that use the added name. The coefficients are already reported in a prior census, and general uniform subcube partitions have an extensive literature. [Prior numerical census](https://ideosphere.ai/papers/dupfree-contradiction) · [Filmus et al., *Irreducible Subcube Partitions*](https://arxiv.org/abs/2212.14685) · [Tarannikov on the general enumeration problem](https://doi.org/10.33048/semi.2024.21.096) · [Our enumeration](../audits/small_sat_core_lifts.py)

## Exhausting the next clause and every subsequent four-variable layer

On four variables the 32 signed clauses correspond bijectively to the 32 edges of the four-cube. The endpoints are the two assignments falsifying the clause. An UNSAT formula is an edge cover of the 16 vertices. It is minimal precisely when every chosen edge has an endpoint of chosen degree one. Therefore every connected component of its chosen edges is a star, including a single edge. Conversely every vertex partition into such stars gives a minimal cover. A star contains at most five vertices, so at least four components are needed. A star forest with $s$ components has $16-s$ edges. This exhausts all possible minimal core sizes from 8 through 12.

For each child $F$ of size $m>8$, let its distance be $\min_P|P\setminus F|$ over minimal parents $P$ of size $m-1$ on these four names. Distance $j$ amounts to deleting $j$ parent clauses and inserting $j+1$. It cannot be zero by the child's minimality.

| Clauses | Minimal UNSAT sets | Distance 1 | Distance 2 |
|---:|---:|---:|---:|
| 8 | 272 | — | — |
| 9 | 9,408 | 9,024 | 384 |
| 10 | 29,792 | 29,792 | 0 |
| 11 | 10,656 | 10,656 | 0 |
| 12 | 400 | 400 | 0 |

The checker partitions vertices into disjoint stars by putting the least remaining vertex in its unique next component. For each $j$ it indexes all $(m-1-j)$-subsets of parents and matches against children with $j+1$ clauses removed. This computes the entire table exactly. An independent C++ search visits all $\binom{32}{9}=28,048,800$ nine-clause subsets, checks all 16 assignments for coverage and private endpoints, and compares every minimal result to all 272 perfect matchings. It finds 15,936 UNSAT sets in total. Of those, 6,528 have redundant clauses. This also equals $272\cdot24$ because a perfect matching extends by one of 24 unchosen edges, and the union of two distinct perfect matchings needs at least ten edges. [Complete layer and edit census](../audits/small_sat_core_lifts.py) · [Independent nine-clause census](../audits/small_sat_minimal_cores.cpp)

## Adding one clause and one fresh variable at every size

For any three literals $a,b,c$ on distinct variables, use a fresh $z$ and replace a single clause by
$$
 (a\lor b\lor c)\quad\longmapsto\quad
       (a\lor b\lor z)\ \land\ (a\lor c\lor\neg z).
$$
On every assignment to the old variables, existentially eliminating $z$ recovers the original clause. Thus the entire formula has exactly the same projection of its satisfying assignments. Moreover, if the original formula was minimally unsatisfiable, then so is the new one. For a deleted old clause, take its old satisfying witness and extend it using the projection identity. For a deleted child, take any witness for the old formula with the parent deleted and choose $z$ to satisfy the surviving child. Both output clauses still have three distinct names. This is an inverse instance of singular Davis–Putnam elimination. [Kullmann and Zhao](https://arxiv.org/abs/1202.2600) · [Lean check of the local identities](../lean/ClauseSelectorLift.lean)

Starting with the three-variable eight-clause core and four available names, choose the fresh name in four ways, the parent in eight, the shared literal in three, and the assignment of the two other literals to the children in two. All $4\cdot8\cdot3\cdot2=192$ results are distinct. The fresh variable is uniquely identifiable by occurring exactly twice, and eliminating it reconstructs the parent. The independent nine-clause census confirms that precisely those 192 minimal cores have a variable with two occurrences. The other 9,216 give explicit failures of this single inverse rule as a generator for the whole next layer.

The operation still gives an infinite sequence of proper minimally unsatisfiable formulas, with a new essential clause and a new used variable at each step. It even gives an exact lower bound on the actual UNSAT input of a fixed-layout selector family. Allow each mandatory clause to be replaced by a satisfiable filler on disjoint fresh names. With selectors $x_1,\ldots,x_m$, SAT has value $1+\prod_i x_i$ over $\mathbb F_2$, since every proper subset of a minimal core is satisfiable. The uniquely rejecting input needs $m$ independent affine tests: any affine fiber of smaller codimension containing it contains an accepting input too. This holds along the entire sequence, without duplicating original clauses.

For a predetermined expansion schedule these instances have a fast promised-input decision. Scan the records for a disabled clause and accept as soon as one is found. For example, repeatedly expand a designated child, writing one completed clause per stage and using consecutive fresh names. A general solver can also recognize the resulting fixed sequence of expected record types and the permitted fillers in one pass, then fall back on other formulas. In a fixed-width binary-name layout these inputs use $\Theta(m\log m)$ bits and each record takes a constant number of logarithmic words. The scanner needs $O(m)$ word operations. The lifted invariant forces sensitivity to every clause on the UNSAT run. It permits the same solver to check each clause just once. The authorship search found related structural and counting results; priority for the four-variable edit-distance table is unverified. [Native clocks and a second one-clause induction](small-sat-exhaustion-and-a-one-clause-lift.md)
