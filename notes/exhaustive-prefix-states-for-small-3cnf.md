# Exhausting every clause prefix on three, four and five variables

A deterministic one-pass reader for satisfiability of proper 3-CNF on $v$ named variables needs exactly 256 states at $v=3$, 43,146 at $v=4$, and 120,510,132 at $v=5$. The clause stream may be arbitrarily long and may repeat clauses. Each clause has exactly three literals on distinct variables. The state count includes finite control, with no charge for the size of the fixed transition table. The numerical counts of representable truth tables were already recorded in OEIS. The experiment reproduces them by enumerating the behavior of all prefixes against future clauses, then measures how quickly shorter suffixes separate them. [OEIS A112535](https://oeis.org/A112535) · [Executable census](../audits/small_cnf_prefix_quotient.py)

## Seven additional clauses always suffice to distinguish two prefix functions

Write $U\subseteq\{0,1\}^v$ for assignments forbidden by a prefix. Each proper width-$k$ clause forbids one coordinate face of codimension $k$. Adding a clause takes the union of $U$ with this face. A stream is unsatisfiable exactly when its union covers the cube. Equal sets $U$ have identical behavior under every continuation.

Suppose two reachable sets differ and choose $x\in U\setminus V$, interchanging the sets if necessary. One clause of the prefix for $U$ forbids a face $F$ containing $x$. Append the $2^k-1$ other patterns on the very same $k$ variables. Their faces partition the complement of $F$. The continuation from $U$ is unsatisfiable, and the continuation from $V$ retains $x$. For the empty prefix and a single clause, fewer than $2^k-1$ further clauses leave both satisfiable by the union bound on the forbidden volumes. Thus the worst shortest distinguishing suffix is exactly $2^k-1$ for every $v\ge k\ge1$. For example at $v=4$ begin with $(x_1\vee x_2\vee x_3)$ versus the empty formula. Append its other seven sign patterns on the first three variables. The latter stream retains precisely the two assignments with these three bits zero.

This proves minimality of the prefix automaton for all deterministic one-pass transition rules. Each reachable set must be separately represented, and storing its identity suffices with an unrestricted table. Since the count equals the known number $G_3(v)$ of 3-SAT functions, Ilinca and Kahn's theorem gives $\log_2 G_3(v)=\binom v3+v+o(1)$ before rounding to whole bits. [Ilinca and Kahn](https://arxiv.org/abs/1005.2861)

## Enumeration by prefix length and suffix length

At $v=3$ the eight clauses forbid individual assignments. At $v=4$ each of the $8\binom43=32$ clauses forbids one distinct edge of the four-dimensional cube. The reachable sets are precisely the empty set and all vertex sets whose induced subgraph has no isolated vertex. Indeed each vertex is then covered by at least one internal edge.

| Minimum number of clauses in a prefix | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Three-variable states | 1 | 8 | 28 | 56 | 70 | 56 | 28 | 8 | 1 |
| Four-variable states | 1 | 32 | 472 | 3,392 | 11,204 | 15,184 | 9,568 | 2,928 | 365 |

The four-variable lower bound of 16 state bits already holds for streams of exactly 15 clauses, with the total length and the current position supplied for free. Each of the 43,145 nonempty forbidden sets is reachable after exactly eight clauses by repeating an existing clause as needed. Every pair is distinguishable by an exactly seven-clause suffix. Thus the input-length convention cannot merge any of these states at that cut.

The audit computes this histogram by breadth-first union of clauses. Independently, for each attainable $U$ in the four-cube its shortest prefix is a minimum edge cover of the induced graph. Its size is $|U|-\nu(U)$, where $\nu$ is maximum matching size. A maximum matching extends to such a cover by attaching one edge at each unmatched vertex. Conversely a minimal edge cover is a disjoint union of stars, and one edge from each star is a matching. The script computes $\nu$ by removing a vertex and either leaving it unmatched or pairing it with one of its available neighbors.

| Maximum number of clauses in a distinguishing suffix | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Three-variable equivalence classes | 2 | 10 | 38 | 94 | 164 | 220 | 248 | 256 |
| Four-variable equivalence classes | 2 | 50 | 866 | 6,866 | 24,666 | 38,874 | 42,938 | 43,146 |

For this table the initial partition uses only the current verdict. Each refinement records the previous class and the previous class after *every labeled clause*. Induction gives exactly the behavior on all suffixes up to the stated length. Signed variable permutations reduce the four-variable search to 253 orbits when the question is invariant under simultaneous relabeling. States related by a permutation can still be distinguished by labeled clauses, as the suffix table records.

## Adding a variable by testing two old slices

Let $K_j(U)$ denote the union of all codimension-$j$ coordinate faces contained in $U$ on the old $v$ variables. For $v\ge k\ge2$ a reachable forbidden set on $v+1$ variables is represented by two slices $U,V$, each reachable at width $k$ on $v$ variables. A clause involving the fresh variable restricts to a width-$(k-1)$ forbidden face in one slice only. Such an old face can itself be split into two width-$k$ faces, proving the claimed reachability of the slices. A clause omitting the fresh variable contributes the same face to both. The exact compatibility test is
$$
       (U\setminus K_{k-1}(U))\cup(V\setminus K_{k-1}(V))
                    \ \subseteq\ K_k(U\cap V).
$$
Necessity follows since every uncovered point on the left must belong to a shared clause. Conversely include all shared width-$k$ faces inside the common intersection, then include all available width-$(k-1)$ faces independently on each side with the corresponding fresh literal. These choices cover both desired slices exactly. In particular $G_k(v+1)\ge G_{k-1}(v)^2$, and the right hand side counts exactly the functions with a representation in which every clause uses the fresh variable.

Fixing one representative $U$ and ranging over all labeled $V$ counts all ordered pairs after multiplication by the orbit size of $U$. This uses $253\times43{,}146=10{,}915{,}938$ tests for $v=4$ and reproduces the known five-variable total. Of these states, $4{,}170^2=17{,}388{,}900$ admit a representation using the fresh variable in every clause, and 103,121,232 require some shared clause. The most frequent forbidden-set size is 20 out of 32 assignments, with 19,745,096 states. There are 4,438,306 states forbidding exactly half of the assignments. The executable prints the complete weight distribution. At one dimension lower the same slice computation agrees with direct enumeration for each weight.

## Failure of the one-pass inference on an unrestricted RAM

Consider the subfamily consisting of an arbitrary subset of the all-positive clauses, followed by a query suffix of seven clauses. Each subset has a different prefix function. For a target triple $S$, the seven other patterns on $S$ leave exactly the assignments zero on $S$. If its all-positive clause is present, the result is unsatisfiable. If it is absent, the assignment zero exactly on $S$ and one elsewhere survives every prefix clause. A one-pass reader before the query therefore needs $\binom v3$ bits of total state even for these special prefixes.

On the same family a two-pass reader can learn the target variable names from the final seven clauses on its first pass, then scan the prefix looking only for that triple. With a marked prefix boundary or the promised final-seven layout, $O(\log v)$ bits store the target and a constant-size clause buffer, and the work is linear in the encoded input length. Random access also allows the target to be read before the prefix scan in a fixed-width layout. The separating continuations prove a prefix information requirement, while a superlinear RAM lower bound would additionally have to charge access after the continuation becomes known.
