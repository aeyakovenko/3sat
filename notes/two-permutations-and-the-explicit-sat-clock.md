# Two permutations suffice to express the unrestricted SAT clock

Given two permutations `P,Q` of a common set of size `q`, ask whether there is a subset `S` such that
$$
                   S\ \dot\cup\ P(S)\ \dot\cup\ Q(S)=[q].
$$
The unions must be disjoint, including when two images of a selected point coincide. Store the two arrays explicitly in fixed-width binary fields of $\lceil\log_2(q+1)\rceil$ bits. This decision problem and explicit ASCII DIMACS 3-SAT reduce to one another in deterministic $O(N)$ logarithmic-word RAM steps with $O(N)$ output bits. Hence excluding $O(N)$, $O(N^2)$ or $O(N^3)$ for the permutation problem would give the corresponding unrestricted SAT result. The hard direction of any such exclusion remains open.

The reduction can supply a disjoint packing missing just three points, a signed solution with one negative coordinate, and a solution on a double cover. All three promises hold simultaneously for every source formula. The optimum number of disjoint triples on the resulting instance is either $q/3-1$ or $q/3$, according to the source verdict.

The incidence version is restricted exact cover by indexed triples. Different indices may have identical neighborhoods. Its NP-completeness is classical. The construction below supplies the two permutations directly, bounds the cost on encoded bits even for repeated short DIMACS clauses, and tracks the multiplicity of solutions. [Gonzalez, Appendix A on restricted exact cover](https://www.cs.columbia.edu/~verma/classes/uml/ref/clustering_minimize_intercluster_distance_gonzalez.pdf) · [Moore and Robson on cubic monotone one-in-three SAT](https://arxiv.org/abs/math/0003039) · [Döcker et al., §3.2, parsimonious reductions to regular instances](https://arxiv.org/html/2611.31145v1#S3.SS2) · [Cole, Ost and Schirra on bipartite edge coloring](https://cs.nyu.edu/media/publications/TR1999-792.pdf)

In particular, regular positive exact-one instances plus linear-time cubic bipartite edge coloring already give the unrestricted permutation formulation. The direct coloring here lets us follow a specified signed assignment through the regularization. Priority for the bounded-defect promise is unestablished.

## From a formula to positive exact-one

Write $E(a,b,c)$ for $a+b+c=1$ over the integers on Boolean arguments. Intern and normalize the variable names and remove duplicate ordered clauses. Retain tautologies if tracking assignments on all occurring names. For each short nonempty clause, repeat its last literal to obtain three positions. Use $E(o,o,t)$ to force $o=0,t=1$, and $E(v,\bar v,o)$ to create a unique complement for each variable whose complement is used. For each clause with truth bits $b_1,b_2,b_3$ introduce selector bits with $E(s_1,s_2,s_3)$. Require that $s_j$ implies $b_j$ and also implies $1-b_i$ for $i<j$. A requirement $s\Rightarrow b$ takes one $E(s,1-b,u)$ with fresh slack $u$. The slack is unique on the three allowed pairs. Hence each satisfying assignment on the occurring original names has exactly one extension, choosing its first true literal in every clause. Empty clauses give an immediate no instance. A clause-free input with no occurring variables may use the pin by itself. This decision convention also covers files whose headers declare many unused names.

Let $m_0$ be the number of positive exact-one records after this step. If the source has $f$ distinct retained clauses, then $m_0=O(1+f)$. The distinct normalized clause strings already require $\Omega(f\log(f+1))$ bits in total by counting fixed-alphabet strings. Their total length is $O(N)$ before and after short-clause padding. Fixed-alphabet tries for names and clause strings, followed by consecutive indices, perform the normalization and deduplication in $O(N)$ steps. All subsequent record counts are linear in $m_0$.

## A cubic bipartite incidence graph with an explicit edge coloring

Copy every positive clause three times, rotating its slots through $0,1,2$. Write $m=3m_0$ for this number of clauses, counting copies as separate records. Each original occurrence of a variable produces one occurrence at each slot. For each variable arrange its resulting occurrences in a cyclic order with the slot increasing by one modulo three. Interleave three buckets by slot to do this in linear time. Write $j(i)$ for the successor of occurrence $i$ and $s_i$ for its slot. Introduce four bits $x_i,a_i,b_i,w_i$ for each occurrence.

* Include the rotated clauses on their occurrence copies $x_i$. Include two copies of each of these clauses on the corresponding $w_i$.
* For each occurrence $i$ include the three additional clauses
$$
 E(x_i,a_i,b_i),\qquad E(x_{j(i)},a_i,b_i),\qquad E(w_i,a_i,b_i).
$$

The three extra constraints have the same last two arguments, hence $x_i=x_{j(i)}=w_i$. This reconstructs a single bit for each source variable. Given these bits, there is one choice of $(a_i,b_i)$ when $x_i=1$ and two when $x_i=0$. Every satisfying assignment has precisely two false occurrences per rotated clause. Thus the new formula has exactly $2^{2m}$ times the number of solutions of the positive formula. The extra copies on $w_i$ maintain the degree without changing feasibility.

There are $q=12m$ variables and $q$ clauses, each of degree three. Each clause has three distinct variables, including when the source repeated a variable. Color incidence edges in $\mathbb Z/3$ as follows.

| Clause record | Color of incidence at original slot $s_i$ |
| --- | --- |
| Rotated clause on $x_i$ | $s_i$ |
| First and second copy on $w_i$ | $s_i$ and $s_i+1$, respectively |

In the three extra records for $i$, the colors of their first entries, in order, are $s_i+1,s_i,s_i+2$. In each record add one to that first color for $a_i$ and two for $b_i$. The colors are distinct around every clause. The colors around $x_i$ are $s_i,s_i+1,s_i-1$ because its other occurrence is in the second record of its predecessor. The colors around $w_i$ are $s_i,s_i+1,s_i+2$. Each $a_i$ or $b_i$ sees all colors because its triple of first-entry colors already does. Thus each color gives a bijection $f_j$ from variables to clauses.

Use the color-zero bijection to name the variables by clauses and emit $P=f_1 f_0^{-1}$, $Q=f_2 f_0^{-1}$. A selected variable covers its three incident clauses. Exact coverage is precisely the displayed partition. Dense indexing and permutation construction take $O(q)$ word steps after input processing. The two arrays use $O(q\log(q+1))=O(N)$ bits. This builds the coloring as part of the reduction.

## A supplied packing missing only three points

First construct an always satisfiable formula with a distinguished bit. Add a fresh $g$. For each original padded clause $a\lor b\lor c$, enforce $h\leftrightarrow(g\land\neg a)$ on a fresh bit and add $\neg h\lor b\lor c$. The equivalence uses $(\neg h\lor g)$, $(\neg h\lor\neg a)$, and $(h\lor\neg g\lor a)$. An original empty clause contributes $\neg g$. Deduplicate originals before introducing their guards. With $g=0$, the all-zero assignment to original and auxiliary variables satisfies the guards. With $g=1$ the satisfying assignments correspond bijectively to those of the original formula. Include $E(g,\bar g,o)$ in the positive compiler even on an empty formula. In the cubic graph designate an $x_i$ for an occurrence of $\bar g$ as $v$. The compiler produces a known Boolean cover with $v=1$. There exists a Boolean cover with $v=0$ exactly when the source is satisfiable. Recover a known cover at $v=1$ by taking the first true selector and any one allowed pair $(a_i,b_i)$ at every occurrence.

Use a fixed separate component with six columns $D,Z_0,Z_1,H_0,H_1,H_2$ and six rows. For $i=0,1,2$ its row $i$ contains $D$ and the two $H$'s other than $H_i$. Row $i+3$ contains $Z_0,Z_1,H_i$. Each column occurs three times. Its only exact covers are $\{D,Z_0\}$ and $\{D,Z_1\}$. Each $H_i$ meets every other column somewhere, and an exact cover requires two disjoint columns. A signed solution is $D=-1$, $H_0=H_1=H_2=1$, $Z_0=Z_1=0$. Fix a proper three-edge-coloring of this constant-size cubic bipartite component; one exists by the bipartite matching theorem or can be found by exhaustive search.

Swap the row endpoints of the color-one edges at $v$ and at $H_0$ across the two components. This preserves all degrees and the coloring, changes one permutation by a transposition and keeps the identity matching. In a Boolean cover of the switched graph, summing its six gadget rows gives
$$
                  3\sum_{i\ \mathrm{in\ gadget}}x_i+x_v-x_{H_0}=6.
$$
Therefore $x_v=x_{H_0}$, since each is a bit. Undoing the switch then preserves every row. The small component forces $x_{H_0}=0$, hence the guarded input has a cover with $v=0$. Conversely such a cover joins either small-component cover across the switch. This proves the decision equivalence on the switched instances. The swap joins disjoint components at its two new incidences, so every physical row still has three distinct entries. Indexed columns may have identical neighborhoods.

Two different explicit assignments show how close every output is to exact coverage.

* Start with the known Boolean cover of the guarded graph ($v=1$) and one Boolean cover of the small component ($H_0=0$). After the swap one row is empty and one has two selected columns. Every other row is covered exactly once. The number of selected columns is still $q/3$, where $q$ now includes the six added rows. Remove either selected column on the doubly covered row. Its three rows are distinct, and its two other rows were singly covered. The result is a packing of $q/3-1$ disjoint triples missing exactly three points.
* Instead use the signed solution of the small component with $H_0=1$. Both exchanged bits are now one, so the same assignment $y$ satisfies $Ay=\mathbf1$ after the swap. Here column $i$ of $A$ has ones at $i,P(i),Q(i)$. Precisely one entry of $y$ is negative, equal to $-1$ at $D$; all others are bits. The set $\{i:y_i=1\}$ covers every point once except the three incident to $D$, which it covers twice. Its cardinality is $q/3+1$. A signed solution with zero negatives would itself decide the instance positively.

All witnesses can be emitted in linear encoded size and time even when the original SAT verdict is unknown. To get an explicit solvable double cover set $z=\mathbf1-y$. Its entries are $0,1,2$ and $Az=2\mathbf1$. Select $z_i$ copies over each $i$. In each target fiber, after reserving its identity contributions, partition the remaining positions into the prescribed numbers of images from $P$ and $Q$. For each strip independently, match its selected source copies to the allocated target positions and the unselected copies to the remaining positions for that strip. This gives the required two permutations upstairs. The same proof works at any sheet degree with the corresponding histogram; $\mathbf1$ works at degree three. Disjoint unions show that every output instance admits a solvable cover of every degree $d\ge2$, including when the base is infeasible. The lifts may even use only cyclic shifts of the sheets. Write $d=2a+3b$ with $a,b\ge0$, and use the degree-$d$ histogram $z=a(\mathbf1-y)+b\mathbf1$. Select sheets $0,\ldots,z_i-1$ at $i$. In the target fiber $u$, shift the $P$-strip by $z_u$ and the $Q$-strip by $z_u+z_{P^{-1}(u)}$ modulo $d$. The three selected intervals fill that fiber consecutively. The constructed lift may have multiple connected components. Supplying the double cover and its assignment takes $O(N)$ time and bits.

## The remaining algebraic search

A Boolean solution $x$ yields an integer kernel vector $x-y$ that increases $D$ by one or two, increases other zero entries by at most one and decreases one entries by at most one. Conversely any kernel vector in those intervals repairs $y$. One **conformally indecomposable** integer kernel vector suffices. Decompose $x-y$ into nonzero kernel summands of the same coordinatewise sign with no cancellations, splitting until further decomposition is impossible. This terminates by integer $\ell_1$ norm. Some summand increases $D$; that summand alone respects every interval and repairs the solution. The proof gives no size or time bound for finding it.

There is also a packing interpretation. Given a perfect cover, discard triples shared with the supplied packing, and connect the remaining old and new triples when they share a point. In each connected component the number of previously uncovered points equals three times the excess of new triples over old triples. Exactly one component therefore contains all three previously uncovered points. Replacing the old triples just in this component augments the packing to a perfect cover. Determining whether such a replacement exists still carries the unrestricted SAT clock. A packing missing zero points already certifies a yes instance.

## Back to SAT

Compute the inverses of the two arrays. At each $u$ require $E(x_u,x_{P^{-1}(u)},x_{Q^{-1}(u)})$. Use one positive clause and three pairwise negative clauses with the corresponding occurrences. This enforces integer sum one even for repetitions. Simplify duplicates and tautologies inside the ordinary Boolean clauses. To emit proper ternary DIMACS, pin three distinct padding variables to zero by the seven proper clauses excluding the other assignments, and fill short clauses with distinct pins. Ensure any free named bit still occurs if the encoding requires density. These steps take $O(q\log(q+1))$ bits and time. Every exact cover gives one Boolean assignment to the $x$ bits and conversely. Permutation validity can be checked while building the inverses. Fixed yes/no outputs handle degenerate records.

The [compiler audit](../audits/two_permutation_sat_audit.py) tested 781 positive exact-one inputs, including all ordered inputs of up to two clauses over three names. The [signed and packing audit](../audits/signed_permutation_cover_audit.py) checked 256 guarded CNFs and 1,024 explicit cyclic lifts of degrees two through five. [Lean](../lean/OneNegativePermutationPatch.lean) checks both the six-row gadget and its effect after the incidence swap with an arbitrary external system. The encoded lengths and the full two-way algorithmic reductions are manuscript arguments. The [algebraic lift](logarithmic-neighborhoods-in-opposite-permutation-covers.md) gives connected instances of both verdicts in every stage of a single infinite construction and a linear-time test that recognizes them.
