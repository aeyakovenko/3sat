# Every affirmative run must inspect almost every complete 3-SAT record

**Local completion theorem.** Fix one signed clause on every triple of \(v\) Boolean variables. Choose **any 63 different triples**. One can replace their signs so that the induced formula on their at most 189 variables is already unsatisfiable. All other signs stay fixed. The choice can be computed from the clauses on those 189 variables alone.

Consequently every positive certificate in the model that queries an entire clause’s signs must query at least \(\binom v3-62\) records, on **every** satisfiable file. On physical sign slots in ordinary DIMACS this implies \(\Omega(N/\log N)\) native steps on every such positive input, including every accepting path of a sound nondeterministic solver. Every bounded-error randomized solver incurs the same order of expected time on each positive file. The deterministic scan upper bound on this family matches the order. [Word-RAM upper bound, encoding and prior complete-CSP work](complete-csp-in-linear-dimacs-time.md)

## Completing an arbitrarily prescribed set of holes

Let \(T\) consist of the 63 chosen triples, with union \(U\). A row is a Boolean assignment on \(U\) that satisfies every fixed clause whose variables all lie in \(U\). We may calculate these rows directly by exhaustive enumeration on a constant-size set. We need a bound much smaller than \(2^{189}\).

By the strong form of the Sauer inequality, the number of rows is at most the number of coordinate sets they shatter. Every triple in a shattered set must belong to \(T\), since any fixed clause on it would exclude one of the projected bit patterns. Thus every shattered set of size \(s\ge3\) is an \(s\)-vertex clique in the 3-uniform hypergraph \(T\). It has \(s\le8\) since \(\binom93=84>63\). Sets of size at most two contribute at most \(1+189+\binom{189}2=17{,}956\). [Sauer, 1972](https://doi.org/10.1016/0097-3165(72)90019-2) · [Strong shattering inequality in Lean](DyadicCspProjection.lean)

For \(3\le s\le8\), put \(d=\lceil s/3\rceil\). A clique on \(s\) specified vertices has exactly
\[
 C(s,d)=\sum_{i=0}^s(-1)^i\binom si\binom{\binom{s-i}3}{d}
\]
choices of \(d\) different triples whose union is all \(s\) vertices, by inclusion-exclusion. An unordered \(d\)-tuple of distinct members of \(T\) has just one union. Thus at most \(\lfloor\binom{63}d/C(s,d)\rfloor\) different vertex sets of size \(s\) can be cliques.

| \(s\) | \(d\) | Covers on a specified clique | Upper bound on its number of vertex sets |
|---:|---:|---:|---:|
| 3 | 1 | 1 | 63 |
| 4 | 2 | 6 | 325 |
| 5 | 2 | 15 | 130 |
| 6 | 2 | 10 | 195 |
| 7 | 3 | 945 | 42 |
| 8 | 3 | 840 | 47 |

The total bound on the candidate rows is **18,758**. For each still unsigned triple, choose the forbidden pattern occurring most often among the surviving rows. With \(m\) rows, the next count is at most \(\lfloor7m/8\rfloor\). Iterating this integer bound 63 times from 18,758 leaves zero. In fact the last seven upper bounds before zero are \(7,6,5,4,3,2,1\). Every original restriction on \(U\) is honored, so the completed formula on \(U\) is unsatisfiable. This also works for any larger number of available holes by using just 63 of them. The number 63 is a proved sufficient value. Its optimality is open here. [Exact arithmetic, physical layouts and finite audit](unseen_sign_completion_audit.py) · [Lean proof of greedy elimination for arbitrary actual projection functions](upstream-checks/AdversarialSignCompletion.lean)

## An exact size successor for positive certificate complexity

Let \(h(v)\) be the largest number of whole triples one can leave unsigned while making **every** signing completion satisfiable by fixing the other triples appropriately. The least certificate size over all satisfiable signings at \(v\) equals \(\binom v3-h(v)\). Given such an example on \(v\) variables, add one fresh variable as false and give every new triple a clause containing its negation. Every old model extends, so \(h(v+1)\ge h(v)\).

Conversely suppose an all-satisfiable partial signing leaves \(r\) holes. Restrict to the union of their at most \(3r\) vertices, discarding the other clauses. All completions of that smaller table are still satisfiable. The local completion theorem gives \(r\le62\), so every attainable value already occurs on at most 186 vertices. Hence there is a fixed integer \(h_*\) such that for **every \(v\ge186\)**
\[
  \min_{F\ {\rm SAT}} C_1(F)=\binom v3-h_* .
\]
At each such successor the minimum certificate size increases by exactly \(\binom v2\). Also \(10\le h_*\le62\). To witness the lower number, leave all ten triples on five variables unsigned. Every signing on them is satisfiable; extend to further variables via negative fresh literals. The five-variable base was proved previously, including in the September 2026 resolution of the GraphSAT table. [Korea Superintelligence Labs, Theorem 1.3](https://ideosphere.ai/papers/graphsat-uniform-v1.pdf) · [Independent five-variable certificate](CompleteClauseSeed.lean)

The argument generalizes to any fixed \(k\ge2\). Start with \(r\) designated \(k\)-sets on at most \(kr\) vertices. Every shattered set of size at least \(k\) is a clique and has size \(s=O_k(1+r^{1/k})\), since \(\binom sk\le r\). There are at most \(\exp(O_k((1+r^{1/k})\log(r+2)))\) such candidate projections including the contributions from smaller sets, by summing \(\binom{kr}{j}\) up to this size. The proportion surviving \(r\) greedy choices is at most \((1-2^{-k})^r\), which forces an empty set for all sufficiently large \(r=r(k)\). Therefore the least positive certificate equals \(\binom vk-h_k\) for all sufficiently large \(v\), with an absolute \(h_k\) for that width. The finite cover count yields sufficient values \(16,63,262,864\) at widths two through five, respectively.

The stabilization constant has exponential rate exactly two as width grows.
\[
                    \lim_{k\to\infty}h_k^{1/k}=2 .
\]
For an upper bound take \(r=100 k^2 2^k\). From \(\binom sk\ge(s/k)^k\) a clique has \(s\le k r^{1/k}\le 3k\) for all sufficiently large \(k\). Including smaller sets, the number of projected patterns is at most \((kr+1)^{3k}\le 2^{6k^2}\) eventually. Independent uniform signs leave at most \(2^{6k^2}\exp(-100k^2)<1\) patterns in expectation, so \(h_k<r\). For a lower bound take a core of \(k-1\) variables and one distinct fresh leaf per free support, each consisting of the core plus that leaf. Fix every remaining clause to be all-negative, so any assignment of weight at most \(k-1\) satisfies all fixed clauses. Under an arbitrary completion, group the free clauses by the one forbidden pattern \(b\) on the core. If their total number is less than
\[
      \sum_{b\in\{0,1\}^{k-1}}(k-|b|)=(k+1)2^{k-2},
\]
one bucket contains at most \(k-1-|b|\) clauses. Choose that core pattern. Give each leaf in its bucket the opposite of its forbidden value and set the other leaves to zero. The weight is at most \(k-1\), and all clauses are satisfied. Thus \((k+1)2^{k-2}-1\le h_k=O(k^2 2^k)\). Both bounds concern ordinary Boolean assignments.

For a fixed alphabet of size \(q\ge3\) with one forbidden tuple per present support, the maximum number of free supports is instead \(\Theta_{q,k}(v)\). For the lower bound leave a matching of \(\lfloor v/k\rfloor\) disjoint supports free and fix all other supports to forbid the tuple constantly two. Any signs on the matching admit a Boolean assignment by choosing its disjoint restrictions separately. For the upper bound on any arrangement of \(r\) free supports, a uniformly random completion leaves at most \(q^v(1-q^{-k})^r\) full assignments in expectation. All completions can remain positive only when \(r=O_{q,k}(v)\). The same alphabet change also affects single-constraint sensitivity. [Three-symbol pivotal example](a-third-symbol-allows-cubically-many-private-triples.md)

On the other verdict, querying an unsatisfiable subformula certifies UNSAT. Conversely, if the inspected clauses are satisfiable, sign all uninspected triples to allow that one assignment. Thus the negative certificate complexity in this table model is exactly the size of a smallest unsatisfiable subformula. At width three, an upper bound for every such negative certificate is \(O(v^{7/3}(\log v)^{2/3})\), while some require \(\Omega(v^2)\). These are query certificates with unrestricted computation to recognize their implications. [Fractional-cover and subformula upper bounds](private-clauses-in-complete-signed-triple-families.md) · [Quadratic necessary-clause construction](sharp-pivotal-growth-on-complete-clause-supports.md)

## Actual native runs, including randomization

For a concrete encoding use lexicographic triples on the names \(1,\ldots,v\). Within each literal reserve a sign byte, either minus or space. Put ordinary spaces **before** the sign byte to align the decimal names to their maximum width; the digit sequence begins immediately after the sign. Include the usual token delimiters, zero terminators and DIMACS header. These are standard ASCII DIMACS files with fixed physical offsets at fixed \(v\). Each row occupies \(\Theta(\log(v+2))\) bytes, independently of its signs. The file length is \(N=\Theta(v^3\log v)\) bits. An aligned or unaligned logarithmic native word intersects the sign slots of only a bounded number of rows.

On any accepting trace, if 63 rows have had none of their original sign bytes exposed, replace those signs by the local unsatisfiable completion. The same accepting trace is possible on the opposite verdict. Copying, overwriting, or guessing an unread value cannot distinguish the two runs. Thus deterministic or sound nondeterministic acceptance must expose at least one original sign byte on all but 62 rows. For each fixed finite roster, the same modification yields one common negative continuation of any collection of prefixes that has left 63 common rows untouched.

Fix any positive file and partition its rows into disjoint groups of 63, possibly leaving a remainder. For each group choose a negative file differing only inside that group. Couple a two-sided randomized solver on the two files using identical coins. Until it observes a changed original sign their traces agree. Error at most \(1/3\) on each file forces the probability of observing a change in that group on the positive file to be at least \(1/3\), since the acceptance probabilities differ by at least \(1/3\). Linearity of expectation gives at least \(\lfloor\binom v3/63\rfloor/3\) distinct groups touched in expectation on **each** positive file. Each word reaches only constantly many groups, giving the claimed native lower bound. The deterministic upper is of the same order even with unlimited workspace. Thus the exact certificate-size successor survives indefinitely on actual SAT clauses, while word time on this family grows only at the packed-scan rate.

The finite checker independently enumerates every small cover number used in the table and verifies local completions for 80 examples, including planted inputs and arbitrary initial signs. The combinatorial upper on the initial projection family and its physical RAM transfer are manuscript arguments. Priority for the prescribed-hole theorem and the eventual certificate formula has not been established.
