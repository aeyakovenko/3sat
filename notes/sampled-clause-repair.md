# Repairing a sampled 3-CNF with candidate assignments

**Research journal, 25 November 2026.** A candidate assignment can identify every clause it violates and still remove just one of cubically many possibilities for a single UNSAT verdict. The exact number of candidates required by a one-at-a-time repair rule is a graph parameter. The construction below also admits a direct linear-time algorithm in the number of clause records.

The comparison comes from minimum spanning forests. Karger, Klein and Tarjan show that if edges are sampled independently with probability $p$, the expected number of edges that survive their forest filter is at most $n/p$ on $n$ vertices. The cycle property justifies discarding all heavy edges at once. Khanna, Putterman and Song's deterministic MST preprint uses path maxima and counts histories to select schedules, ultimately obtaining a uniform linear-time algorithm from a comparison bound. Can sampling plus a small number of violations justify an analogous reduction for one SAT decision? [Karger, Klein and Tarjan, Lemma 1](https://www.cs.cmu.edu/~guyb/paralg/papers/KargerKleinTarjan95.pdf) · [Khanna, Putterman and Song, Theorem 1.1 and §3](https://eccc.weizmann.ac.il/report/2026/339/)

## A sample can have uniformly few violations

Fix a background $B$ and $m$ indexed clauses on $v$ Boolean variables, counting the background variables. Retain each indexed clause independently with probability $0<p<1$ and keep all of $B$. For every integer $t\ge1$ the following bound holds.

$$
\Pr[\text{some model of the sample violates at least }t\text{ full clauses}]
\ \le\ \min\{1,2^v(1-p)^t\}.
$$

A fixed assignment violating $s\ge t$ clauses survives only if all $s$ are omitted. Sum over at most $2^v$ assignments. For $0<\delta<1$, setting $t=\lceil (v\ln 2+\ln(1/\delta))/(-\ln(1-p))\rceil$ gives failure probability at most $\delta$, also for a witness chosen after seeing the sample. This elementary union bound counts violations of a selected witness. Replacing the witness can expose a different set of violations.

## Exact repair counts

Assume the full formula is unsatisfiable. From a subcollection $S$ of retained clauses, select a model of $B\land S$, adjoin **every** indexed clause it violates, and repeat until the retained formula is unsatisfiable. Charge one per model selected, with arbitrary computation and a complete SAT oracle available for making the selection.

Make a finite simple graph $G_S$. Its vertices are the initial models $a\models B\land S$. Put $D(a)=\{i:a\text{ violates clause }i\}$, which is disjoint from $S$ and nonempty. Join two distinct vertices exactly when their two sets $D$ intersect. If the selected model is $a$, a current model $b$ survives precisely when $D(b)\cap D(a)=\varnothing$. The step therefore deletes $a$ and its current neighbors. Subsequent steps operate on the induced graph of survivors.

**Theorem.** The possible completed one-at-a-time runs are exactly the orderings of the maximal independent sets of $G_S$. The minimum number of selections is its independent domination number and the maximum is its independence number.

Indeed, every selected vertex survives all earlier selections, so selected vertices are independent. Completion says that every unselected vertex neighbors a selected vertex. Conversely every ordering of a maximal independent set consists of feasible selections and its last deletion exhausts the graph. For an initially unsatisfiable sample there are zero selections and the graph is empty.

In a parallel round one may select up to $b$ distinct models of the same current formula before adjoining all their violations. A prescribed sequence of nonempty, disjoint batches $A_1,\ldots,A_k$ completes exactly when each has size at most $b$, there are no graph edges between different batches, and their union dominates $G_S$. Indeed, a batch deletes its closed neighborhood. Vertices in the same batch may be adjacent. These conditions give a direct test even when later choices depend on all earlier models or violations.

**Every finite simple graph occurs.** Force exactly one of $X_1,\ldots,X_h$ to be one. Use prefix flags $P_0=0$, $P_j\leftrightarrow(P_{j-1}\lor X_j)$, clauses $\neg P_{j-1}\lor\neg X_j$, and $P_h=1$. Each choice has a unique extension. For each graph edge $e=uv$ add the background gate $Y_e\leftrightarrow(X_u\lor X_v)$. Use the private unit clauses $\neg X_v$ and edge unit clauses $\neg Y_e$ as the indexed collection, initially omitted. The full formula is unsatisfiable. The model selecting $v$ violates its private clause and the edge clauses incident with $v$. Two different models share a violation exactly when the vertices are adjacent. OR equivalences use ordinary width-three clauses, and shorter clauses can repeat a literal. The construction uses $O(h+|E|)$ variables and clauses. Hence optimizing the selection count is NP-hard even for this explicitly presented family with the same terminal verdict on every graph. The complexity of minimum independent domination is classical. [Irving, *On approximating the minimum independent dominating set*](https://doi.org/10.1016/0020-0190(91)90188-N)

## Cubically many forced selections on one formula

Take three disjoint groups $X,Y,Z$ of $r\ge1$ selectors and apply the same linear-size exactly-one background to each. Include $m=r^3$ indexed clauses

$$
C_{ijk}=\neg X_i\lor\neg Y_j\lor\neg Z_k,\qquad 1\le i,j,k\le r .
$$

Every background model selects one triple and violates exactly its corresponding clause. Starting with any retained $S$, the graph of surviving models has $r^3-|S|$ vertices and no edges. Every successful repair requires exactly $r^3-|S|$ distinct models. With capacity $b\ge1$, its optimal round count is $\lceil(r^3-|S|)/b\rceil$. Under independent sampling the expected number of models needed is exactly $(1-p)r^3$. In particular, even a clairvoyant choice with no cost for finding a model cannot reduce the total. All these statements apply to the same unpinned formula.

Lee's construction already uses the complete three-partite family of triples, up to complementation of the selectors. His Claim 3 supplies a private witness for each triple, and his width-reduction construction gives genuinely minimally unsatisfiable 3-CNFs with cubically many clauses. Here the exactly-one background makes **every** surviving model expose one missing triple. We only require the indexed clauses to be individually necessary in the fixed background. [Lee, §3, Claim 3 and the construction following it](https://arxiv.org/pdf/0811.0427)

The single-verdict cost of this witness rule does not give a superlinear native-time bound. On the ordinary explicit layout with any list of $L$ blocking triples, $B$ can be extended precisely when some one of the $r^3$ keys is missing. A deterministic word RAM can check the background, validate that each blocker has one correctly signed selector per group, and mark the seen triples in a direct table. With $L\ge r^3$ this costs $O(r+L)$ word operations, including zeroing the table and counting distinct keys. When $L<r^3$, absence of a key follows from the count once the layout has been checked. For the full cubic example the explicit fixed-width encoding uses $N=\Theta(r^3\log(r+1))$ bits and this calculation takes $O(r^3)$ steps. An ordinary globally correct solver can dispatch to a complete SAT algorithm on a layout mismatch. Moreover, on the full unsatisfiable formula, changing the sign of any single blocking literal makes the private triple's model satisfy the entire formula. A deterministic solver must therefore inspect the words containing these signs on that actual rejecting run. Each word intersects only constantly many fixed-width blocker records, giving $\Omega(r^3)=\Omega(N/\log N)$ native steps on the family.

[Finite checks of the repair graph, parallel rounds and tripartite blockers](../audits/sampled_clause_repair_audit.py)
