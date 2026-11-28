# Model density bounds the minimum transversal of the ternary clauses

Let $F$ be an ordinary width-at-most-three CNF file of $N$ physical bits. Remove tautologies and repeated literals and let $\tau(F)$ be the fewest variables that meet every remaining ternary clause. A deterministic logarithmic-word RAM with unrestricted workspace can exploit the model density of a neighboring formula $E$, even on unsatisfiable inputs $F$. It receives only $F$.

Suppose every clause of $F$ except at most $r$ occurs in $E$, and that a fraction $\mu>0$ of assignments satisfy $E$. Simplifying clauses consistently suffices. Fractions use the union of the variable sets, with unused variables unrestricted. Then
$$
\tau(F)\le r+\log_{8/7}(1/\mu).
$$
This bound on the minimum transversal is sharp even with $r=0$. The denominator $\log(8/7)$ comes from a whole ternary clause. Replacing the minimum transversal by three times a maximal disjoint packing would lose a factor of three in the exponent.

Write $\gamma=\log_2(8/7)\simeq 0.192645$. There is one globally correct ordinary SAT solver with the following three guarantees. For each $h=1,2,3$, each fixed edit bound $r$, and each fixed $c>0$, it takes $O(N^h)$ steps whenever
$$
\mu\ \ge\ c\big((N+1)^{h-1}\log_2(N+2)\big)^{-\gamma}.
$$
The linear guarantee includes model densities tending to zero as $(\log N)^{-\gamma}$. These are sufficient thresholds for this solver. We do not establish computational optimality for any of the thresholds.

## The density inequality

Consider a finite signed family of clauses with distinct variables in each clause and width at most $d$. Let $\tau$ be its minimum transversal size. Its model fraction satisfies
$$
\Pr[\mathrm{all\ clauses\ true}]\ \le\ (1-2^{-d})^\tau .
$$
For the application to $F$, apply this statement just to its ternary clauses shared with $E$. Their satisfiers include every model of $E$. Add one arbitrary variable from each missing ternary to a transversal of the shared clauses.

First align all occurrences of each variable to the negative polarity. Fix the other variables. If they already falsify a clause omitting this variable, both model counts in the fiber are zero. Otherwise the unsatisfied parts of clauses containing it may demand its positive value, its negative value, both or neither. Alignment leaves two available values in the last case and one when just one polarity was demanded. A double demand changes from zero available values to one. Repeating variable by variable preserves the supports and only increases the model fraction.

For all-negative clauses a model is an independent set in the support hypergraph, with value one denoting membership. Put $q=1-2^{-d}$. Induct on the number of remaining variables. An empty family has transversal zero. If an empty edge arises the model fraction is zero. Otherwise expose the bits of any edge in a fixed order up to and including the first zero. An all-ones edge fails. In each surviving branch just one exposed variable is zero. Delete its incident edges and remove the exposed ones from every remaining edge. Any transversal of the residual, together with the exposed zero, hits every original edge. The residual therefore has transversal number at least $\tau-1$. Its remaining unexposed variables are uniform independent bits. Induction bounds the conditional acceptance probability of every surviving branch by $q^{\tau-1}$. The branches have total mass $1-2^{-|e|}\le q$. Multiplication proves the result. Disjoint width-$d$ edges have transversal number equal to their count and attain equality.

The earlier [one-edit analysis](affine-insertion-at-a-clause-of-an-ordinary-3cnf.md) bounded the number of disjoint ternaries. Bonato, Brown, Mitsche and Prałat give an independence-density bound in terms of the matching number. Their parameter can be smaller than the minimum transversal. Akmal and Williams give linear-time algorithms comparing the model fraction of one bounded-width CNF to a fixed rational threshold. Here the accepted-model fraction concerns a potentially different file and may depend on the encoded length. Priority of the sharp transversal inequality is unestablished. [Bonato et al.](https://arxiv.org/abs/1308.2837) · [Akmal and Williams](https://arxiv.org/abs/2107.02748)

## Finding the transversal

Intern decimal identifiers in a digit trie and assign dense indices in order of first appearance. Sort at most three signed indices inside each occurrence, discard tautologies and use a fixed number of stable counting-sort passes to group equal clauses. Each pass costs linear time in the occurrence count plus the number of indices. All preprocessing takes $O(N)$ word steps. The number $m$ of distinct surviving clauses is $O(1+N/\log(N+2))$. Indeed, their distinct normalized strings over a fixed alphabet have total length $O(N)$, so $m\log(m+2)=O(N)$. If $m\le\sqrt N$ the stated bound is immediate, and otherwise $\log m\ge\frac12\log N$. The number of relevant variables is at most $3m$. [Physical clause-count argument](sat-time-from-model-counts-of-clause-prefixes.md)

Try transversal budgets $j=0,1,\ldots$ in increasing order. A small deterministic reduction keeps the search cost separate from the size of the file. Put $B_s=(j+1)^{3-s}$ for $s=0,1,2,3$. Keep a new ternary support unless some subset $S$ of it already has $B_{|S|}$ retained supersets. This caps all subset counts and retains at most $(j+1)^3$ edges, by the cap for the empty set. Suppose a set $T$ of at most $j$ vertices hits the retained family. When a support is skipped because of a proper subset $S$, a $T$ avoiding $S$ could hit at most $j B_{|S|+1}<B_{|S|}$ of those supersets. Hence $T$ meets $S$. The case of a skipped full support is a duplicate. Every such $T$ hits all original ternaries, so a cover found on the retained kernel lifts without change. Simple scans of this small retained family suffice to check the eight subset counts of a new support, in $O(m(j+1)^3)$ time per budget. This is the bounded-superset hitting-set kernel of Fafianie and Kratsch. Faster linear-time implementations also exist. [Fafianie and Kratsch](https://arxiv.org/abs/1504.08235) · [van Bevern and Smirnov](https://arxiv.org/abs/2003.04578)

For completeness a simple branching routine on the kernel suffices for all three exponents. Delete duplicates. When an edge is disjoint from every other edge, choose any one of its variables and remove that edge. Otherwise choose two intersecting triples. If the intersection is a single variable, either choose that variable or hit both remaining disjoint pairs. There are one branch of cost one and four branches of cost two. If the intersection has size two, choose either common variable or both private variables. There are two branches of cost one and one of cost two. Each choice removes every hit triple, and every possible solution is covered by at least one branch. Thus the cost per search is $\operatorname{poly}(j+1)\rho^j$, for $\rho=(1+\sqrt{17})/2<\sqrt8$. Branch order does not affect the bound. Crucially the returned transversal is a set of original variables, so it remains available for the SAT step.

At the first successful budget $\tau$, enumerate its $2^\tau$ truth assignments. Every residual is a 2-CNF on at most $3m$ variables and $m$ clauses. Deterministic strongly connected components solve each one in $O(m+1)$ word operations. Enumeration can use depth-first search and one mutable assignment. This use of a variable set to reduce SAT to a tractable class is a strong backdoor to 2-SAT. [Aspvall, Plass and Tarjan](https://collaborate.princeton.edu/en/publications/a-linear-time-algorithm-for-testing-the-truth-of-certain-quantifi/) · [Williams, Gomes and Selman](https://ijcai.org/proceedings/2003/167)

The solver can stop trying budgets at $3\lceil\log_2(N+2)\rceil$ and then run ordinary exhaustive SAT. It can also dispatch arbitrary-width files to the general fallback. On a successful budget within this range the elapsed time is
$$
O\big(N+(m+1)(\tau+1)^4+\operatorname{poly}(\tau+1)\rho^\tau+(m+1)2^\tau\big).
$$
For the stated density threshold, $\tau\le (h-1)\log_2(N+1)+\log_2\log_2(N+2)+O(1)$. At $h=1$, kernel scans fit in the $O(N)$ preprocessing bound because $(\log\log N)^4=O(\log N)$, and the search cost is polylogarithmic. For $h=2,3$ the scans cost $O(N\operatorname{polylog} N)$, and $\rho<\sqrt8$ implies $(h-1)\log_2\rho<h$. The final $2^\tau$ SCC evaluations multiply the compressed word count $O(1+N/\log N)$, leaving $O(N^h)$ in all three cases. Additive constants depending on $r,c$ affect only the time constant and the finitely many lengths before the budget cutoff is sufficient.

## Verification

The [core Lean proof](../lean/TernaryDensityTransversal.lean) verifies that polarity alignment cannot shrink a fiber, that a transversal of each actual residual lifts with one extra vertex, and that integer mass surviving $k$ first-zero rounds on a rank-three support family needing $k$ vertices is at most $7^k$ out of $8^k$. The calculation uses fresh fair blocks of three bits for the exposure and discards unused bits after a first zero. Its identification with draws of fresh unexposed variables and the RAM running times are mathematical arguments above. The [finite audit](../audits/ternary_density_transversal.py) independently counts full models of signed clauses and all monotone ternary hypergraphs on six vertices. It checks kernel preservation on all hypergraphs on five vertices for candidate sets of up to three variables.
