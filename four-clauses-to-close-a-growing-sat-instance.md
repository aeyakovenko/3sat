# Four clauses suffice to close a growing 3-SAT instance

Start with one clause on three distinct variables. In each following *introduction*, put one fresh variable in a clause with two distinct older variables. After introducing all $n\ge3$ variables, append $k$ arbitrary clauses using old variables. Every clause has exactly three distinct variables, and every occurrence can take either sign. The smallest $k$ that can make the formula unsatisfiable is
$$
                    k_{\min}(n)=\max\{4,10-n\}.
$$
Thus four closing clauses first suffice at six variables and continue to suffice at every larger size.

## Why three closings always leave a model

Take a clause-minimal unsatisfiable core $H$ and write $g$ for the number of selected seed or introduction clauses, $q$ for its closing clauses. Its deficiency is its number of clauses minus its number of occurring variables. Tarsi's lemma gives deficiency at least one. If $g=0$ and $q\le3$, a uniformly random assignment violates at least one clause with probability at most $3/8$, so this case is impossible. If $g>0$, the earliest selected introduction or seed supplies three variables. Every later selected introduction supplies at least its own fresh variable. The core therefore uses at least $g+2$ variables and has deficiency at most $q-2$. This already excludes $q\le2$. [Kullmann, deficiency of minimally unsatisfiable clause-sets](https://eccc.weizmann.ac.il/report/2007/055/revision/1/download/)

At $q=3$ equality holds throughout. In the order inherited from the input, each selected introduction after the first adds **exactly one** variable to the union of the earlier selected clauses. The closing clauses add none. In particular, the variables in this whole core can grow from the first selected triple by repeatedly taking triples with two previously seen variables.

By Kullmann's deficiency-one structure theorem, the clauses of $H$ arise from leaves of a full binary tree with distinct variables at its internal nodes. Each leaf clause uses literals from its root-to-leaf path, possibly after literal deletions. Split the clauses at the two children of the root. The variable sets of the two sides meet in at most the root variable. Both sides have at least one clause, and every surviving clause has three distinct variables. A seed triple is on one side. As long as every seen variable is on that side, no clause of the other side contains two seen variables. Growth cannot reach the other side's private variables. This contradicts the spanning growth order just derived for $H$. [Kullmann, Theorem 6.16(ii) and the definition of a deficiency-one tree, pp. 60–64](https://eccc.weizmann.ac.il/report/2007/055/revision/1/download/)

Independently, each proper ternary clause excludes exactly an eighth of the assignment cube. Unsatisfiability thus requires at least eight clauses. There are $n-2+k$ clauses, which proves the other lower bound $k\ge10-n$.

## An eight-clause witness

In the rows below place the first clause of each row first, in the displayed order, then append the four second clauses. The first row is the seed and the next three introduce $d,e,f$.

| Seed or introduction | Closing clause |
|---|---|
| $a\lor b\lor c$ | $\neg a\lor b\lor c$ |
| $a\lor\neg b\lor d$ | $\neg a\lor\neg b\lor d$ |
| $b\lor\neg c\lor e$ | $b\lor\neg c\lor\neg e$ |
| $\neg b\lor\neg d\lor f$ | $\neg b\lor\neg d\lor\neg f$ |

Resolving each row's two clauses yields $b\lor c$, $\neg b\lor d$, $b\lor\neg c$, $\neg b\lor\neg d$. These force both $b$ and $\neg b$. In fact every assignment falsifies exactly one of the eight original clauses. For five variables identify $f=a$. For four additionally identify $e=a$. For three additionally identify $d=c$. All resulting clauses stay proper. In each instance designate the first $n-2$ displayed first clauses as the growth sequence and treat the remaining clauses as closings. For $n>6$, insert fresh introductions with parents $a,b$ before the four closing clauses. The original contradiction survives regardless of those extra variables.

Lean verifies the contradiction for every assignment, including under the variable identifications, the four finite layouts and counts, and the closure invariant for a split with at most one common variable. The structural classification of deficiency-one cores is an external theorem. This threshold identifies the first possible contradiction in the specified growth rule. The construction itself admits an immediate fixed-size check and supplies no unrestricted running-time lower bound. Priority for this ordered formulation has not been established. [Lean verification](GrowingSatClosures.lean)

## When arbitrary many closing clauses are permitted

Every proper 3-SAT instance can occur as the closing portion with a growth prefix that imposes no restriction on its source variables. On a densely normalized source with names $x_1,\ldots,x_v$, seed with three fresh names $u,v',z_0$. Take $x_0=u$. For $i=1,\ldots,v$ introduce $x_i$ with $(x_i\lor z_{i-1}\lor x_{i-1})$, then $z_i$ with $(z_i\lor x_i\lor z_{i-1})$. Finally append the original clauses verbatim. All $z$ bits set to one satisfy the prefix for every source assignment. The prefix itself has maximum occurrence count four, since $z_i$ appears in its introduction and at most two following clauses (with the seed counted when $i=0$). Source clauses can of course add further occurrences. There are $2v+1$ prefix clauses. Dense normalization gives $v\log(v+1)=O(N+1)$ for original encoded length $N$, so constructing the prefix and writing its decimal names fit linear time and length. This proves equivalence of the three unrestricted RAM deadlines on the family allowing arbitrary closing clauses. The constant minimum of four identifies when both verdicts first occur; it gives no estimate of the time needed when the closing portion itself can encode arbitrary SAT. [Encoding and normalization](exact-network-ceiling-for-ordinary-sat.md)
