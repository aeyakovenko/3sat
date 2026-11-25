# Exact ambiguity of clause-local 3-SAT replacements

A proper ternary CNF can represent $a\lor b\lor c$ with **exactly one auxiliary assignment per true input literal**, using four auxiliary variables and eleven clauses. Each input occurs positively once, in a different clause. Deleting any clause admits an auxiliary assignment at boundary $000$. Both four auxiliaries and eleven clauses are minimum under these conditions.

## An optimal local formula

Use auxiliary variables $s,x,y,z$ and the three port clauses
$$
    (a\lor s\lor x),\quad (b\lor s\lor y),\quad(c\lor s\lor z).
$$
Add the four ordinary clauses on $x,y,z$ forbidding the individual patterns $000,100,010,001$, and the clause $(\neg x\lor\neg y\lor\neg z)$ forbidding $111$. For each of the three unordered pairs $u,v$ from $x,y,z$ add $(\neg s\lor\neg u\lor\neg v)$. The five clauses on $x,y,z$ force weight two; their true pair forces $s=0$. The unique zero coordinate chooses a true port. Each choice gives exactly one extension.

At boundary $000$, deleting a port clause allows precisely its selected coordinate to be zero with $s=0$. Deleting a low-weight-pattern clause allows its pattern with $s=1$. Deleting the $111$ prohibition allows $111$ with $s=0$. Deleting a pair clause allows precisely that pair to be one with $s=1$. Each of the eleven deletions thus has a unique satisfying assignment at zero. For a gadget whose projection is OR, essentiality of every row for the projection is equivalent to this zero-boundary deletion condition, with existence alone sufficient. [Local port lemmas and finite gadget formalizations](LocalClausePorts.lean) · [Independent executable audit](row_minimum_for_literal_witnesses.py)

## Why fewer rows or variables cannot suffice

Write $H$ for the auxiliary assignments satisfying all rows without a port. These are the three models at $111$. Turning off port $i$ forbids a codimension-two face $S_i$ defined by the two other literals of its row. Each singleton true port must have a model. These three models are distinct because a model for two different singleton settings would pass every clause at $000$. Thus $H$ consists of three distinct markers $m_i$, with $S_i\cap H=\{m_i\}$.

Fewer than two auxiliaries cannot supply the distinct literals in a port row. With two there is no proper unguarded row and all four assignments survive at $111$. With three, each unguarded row forbids a single point. Its private witness at zero must be that point and must lie outside all $S_i$. Hence every point in each two-point $S_i$ survives the unguarded rows, contradicting $|S_i\cap H|=1$.

With $d\ge5$ auxiliaries, seven unguarded ternary rows forbid at most $7\cdot2^{d-3}<2^d-3$ assignments. With $d=4$ each unguarded row instead forbids an edge of the four-cube. Covering the thirteen points outside $H$ needs at least seven edges. If there are exactly seven, counting the fourteen endpoints with multiplicity shows that one vertex has degree two and the twelve others have degree one. The cover consists of a two-edge path and five disjoint edges. Its path leaves must both be outside $S_1\cup S_2\cup S_3$ for the two path edges to have private witnesses at zero. Each of the five other edges also needs at least one endpoint outside that union.

The four-cube exclusion is a finite computational step. The audit enumerates all 560 unordered marker triples, then all choices of one of the 24 faces for each marker meeting no other marker. For each edge cover it chooses its unique path center and its two leaves and enumerates perfect matchings of the remaining ten points by pairing the least unmatched vertex. This gives 33,376 compatible face choices, 67,200 edge covers, and 3,086,208 face-choice/edge-cover pairs with the same marker triple. Zero pairs satisfy the private-endpoint conditions. This proves that eight unguarded rows are necessary also at $d=4$. [Complete standard-library census](row_minimum_for_literal_witnesses.py)

An independent Lean proof selects one private endpoint from each of the seven proposed edges. These seven points $P$ are distinct and outside the three port faces. Each selected edge joins its private endpoint to one of the six remaining nonmarker points $R$, and every point of $R$ must be reached. A surjective neighbor map from $P$ to $R$ would provide a neighbor for every point on both sides and three distinct neighbors for every three distinct points of $R$. Lean proves these implications for arbitrary rows and checks by enumeration that no eligible faces, markers and $P$ pass all three conditions. The theorem starts from the assignment sets hit by each row, indexed by its chosen private witness. The closed enumeration uses Lean's native evaluator through `native_decide`. The counting reduction from arbitrary CNF to four cube coordinates and seven edges above is written in prose. [Lean four-cube exclusion](FourCubeLiteralWitnessCover.lean)

## The sharp count on every source formula

Replace each clause $C$ of a proper 3-CNF $F$ independently by a gadget with three different once-occurring positive port rows, identifying the ports with the truth values of its three original literals. Different occurrences of the same source variable retain that variable, with the appropriate sign. Gadgets for different clauses have disjoint private auxiliaries and interact only through source variables. Allow different gadgets for different clauses, with any number of rows and auxiliary bits. Write $\tau_C(\alpha)$ for the number of true literals in $C$ under the source assignment $\alpha$.

For any local gadget projecting to OR, choose one witness per singleton true port. Distinct singleton rows have distinct witnesses, by the zero-boundary argument above. Turning on further ports preserves an existing witness, since each port occurs only positively. Thus a clause with $t$ true literals has at least $t$ auxiliary witnesses. Independence across clauses and summation over source assignments give
$$
       \#\mathrm{SAT}(F_{\mathrm{replaced}})
       \ \ge\ \sum_{\alpha}\ \prod_{C\in F}\tau_C(\alpha).
$$
A falsified clause contributes zero. The eleven-row gadget attains equality on **every** $F$, including formulas whose clauses share variables. The lower bound itself needs no deletion-privacy assumption.

For a concrete uniquely satisfiable source, take the seven signed clauses on three variables that forbid all assignments except $111$. At its unique model three clauses have one true literal, three have two and one has three. The minimum number of extensions is therefore $1^3 2^3 3=24$. Taking $m$ disjoint such source triples gives exactly $24^m$ as the attainable minimum.

There is also an obstruction when several ports may share one row within a gadget. Assume no replacement consists solely of the original three-port clause, each replacement projects to OR, and every row is essential to that projection. A gadget with all three ports together would contain the original proper ternary clause. Deleting any other row would still leave $000$ forbidden, so at least two different rows must contain ports. At $111$ these different rows yield at least two witnesses: enable a single representative port from each row in turn, and apply the same disjointness argument. In each seven-clause block the all-positive clause sees $111$. Every other clause is satisfied and has at least one extension. Hence even this broader independent substitution produces at least $2^m$ extensions of the unique source assignment.

These counts delimit replacing clauses independently while preserving a low-ambiguity SAT promise. The bounds use the once-occurring positive ports and independent auxiliary sets. Global encodings can coordinate their witnesses differently. The distinctions between deletion witnesses and solving the original instance also arise in the work of Burjons et al. Historical priority for the optima here has not been established. [Burjons et al., *Finding Optimal Solutions with Neighborly Help*](https://doi.org/10.1007/s00453-023-01204-1)
