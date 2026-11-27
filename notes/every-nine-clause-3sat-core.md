# Every minimally unsatisfiable proper 3-CNF with nine clauses

For $v$ labeled variables, the exact number of inclusion-minimal unsatisfiable sets of nine proper clauses is
$$
9408\binom v4+324000\binom v5+1913280\binom v6+
3430560\binom v7+1774080\binom v8 .
$$
Each clause has three distinct variables. Variable names and signs matter, clause order is immaterial, and repetitions cannot occur in a minimal formula. The coefficients count formulas that use every name in their selected support. Tarsi's lemma bounds the number of used variables of a minimal unsatisfiable formula by its clause count minus one. This makes the finite enumeration sufficient for every $v$. [Aharoni and Linial](https://doi.org/10.1016/0097-3165(86)90060-9) · [Census program](../audits/nine_clause_core_search.cpp)

| Used variables | Minimal cores on exactly these names | Have a variable occurring twice | Have four-coordinate doubled set |
|---:|---:|---:|---:|
| 4 | 9,408 | 192 | 7,104 |
| 5 | 324,000 | 183,360 | 245,760 |
| 6 | 1,913,280 | 1,861,920 | 1,443,840 |
| 7 | 3,430,560 | 3,430,560 | 2,553,600 |
| 8 | 1,774,080 | 1,774,080 | 1,290,240 |

Thus all seven- and eight-variable cores at nine clauses have a variable occurring twice. On six variables there are 51,360 full-support counterexamples. Any used variable in a minimal unsatisfiable formula occurs with both signs, since otherwise fixing it to satisfy its occurrences leaves a proper unsatisfiable subset. Consequently a variable counted in the third column occurs exactly once with each sign. A prior public counter reports the 4-, 5- and 6-used-variable coefficients in its verified 3-SAT table. Those values are independent reproductions. The five-variable count is also checked by separate inclusion–exclusion on assignment slices. [Prior enumeration](https://github.com/fGhost713/Satisfiability-MinUnsatCounter) · [Independent whole-layer transform](../audits/five_variable_sat_mobius_audit.py)

The four-variable coefficient agrees with the earlier enumeration by edge covers and by direct testing of all 28,048,800 clause sets. [Four-variable and eight-clause counts](minimal-sat-cores-under-one-more-clause.md)

## A pairwise test for the first clause count above the volume bound

For width $k\ge1$, let $F_1,\ldots,F_{2^k+1}$ denote the forbidden coordinate faces of proper clauses. Let $H(x)=\sum_i1_{F_i}(x)$ for a uniformly random assignment. The formula is UNSAT if and only if
$$
                 \sum_{i<j}\Pr(F_i\cap F_j)=2^{-k}.                     \tag{1}
$$
Each summand can be read off a pair of clauses. It is zero when their falsifying patterns disagree on a shared variable, and otherwise equals two to the negative of the size of their combined variable support.

Indeed $\mathbb EH=1+2^{-k}$, so the left side of (1) minus $2^{-k}$ is $\mathbb E[(H-1)(H-2)/2]$. Its integrand is nonnegative at every nonnegative integer, and vanishes exactly for $H=1,2$. Equality therefore ensures UNSAT. Conversely, for an unsatisfiable formula the nonnegative integer function $h=H-1$ has mean $2^{-k}$ and real multilinear degree at most $k$. A nonzero polynomial of degree at most $k$ on a binary cube is nonzero on at least a $2^{-k}$ fraction. Fix variables outside a monomial of maximum degree. Its coefficient survives every such fixing, so every remaining subcube contains a nonzero evaluation. Mean and support now force $h$ to take precisely values zero and one. This proves (1), and proves that exactly a $2^{-k}$ fraction of assignments falsify two clauses, with every other assignment falsifying one. This conclusion also holds for a list with repeated clauses.

## Only two doubled sets occur at width three

The indicator $h$ of doubled assignments is a binary polynomial of degree at most $k$ as well, by reducing the integer clause expression modulo two. Its support $S$ is an affine flat of codimension $k$. To see this directly, $h(x+u)+h(x)$ modulo two has degree at most $k-1$. If nonzero, its support $S\mathbin{\triangle}(S+u)$ has size at least $2|S|$, which by the triangle inequality is its maximum possible size. Thus translates of $S$ are either equal or disjoint. Choosing $x_0\in S$ shows that $S=x_0+\{u:S+u=S\}$. The density already gives the codimension. This is the minimum-weight case of Reed–Muller codes.

For $k=3$ let $E$ be the three-dimensional binary orthogonal complement of the direction space of $S$. The real Fourier support of $1_S$ is exactly $E$, by averaging characters on an affine subspace. Real multilinear degree at most three implies that every word of $E$ has Hamming weight at most three. If $m$ coordinates occur anywhere in $E$, their total weight over its seven nonzero words is $4m$, giving $m\le5$. At $m=5$ there must be six words of weight three and one of weight two. This is impossible because the parity functional on $E$ is odd on either zero or four words. Hence $m=3$ or $4$.

On three coordinates $E$ is the full space and $S$ fixes these three bits. On four coordinates $E=y^\perp$ for a single nonzero four-bit vector $y$. Its weight is odd because the all-ones word cannot lie in $E$, and $y$ cannot have weight one because all four coordinates occur in $E$. Therefore $y$ has weight three. On the four active coordinates $S$ consists of two patterns that agree on one bit and differ on all other three. Every remaining bit is free. The program checks membership of every observed doubled set in the list of these two types. The last column of the table counts the second type.

In a nonminimal UNSAT set of nine distinct clauses, every redundant clause must have its whole face inside $S$. Both have measure $1/8$, so the two sets coincide. Distinct clauses have different faces, so exactly one clause can be redundant. Conversely one may add any new proper clause to an eight-clause partition. Thus the total number of UNSAT nine-clause sets equals the minimal count above plus $(8\binom v3-8)$ times the eight-clause count for $v\ge3$. At $v=4$ this gives $9408+24\cdot272=15936$ and agrees with direct enumeration.

## Where pair data first fail

The matrix of pairwise intersection probabilities of all falsifying faces no longer determines SAT at $2^k+2$ clauses, for every $k≥2$. At width two use the three edges of a triangle and, for each edge, forbid both 00 and 11 with two clauses. Feasible assignments would two-color the triangle, so it is UNSAT. Instead use the three edges of a claw with one center and three leaves and forbid the same two patterns on each. The claw is bipartite, so the formula is SAT. Ordering the six forbidden faces by their two signs gives identical labeled pair matrices. Each diagonal is $1/4$, off-diagonal entries within either sign block are $1/8$, and every cross-block entry is zero. Two edges of either graph meet in exactly one coordinate; the shared coordinate makes opposite patterns inconsistent. Thus even keeping every individual pair, in place of just their sum, cannot repair the test.

To raise width, add one fresh literal to all existing clauses, so they constrain one half of the cube. On the opposite half forbid all patterns of $k$ chosen old variables, using the opposite fresh literal. The opposite half is covered exactly once. The verdict on the first half therefore decides SAT on the whole cube. Old pair probabilities are halved, old-to-new intersections vanish, and the new partition is identical for both formulas. The clause count passes from $2^k+2$ to $2^{k+1}+2$. For $k=2$ use the pair consisting of the claw's fourth variable and one common name in the new partition. At width three the two formulas then each use exactly five names and ten distinct proper clauses. This lifts a failure of using pair data, without bounding RAM time.

## Why the census exhausts all candidates

A node stores the clauses selected so far, uncovered assignments, assignments covered at least twice, and allowed future clauses. The search fixes an initial clause by sign and variable symmetry. From every incomplete node it takes the least uncovered assignment $x$ and tries each still-allowed clause containing $x$ in a fixed order. In a child's subtree earlier tried clauses containing this pivot are forbidden. Other clauses remain available regardless of their index. Each completion must select at least one of these candidates, so it is assigned to exactly its first chosen candidate. Induction proves no completion is omitted or duplicated.

A node with $j$ clauses still to pick can cover at most $j2^{v-3}$ more assignments. Pruning whenever the next selection violates this bound loses no cover. Every selected clause also needs a private assignment that no other selected clause covers. Loss of its last private assignment is permanent. The pivot supplies a private assignment for the newly selected clause. A complete cover at depth below nine cannot be extended minimally. These checks are sufficient at a nine-clause leaf.

All proper signed clauses lie in a single orbit. If a property of a core is invariant under signs and variable permutations, then its total labeled count is its count at the fixed first clause, times $8\binom v3/9$. This double-counts pairs consisting of a core and a distinguished member clause. The executable checks this division is exact for every category, and separately rechecks coverage and a privateness witness for each clause using raw literal patterns at every 4,096th accepted leaf, starting at the first.

| Available variables | Fixed-clause terminal cores | All labeled minimal cores | Elapsed seconds on one reference run |
|---:|---:|---:|---:|
| 4 | 2,646 | 9,408 | <0.01 |
| 5 | 41,742 | 371,040 | <0.01 |
| 6 | 224,910 | 3,998,400 | 0.08 |
| 7 | 770,040 | 23,956,800 | 0.80 |
| 8 | 2,040,930 | 101,592,960 | 6.04 |

The timing used one process per size and an optimizing C++17 compiler with native instruction selection. The command below runs the largest size. The four- through seven-variable runs use the same executable with the corresponding integer argument.

```sh
c++ -std=c++17 -O3 -march=native nine_clause_core_search.cpp -o /tmp/nine_cores
/tmp/nine_cores 8
```

The search found prior work on deficiency-one formulas and their singular-variable reductions, and on bounds for minimum variable degree. The minimum-weight polynomial and affine-flat facts used above are classical. I have not established priority for the numerical census, the two doubled-set types in this formulation, or the pairwise SAT criterion at $2^k+1$ clauses. The formulas here have a fixed number of clauses at width three. The classification and pairwise criterion give no superlinear unrestricted RAM lower bound for arbitrary encoded SAT. [Kullmann on deficiency-one structure](https://arxiv.org/abs/1103.3693) · [Kullmann and Zhao on minimum variable degree](https://arxiv.org/abs/1408.0629)
