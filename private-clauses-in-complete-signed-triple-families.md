# A quadratic bound on pivotal clauses of complete signed 3-CNFs

Let a complete $k$-CNF on $n$ variables have a proper clause on every unordered $k$-subset, with one signed clause per support. In an unsatisfiable formula a clause is *pivotal* if deleting it alone makes the formula satisfiable. A *private witness* for that clause falsifies it and satisfies all the others. Put $B_k(n)=\sum_{j=0}^{k-1}\binom nj$.

**Theorem.** A complete unsatisfiable $k$-CNF has at most $(k+1)B_k(n)$ pivotal clauses. For $k=3$ the bound is $4(1+n+\binom n2)$. The proof also gives a fractional cover of all assignments of total weight at most $(k+1)B_k(n)$. The [choice-chain construction](sharp-pivotal-growth-on-complete-clause-supports.md) attains this exponent for every fixed width. An independent width-three argument below shows that every set of 43 variables contains a nonpivotal triple, so a maximal matching of nonpivotal triples covers all but at most 42 variables.

All deletions in the pivotal-clause statement are tested individually against the original formula. Choongbum Lee constructed ordinary minimally unsatisfiable 3-CNFs with $\Omega(n^3)$ clauses. Completeness is essential here. On the other hand, even a complete *satisfiable* instance can have every clause irredundant as a Boolean function, for example when every triple forbids three ones. These conclusions price input sensitivity on this family. They do not give a time lower bound on unrestricted RAM SAT. [Lee, *On the size of minimal unsatisfiable formulas*](https://arxiv.org/abs/0811.0427)

## Counting patterns with multiplicity

**Weighted counting lemma.** Let $U$ be any finite multiset of assignments to a complete unsatisfiable $k$-CNF. If each clause is false on at most $b$ occurrences in $U$, where $b\ge1$ is an integer, then
$$
 |U|\le (k+1)b\,B_k(n).
$$

For a submultiset $W$, call $S\subseteq[n]$ *shattered with multiplicity $b+1$* when every Boolean pattern on $S$ occurs at least $b+1$ times in $W$. Write $D(W)$ for the family of all such $S$. No $k$-set belongs to $D(U)$: its clause is false on at most $b$ occurrences. Shattering passes to coordinate subsets, hence $|D(U)|\le B_k(n)$.

If a coordinate $z$ splits $W$ into $W_0,W_1$, the families $D(W_0),D(W_1)$ omit $z$. Each member of their union belongs to $D(W)$. For each member $S$ of their intersection the larger set $S\cup\{z\}$ also belongs to $D(W)$: both halves supply all the patterns on $S$ at the stated multiplicity. The larger sets are distinct and absent from the union. Therefore
$$
 |D(W_0)|+|D(W_1)|\le |D(W)|.
$$
This is the coordinate-splitting argument underlying the Sauer–Shelah bound, applied to pattern counts. [Sauer, *On the density of families of sets*](https://doi.org/10.1016/0097-3165(72)90019-2) · [Anstee, *A survey of forbidden configuration results*](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS20/pdf/)

Whenever $|W|>(k+1)b$, some coordinate splits it with both sides containing at least $b+1$ occurrences. Otherwise take coordinatewise majority in $W$. Each coordinate differs from this assignment on at most $b$ occurrences. Some original clause is false at the majority by unsatisfiability. At most $kb$ occurrences differ from that majority on one of its variables, so the clause is false on more than $b$ occurrences, a contradiction.

Split recursively at such coordinates until each leaf has size at most $(k+1)b$. The children of every split have at least $b+1$ occurrences, so the empty set belongs to $D(W)$ at each non-root leaf. The potential inequality bounds the number of leaves by $|D(U)|$. If the root never split, its size already meets the claimed bound. This proves the lemma. For the pivotal-clause theorem take one private witness per pivotal clause. The selected assignments are distinct, and no clause fails on more than one.

For comparison, the ordinary multiplicity-one trace argument bounds the number of *satisfying* assignments of a complete $k$-CSP by $B_k(n)$. This appears in the complete-CSP literature and is used there for polynomial-time decision. The majority step above uses global unsatisfiability to bound the sizes of leaves containing imperfect assignments. I did not locate the pivotal or fractional statement in the cited sources. [*Min-CSPs on Complete Instances II*, §5 and Lemma 5.1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol353-approx-random2025/html/LIPIcs.APPROX-RANDOM.2025.5/LIPIcs.APPROX-RANDOM.2025.5.html)

## Fractional and integral covers by original clauses

For any probability distribution on full assignments, some clause is false with probability at least $\varepsilon=1/((k+1)B_k(n))$. For rational probabilities use a multiset with the indicated multiplicities and take $b$ to be the largest clause count. It is positive by unsatisfiability. For real probabilities pass to a limit; the maximum of finitely many linear functions is continuous. Finite minimax applied to the assignment-by-clause violation matrix now gives a probability distribution on original clauses such that every assignment falsifies a sampled clause with probability at least $\varepsilon$. Multiplying its weights by $1/\varepsilon$ gives a fractional cover. Conversely, the uniform distribution on a set of $p>0$ private witnesses satisfies every given clause with probability at least $1-1/p$, so every fractional cover has weight at least $p$.

There is also a jointly unsatisfiable subformula of size $O_k(n^{k-1+1/k}(\log n)^{1-1/k})$ for fixed $k\ge2$. Partition the variables into $O(n/s)$ blocks of size at most $s$ and take every clause inside a block. This costs $O_k(ns^{k-1})$ clauses. By the multiplicity-one bound each block has $O_k((1+s)^{k-1})$ satisfying assignments, giving at most $\exp(O_k((n/s)\log(1+s)))$ candidates in the product of the block model sets. If none remain the selected subformula is already unsatisfiable. Otherwise apply the distribution statement to the uniform distribution on the surviving candidates, add a clause eliminating at least an $\varepsilon$ fraction and repeat. At most $O_k(n^{k-1}(1+(n/s)\log(1+s)))$ more clauses suffice. Taking $s=\lceil(n^{k-1}\log(2+n))^{1/k}\rceil$, capped at $n$, proves the claim. For triples this is $O(n^{7/3}(\log n)^{2/3})$. The construction is existential with unrestricted time for finding its clauses.

## A forbidden grid of private clauses

Suppose $A,B,C$ are three disjoint sets of $t=6$ variables. Assume every triple in $A\times B\times C$ is pivotal and that, within this grid, each variable has one consistent forbidden sign. Negate individual variables so these signs are all one. Choose one private witness $w_{ijk}$ per grid clause. Within each part this witness has precisely one 1. For example, a second 1 in $A$ would falsify another grid clause with the same $j,k$. Give the $t^3$ witnesses equal probability.

For any variable $z$ outside the three parts, let $f(i,j,k)$ be its witness value. Suppose both values occur on at least $\beta=8/25$ of the grid. Fix $j,k$. The region $j'\ne j,\ k'\ne k$ is bichromatic: its complement occupies $11/36<\beta$. All four regions classified by the truth values of $B_j,C_k$ cannot be bichromatic. Otherwise every assignment on $\{B_j,C_k,z\}$ would occur among the private witnesses, even though all of them must satisfy the compulsory clause on those three names. This clause is distinct from every selected grid clause.

Call the line with fixed $j,k$ *mixed* if it contains both values of $z$ as $i$ varies. In the bipartite graph of mixed lines, every edge has an endpoint of degree one. Otherwise there would be a second mixed line in its row and another in its column, certifying both remaining regions bichromatic. Each nontrivial component is a star. A star forest on two parts of size $t\ge2$ has at most $2t-2$ edges: a connected component spanning all $2t$ vertices cannot be a star, and a forest with at least two components has at most $2t-2$ edges. In particular there are at most ten mixed lines. The same proof applies in each direction.

On a uniformly random line in one direction, independently resample its varying coordinate. Conditional on a line with fraction $q$ of ones, the probability that $f$ changes is $2q(1-q)\le1/2$, and it is zero on each constant line. Resampling the three coordinates in succession therefore changes $f$ between independent uniform endpoints with probability at most $3\cdot10/(2\cdot36)=5/12$. If $p=\Pr[f=1]$ belongs to $[\beta,1-\beta]$, those same endpoints differ with probability $2p(1-p)\ge272/625>5/12$. This contradiction shows that every outside variable has minority frequency below $8/25$. The variables inside the grid have minority frequency $1/6$.

Give every variable its majority value under these witnesses. If this assignment falsifies some clause, the union bound says that clause is falsified by at least $1-3(8/25)=1/25$ of the witnesses. But every clause is falsified by at most one of the $216$ witnesses. This constructs a satisfying assignment and proves the grid impossible in an unsatisfiable formula.

## A local loss in the subcube inequality

For each triple $E$, write $C_E$ for the subcube of assignments taking its three forbidden values. A private point belongs to $C_E$ alone. Call a family irredundant if each cube has a private point. Call its signs consistent if there is a bit $s_i$ for each coordinate such that every cube fixing $i$ fixes it to $s_i$.

**Lemma.** A complete irredundant family on 43 or more coordinates has consistent signs.

Choose a private $w_E$ for each cube. At a base vertex $x$, consider the triples $E$ with $x\in C_E$. Put $B_E=\{i:x_i\ne(w_E)_i\}$. Then $E\cap B_E=\varnothing$, while $F\cap B_E\ne\varnothing$ for each other passing triple $F$. The events that a random permutation places all of $E$ before every member of $B_E$ are pairwise disjoint. Define their uncovered probability by

$$
 L(x)=1-\sum_{E:x\in C_E}\binom{3+|B_E|}{3}^{-1}.
$$

This is the local inequality in Ellis's proof of Meshulam's subcube bound. Each cube contributes total weight $\sum_{d=0}^{n-3}\binom{n-3}{d}/\binom{d+3}{3}$ as $x$ varies. [Ellis, *Irredundant Families of Subcubes*, Theorems 3–4](https://arxiv.org/abs/1003.2960)

Multiplying the $d$-th term by $\binom n3$ gives $\binom n{d+3}$. Since there is exactly one cube on each triple,

$$
 \sum_x L(x)=1+n+\binom n2.
$$

Suppose two triples $A,F$ choose opposite values at their common coordinate $i$. Choose a triple $B$ disjoint from $A$ containing $F\setminus A$, so $S=A\cup B$ has size six. At all $2^{n-6}$ vertices matching $A$ and $B$, both anchors pass, and $F\subset S$ fails at $i$. Condition a random permutation on $S$ occupying its first six positions. No passing triple $E\not\subseteq S$ can precede its blocker, since $B_E$ meets $A$ and some element of $E$ lies after $S$. For the surviving edges $E\subseteq S$ the event depends exactly on the order of $E$ and $B_E\cap S$.

The restricted pairs still satisfy the cross-intersection condition. Equality in the Bollobás set-pairs inequality requires the first sets to be all 3-subsets of a single set $Y$, with the corresponding second sets the complements in $Y$. Since $A,B$ pass, $Y$ must contain all of $S$, and since all the restricted pairs lie within $S$, equality would force $F$ to pass. Every restricted blocker has size at least one because it meets another passing edge and at most three because it avoids its own triple. Thus each weight is $1/4,1/10$ or $1/20$, and the conditional uncovered probability is at least $1/20$. [Bollobás, *Extremal Graph Theory*, Theorem 3.1.2 in the handbook chapter](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Bollobas/Bollobas.pdf)

It follows that $\sum_x L(x)\ge2^{n-6}/(20\binom n6)$. At $n=43$ the numerator is 137,438,953,472 and $20\binom{43}6(1+43+\binom{43}2)=115,466,838,760$, a contradiction. For larger $n$, restriction to any 43 coordinates preserves completeness and irredundance by projecting the private points of the retained triples. Any two inconsistent triples lie in such a restriction. This proves the lemma.

Now let $O$ consist of any 43 variables in the full formula. If all its triples were pivotal, their projected private witnesses would give a complete irredundant family on $O$. By the lemma we could flip signs on $O$ and use any three disjoint six-subsets of $O$ as a consistent grid of pivotal clauses. The preceding construction rules this out regardless of the remaining variables. Hence every 43-set contains a nonpivotal triple. The vertices uncovered by a maximal matching of nonpivotal triples form such an independent set, so there are at most 42 of them.

## Any fixed clause width

Fix $k\ge2$, and suppose we have a consistent grid of pivotal clauses with $k$ parts of size $t$. Its private witnesses again select one name per part. For an outside variable $z$ and one axis, mark a $(k-1)$-tuple of indices in the other parts if $z$ varies on that line. The marked tuples contain no box with two distinct choices per part. If such a box existed, choose one of its two names as anchor in each of the $k-1$ parts. Every possible vector of anchor bits occurs on one of its mixed lines. Both values of $z$ occur there, contradicting the compulsory clause on those $k$ names.

Write $r=k-1$. If $M\subseteq[t]^r$ has density $q$, the probability that a random two-choice box lies in $M$, drawing its two indices per coordinate *with replacement*, is at least $q^{2^r}$. To see this, write $h_r(M)$ for the probability. Conditional on the first $r-1$ pairs, let $g$ be the probability that their box belongs to the slice at one random last coordinate. Independence of the last two choices yields $h_r(M)=\mathbb E[g^2]\ge(\mathbb E g)^2$. But $\mathbb E g$ is the mean of $h_{r-1}$ over the last-coordinate slices. Induction and convexity give the claim, starting with $h_1(M)=q^2$. If $M$ has no box with distinct choices in all axes, an all-marked random box needs a repeated index in some coordinate. Thus $q^{2^r}\le r/t$.

Successive resampling of the $k$ coordinates now bounds the independent-endpoint discrepancy for $z$ by $(k/2)(r/t)^{1/2^r}$. For $\beta=1/(2k)$ choose a constant integer $t=t(k)>2k$ large enough that this is less than $2\beta(1-\beta)$. Every coordinate then differs from its majority on less than $\beta$ of witnesses. A clause falsified by the majority would fail on at least half the witnesses, although only one of $t^k$ witnesses can violate it. This excludes a consistent pivotal $k$-partite grid of fixed size.

As an additional restriction on where the pivotal supports can occur, Erdős's complete-partite bound gives $O_k(n^{k-1/t^{k-1}})$ pivotal clauses after coloring ordered supports by their $2^k$ sign patterns. The same counting proof applies with any subset of the original variable names as its vertex set: an excluded grid there would also furnish a model of the entire formula. If all $k$-subsets of $s$ names were pivotal, they would yield $\binom sk=O_k(s^{k-1/t^{k-1}})$. Thus the maximum such $s$ is bounded by a constant depending only on $k$. Every maximal matching of nonpivotal supports covers all but $O_k(1)$ variables. [Erdős, complete-partite extremal theorem](https://combinatorica.hu/~p_erdos/1964-13.pdf)

## Verification

Lean 4.34.1 with Mathlib kernel-checks the full finite weighted counting lemma as `signed_complete_bound` and the pivotal-clause theorem as `pivotal_count`. These definitions quantify the forbidden pattern on each support, the original unsatisfiability assumption and, for the weighted version, a finite set of occurrence IDs that may encode repeated assignments. Use `lake env lean /absolute/path/to/upstream-checks/PrivatePatternBudget.lean` from a Mathlib checkout providing the two imports. The fractional minimax and integral-cover arguments are given in the manuscript. [Kernel-checked weighted and pivotal theorems](upstream-checks/PrivatePatternBudget.lean)

The executable audit tests 39,366 multiplicity-aware coordinate splits exhaustively on three variables. It also checks 88 complete ternary UNSAT files by truth tables, covering 144 private witnesses and 22 nontrivial splits with one and two copies of each witness. For the localized grid statement, the program counts 685,507 admissible labeled six-by-six mixed-line graphs and verifies their ten-edge maximum. It tests 182 balanced block colorings and 1,728 signed grid clauses. The auxiliary subcube census checks all 262,143 proper six-coordinate families with two fixed complementary triples. Exactly 18 attain the sharp conditional weight $19/20$. The local mathematical proof uses Bollobás’s published equality characterization independently of the census. A separate core-only Lean component checks the 216-witness majority implication and two private-witness transfers. [Executable audit](complete_triple_private_cube_audit.py) · [Lean lemmas for the localized argument](PrivateTripleAnchors.lean)
