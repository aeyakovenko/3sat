# Two deleted clauses per local triple suffice for unrestricted 3-SAT

The exact repair-distance construction admits a packed scan on the tested faces because six local clauses force three variables to agree. How much damage to those six clauses can a linear solver tolerate? For the following named family of ordinary proper 3-CNFs there is an exact boundary for the **reduction to Boolean binary constraints**. One deletion per local triple always preserves that reduction. Two deletions suffice to encode every proper 3-SAT instance with linear construction time and encoded length. Two layers suffice, and every one-layer instance admits a scan-time solver. Three of the four port maps can be crossing perfect matchings across a common bipartition. The last map has exactly two fixed points. Restoring their single crossing edge always gives two explicit complementary satisfying assignments. [Preceding sheet construction and its fast algorithm](exact-repair-distance-of-sheeted-sat-formulas.md)

A sheet has one public variable $x_i$ shared across layers. At center $i$ in one layer, use two fresh private variables $y,z$. The six guard clauses exclude the six mixed triples $(x_i,y,z)$, so leaving them intact permits exactly $000,111$. Deleting the clause for a pattern permits that pattern too. In addition the center has the ordinary clauses
$$
                        (a\lor y\lor z),\qquad (\neg b\lor\neg y\lor\neg z).
$$
Here $a=x_{\pi(i)}$ and $b=x_{\sigma(i)}$, where the two permutations separately consist of disjoint left–right swaps and fixed points. This is the positive and the negative port of the earlier sheet construction. Every clause has three distinct variable names even when $a=b$ or when one of them is $x_i$. Each private variable belongs to only this center and layer. The encoded names specify their roles.

## The complete local exhaustion

For fixed $x$, the allowed local rows have three possible effects.

* If any retained possibility has $y\ne z$, both port clauses are satisfied for that $x$.
* If the only possible pair is $y=z=x$, the surviving requirement is $a$ when $x=0$, and $\neg b$ when $x=1$.
* If both equal pairs are allowed and no unequal pair is allowed, the requirement is $a\lor\neg b$.

For each of $x=0,1$, the three corresponding counts among the eight choices of which three mixed patterns at that value of $x$ to restore are $6,1,1$. Taking their Cartesian product exhausts all 64 deletion masks. Exactly 52 yield a conjunction of some of the binary clauses $x\lor a$, $\neg x\lor\neg b$, $a\lor\neg b$. The other 12 yield a single genuine ternary clause, forbidding only $101$ or only $001$ in $(x,a,b)$. Four of these masks use two deletions, six use three, and two use four. A relation excluding just one triple is not expressible by a 2-CNF on those variables, even with existential auxiliary bits. Its three one-coordinate neighbors have the excluded triple as their coordinatewise majority, while binary clauses and existential projections preserve majority. [Schaefer on Boolean constraint relations](https://doi.org/10.1145/800133.804350) · [Lean verification of the projection](SheetGuardProjection.lean)

Thus **all masks with at most one deletion** yield 2-CNF. The same holds with any number of deletions if each deleted local pattern is accompanied by its bitwise complement. In that case the types at the two $x$ values agree. Processing each center once and applying the implication-graph algorithm gives an $O(gd)$-step RAM solver on $d$ sheets with $g$ layers and dense, word-readable role names. Parsing the canonical ASCII files takes $O(N)$ time in their encoded length. The solver can validate the roles and use general SAT on other formats. [Aspvall, Plass and Tarjan](https://doi.org/10.1016/0020-0190(79)90002-4)

## The two-layer reduction

Use only two guard types in the entire output. Type $I$ leaves all six guards intact. Type $P$ deletes precisely the guards excluding $001$ and $100$. Eliminating the private pair gives
$$
 I(x,a,b)=(x\lor a)\land(\neg x\lor\neg b),\qquad
 P(x,a,b)=\neg x\lor a\lor\neg b.
$$

**Layer one copies logical variables.** Create a physical sheet for each occurrence needed below, placing it on the requested side. Each occurrence carries a logical name $X$. Add unused occurrence sheets so that each logical name has the same number of left and right occurrences. For one name list these as $l_j$ and $r_j$, with $l_j$ standing for its physical bit and $r_j$ for the *complement* of its right physical bit. Use positive edges $L_j$–$R_j$ and negative edges $L_j$–$R_{j+1}$, cyclically. All centers in this layer have type $I$. The left centers impose $r_j\Rightarrow l_j\Rightarrow r_{j+1}$. Going around the cycle forces every $l_j,r_j$ to one logical value. Either common value also satisfies every right center. Thus after layer one the physical values of left and right occurrences of $X$ are exactly $X$ and $\neg X$, regardless of the number of occurrences. [Lean cycle and converse](SheetGuardProjection.lean)

**Layer two uses a single ternary relation and two intact centers.** A job $P(c,a,b)$ uses fresh occurrence sheets for its three requested values, with $a,b$ on the opposite side to $c$. Give the job one further sheet $z$ on $c$'s side, bearing a new logical name private to this job. Use positive matching edges $c$–$a$, $z$–$b$ and negative matching edges $c$–$b$, $z$–$a$. All four centers have type $P$. Apart from the desired clause there are exactly three reciprocal constraints, $P(a,c,z)$, $P(b,z,c)$ and $P(z,b,a)$. Setting the physical bit $z=c\land b$ satisfies all three for any $c,a,b$. The opposite-side occurrence introduced to balance $z$'s first-layer cycle places no restriction on its value: all unused occurrences in the second layer are paired across sides with the same partner on both ports, and $P(x,t,t)$ is always true. The four-sheet jobs are disjoint. [Lean identities for the four centers](SheetGuardProjection.lean)

Reserve one special box with left sheets $h,h'$ and right sheets $r_1,r_0$. Fix the positive ports of $h,r_0$ at themselves and pair $h'$ with $r_1$. On negative ports pair $h$ with $r_1$ and $r_0$ with $h'$. Only $h,r_0$ have type $I$. Their constraints $I(h,h,r_1)$ and $I(r_0,r_0,h')$ force physical values $h=r_0=1$ and $r_1=h'=0$. At the other two centers $P$ holds since the center bit is zero. Give $h,r_1$ the logical name ONE and $h',r_0$ the logical name ZERO. The first layer supplies as many calibrated copies of either constant as needed.

For each original variable $X$ create a second logical symbol $Z$ for its negation. Write $L_X,R_X$ for fresh occurrences of the indicated name and side at each use. The two jobs
$$
                    P(R_X,L_Z,L_{\rm ONE}),\qquad
                    P(L_X,R_Z,R_{\rm ZERO})
$$
impose $X\lor Z$ and $\neg X\lor\neg Z$, hence $Z=\neg X$. Finally encode $\ell_1\lor\ell_2\lor\ell_3$ by $P(L_{\neg\ell_1},R_{\neg\ell_2},R_{\ell_3})$, replacing each literal by its appropriate logical name. It projects to exactly that clause. All job assignments lift to the private $y,z$ variables at each center independently. Conversely every satisfying assignment yields a consistent assignment to the source clauses.

There are exactly two layers. The first is uniformly intact. The second uses the same fixed deletion pair everywhere except its two intact anchor centers. Every port map is a crossing perfect matching except the one positive map with two fixed points. This achieves all three structural boundaries together.

## The two physical bits carrying the verdict

Restore the missing positive edge by swapping the fixed endpoints $h,r_0$ with one another. The resulting file has two explicit complementary satisfying assignments: give all sheet bits on one side zero, those on the other one, and take both private bits equal to their center, or complement every bit. In the unrepaired encoding each of these assignments violates exactly one clause, at different anchors. A balanced crossing involution cannot have just one fixed endpoint because its unmatched left and right sets have the same size.

Give $h,r_0$ the identifiers 10 and 11. Their encodings differ in one bit in both binary and ASCII. The transposition then changes two positive literal identifiers in two records. In either intermediate setting just one positive port remains fixed; its center can be given value one by choosing the appropriate complementary assignment. Thus of the four settings of these **two designated physical bits**, three have known satisfying assignments. At the fourth the SAT verdict is exactly the source verdict. The two intermediate files remain ordinary proper 3-CNF even though their altered port maps are not permutations. Prior work gives hardness for SAT even when satisfying assignments for every one-clause deletion are supplied. The restriction here concerns a length-preserving matching edit, two uniform layers, and two complementary assignments. [Burjons et al., Theorem 2](https://doi.org/10.1007/s00453-023-01204-1)

Let $q$ be the number of distinct proper source clauses. Remove duplicate clauses first. Intern ASCII identifiers in a digit trie, sort the three signed IDs in each row, then radix-sort triples of dense IDs. This takes $O(N)$ word operations on an $N$-bit file, including normalization of leading zeros where the input permits them. Choose one full input record string for each distinct clause. They are $q$ different, disjointly occurring strings, so their total encoded length is $\Omega(q\log(q+2))$ for growing $q$ by counting short strings. Only variables occurring in the retained clauses need logical names. The jobs, occurrence sheets, new private symbols and balancing slots all number $O(q+1)$. Their dense identifiers use $O(\log(q+2))$ bits or digits. Including the header, the new proper 3-CNF has $O(N+1)$ encoded bits and deterministically takes $O(N+1)$ word operations to construct. A fixed list of unused dummy names can handle small inputs. No bounded-occurrence normalization of the source is needed.

Accordingly, deciding whether the one designated transposition on the fully crossing file preserves satisfiability is NP-complete, and any $O(N)$ algorithm for it would decide ordinary proper 3-SAT in $O(N)$ time. Both parts count preprocessing on the initial file, even when its two known witnesses are supplied. The reduction also preserves quadratic and cubic time targets. This equivalence supplies no unconditional time exclusion. [Compiler and four-setting DIMACS audit](sheet_guard_deletions_audit.py)

## What one layer and random wiring actually cost

With only one layer the union of the two involutions has degree at most two after suppressing loops and duplicate edges. The shared bits form paths and cycles. Each projected constraint involves just a vertex and its neighbors. A scan retaining two successive bits suffices for a four-state dynamic program, trying the four initial bit pairs to close a cycle. Handle singleton and two-vertex components directly. This takes $O(d)$ packed-word steps on the named one-layer layout with $d$ sheets for **all 64 deletion masks**, including any number of fixed points.

There is a stronger positive test on the homogeneous two-layer family. Suppose there are $a$ sheets per side and the relative permutation of the first layer's two matchings has $c$ cycles. After contracting them there are just $c$ Boolean variables and $O(a)$ clauses. Remove tautologies and deduplicate by radix sorting signed variable indices. The residual has $O(c^3+1)$ clauses. Branch on all satisfying assignments to the variables of one residual clause of width $j\le3$ at a time. This has branching factor at most $2^j-1\le 7^{j/3}$ while fixing $j$ fresh variables. With the work for simplifications and possible internal nodes the time is $O(a+\operatorname{poly}(c)7^{c/3})$ in the fixed-width packed encoding. Width-one steps do not invalidate this bound since the tree depth is at most $c$. This is an exact solver on every input in the class.

If the relative permutation of the first layer is uniform, its cycle count satisfies $\mathbb E[\theta^c]=\prod_{i=1}^a(1+(\theta-1)/i)=O_\theta(a^{\theta-1})$ for constant $\theta>1$. Inserting the next label into a uniform permutation starts a new cycle in precisely one of the possible insertion slots, giving the product formula. Choose $7^{1/3}<\theta<2$ to absorb the polynomial in $c$. The expected solver time is then **$O(a)$**, even if the entire second layer is chosen adversarially after seeing the first. Thus sampling these unconditioned layouts typically removes most of the independent logical variables that carry the source instance.

Normalize the first positive matching to identity and designate the missing edge by its left endpoint zero. For each $a$, the census counts $(a!)^3$ labeled choices of the other three perfect matchings before that edge is removed. It groups identical sets of surviving assignments for the first-layer cycles and intersects them with the exact second-layer truth table.

| Sheets per side | SAT | UNSAT |
| ---: | ---: | ---: |
| 1 | 0 | 1 |
| 2 | 1 | 7 |
| 3 | 28 | 188 |
| 4 | 1,656 | 12,168 |
| 5 | 179,280 | 1,548,720 |
| 6 | 33,192,720 | 340,055,280 |

Appending one new sheet on each side, paired to one another by all four matchings, preserves the old verdict and the two exceptional fixed entries. It gives exactly four extensions of every full satisfying assignment, counting the private variables. The new first layer admits either orientation with its private bits fixed. In the second layer the center with value zero has two private completions and the center with value one has one. A program can recognize and discard this independent component. The exact factor of four enlarges the witness count without forcing comparable growth in the solver's running time. [Permutation census and full-assignment check](two_layer_sheet_census.py)

## How many genuinely ternary centers fit in linear time?

Let $t$ count centers whose projected relation genuinely forbids just one ternary pattern. The rest form a 2-CNF on the shared bits. Reject if its implication graph has a contradictory strongly connected component. Mark the at most $3t$ terminal literals of the ternary clauses. In topological order on the component DAG propagate bit masks recording which terminals reach each component. This computes all conflicts between selected terminals in $O((gd+t)\lceil (3t+1)/w\rceil+t^2)$ word steps on the packed layout. In particular $t=O(\log N)$ costs $O(gd+t^2)$ because $w=\Theta(\log N)$.

Two terminals conflict when one implies the negation of the other, allowing a self-conflict. A choice of one terminal from each ternary clause extends to a satisfying assignment exactly when it contains no conflict. Indeed, if the implication closure of the chosen units contains both $v$ and $\neg v$, two chosen units imply these opposite signs, and contraposition gives a conflict between them. A consistent closed set in a satisfiable implication graph extends by completing complementary components in topological order. This leaves a binary-constraint problem with $t$ variables and at most three options per variable. The deterministic $(3,2)$-CSP algorithm therefore gives $O(gd+t^2+1.3645^t)$ time for $t=O(\log N)$. In particular $t\le\log_{1.3645} N+O(1)$ still fits $O(N)$ time on the explicit layouts, including ASCII parsing. Beigel and Eppstein already give their ternary-clause parameter bound for general formulas. Here the packed implication pass specifies how many such centers can occur before this particular linear-clock guarantee ends. [Beigel and Eppstein](https://arxiv.org/abs/cs/0006046)

The two-layer compiler emitted all four settings for 288 sources, including 15 unsatisfiable sources. Resolution eliminating private pairs followed by DPLL, and an independent CaDiCaL run, agreed on all 1,152 files. Their byte-level checks give Hamming distances $0,1,1,2$ from the base. Lean verifies the finite guard classification, relay cycle, pin and four-center gate. The size bound, global reduction and RAM algorithms are manuscript proofs. Priority for this combined two-layer statement is unestablished. [Lean identities](SheetGuardProjection.lean) · [Compiler and independent solver checks](sheet_guard_deletions_audit.py)
