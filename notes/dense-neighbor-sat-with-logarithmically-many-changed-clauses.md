# A linear SAT solver near a model fraction of one over log input length

There is a deterministic scalar word-RAM SAT solver with the following guarantee on ordinary width-at-most-three inputs. Let $N$ count encoded bits and put $\lambda=\lceil\log_2(N+2)\rceil$. Suppose a formula $E$ has model fraction $\mu\ge c/\lambda$, for a fixed $c>0$, and all but at most $\lfloor\lambda/4096\rfloor$ clauses of the input $F$ occur in $E$. The solver runs on $F$ in $O_c(N+1)$ time. It receives only $F$. Both verdicts are covered. The bound permits any $r=o(\log N)$ altered clauses for all sufficiently large lengths. We give one absolute constant for the larger edit budget; its value has no optimality claim.

Model fractions refer to the same variable set, extending unused variables freely. Simplify duplicates and tautologies consistently. Multiple sign patterns on a ternary support are retained for solving. At most eight distinct signed clauses use a given support. For counting overlaps let $G$ be the family of unsigned ternary supports of the clauses shared by $F$ and $E$. At most $r$ distinct ternary supports of $F$ are absent from $G$. Write $A_G$ for the event that a uniform random set of vertices avoids containing any edge of $G$. Polarity alignment applied to the shared clauses gives $\Pr(A_G)\ge\mu$. The [sharp transversal inequality](model-density-and-a-transversal-of-ternary-sat-clauses.md) gives $\tau(G)\le\log_{8/7}(1/\mu)$.

## Finding a small set meeting nearly all ternaries

Use the budgets
$$
L=\lceil16\log_2(\lambda+2)\rceil,\qquad R=\lfloor\lambda/4096\rfloor .
$$
For large enough $N$ depending on $c$, there exists a set $T$ of at most $L$ vertices hitting all but at most $R$ distinct ternary supports of $F$: a minimum transversal of $G$ works. Find any such $T$. The procedure need not identify $G$.

A small kernel makes this search economical. For each $0\le d\le3$ put $B_d=(L+R+1)^{3-d}$. Scan the distinct supports and retain a triple unless some subset $S$ of it already belongs to $B_{|S|}$ retained triples. Update the eight subset counts on retention. Every subset count remains below or equal to its cap. There are at most $B_0$ retained triples. Suppose $|T|\le L$ and $T$ misses at most $R$ retained triples. For a proper saturated subset $S$ disjoint from $T$, at most $L B_{|S|+1}$ of its retained supersets meet $T$. At least $(R+1)B_{|S|+1}>R$ would miss $T$. Thus $T$ meets every such $S$ and hits every skipped support. Saturation at a full support can only skip a duplicate; the input to this step already has distinct supports. The partial transversal found on the kernel lifts to the original supports without change. This uses the bounded-superset kernel idea with an explicit allowance for misses. [Fafianie and Kratsch, *A shortcut to (sun)flowers*](https://arxiv.org/abs/1504.08235)

On a remaining kernel triple either choose one of its three variables or mark that triple missed. Stop a branch when either budget is exceeded. Every successful solution is covered by this branching, including a solution that could have hit an earlier voluntarily missed triple. A branch uses at most $L$ variable choices and $R$ misses. The number of internal nodes and leaves is bounded by
$$
\operatorname{poly}(L+R+1)\,3^L\binom{L+R}{L}
=\exp(O((\log\log(N+2))^2)).
$$
For example, count words with $i\le L$ variable choices and $j\le R$ misses by $3^i\binom{i+j}{i}$ and sum. Scanning the whole polylogarithmic kernel per node preserves the last time bound. When the search fails, the solver can use an ordinary complete fallback.

Intern the decimal input names, remove tautologies and compact repeated signed clauses in $O(N)$ word steps. The number $m$ of distinct signed clauses is $O(1+N/\lambda)$: their distinct normalized spellings over a fixed alphabet have total length $O(N)$, so $m\log(m+2)=O(N)$. Only $O(m+1)$ variables occur in these clauses. Stable counting-sort passes on the dense indices deduplicate supports. The eight subset keys of every support can be indexed in one further sort on tuples of at most three of the dense indices, with a length tag. The kernel then uses eight constant-time counter checks per support. These linear scans cost $O(N)$ in total.

## Which variables justify a separate scan?

For each vertex $v\in T$, take a greedy maximal matching in its link graph. An edge of this graph is the pair of other coordinates in a ternary support containing $v$. Write $k_v$ for the number of selected pairs, and $Q_v$ for their $2k_v$ endpoints. Every pair in the link meets $Q_v$ by maximality. All the matchings together take $O(m+1)$ scans of word records: each support occurs on three incidence lists, and timestamp markers let each vertex start with an empty occupied set.

Let $a_v$ count the selected pairs whose originating support is in $G$. Each missing support can cost at most one selected pair at each of its three vertices, so
$$
\sum_{v\in T}(k_v-a_v)\le3r .
$$
Put $J=\{v\in T:a_v\ge L\}$. For $v\in J$, if $v$ is chosen in the random set defining $A_G$, every one of its $L$ disjoint pairs must omit a vertex. Therefore
$$
\mu\le\Pr(A_G)\le 2^{-|J|}+L(3/4)^L .
$$
The first term accounts for avoiding every vertex of $J$. The second is a union bound on $A_G$ occurring together with a selected member of $J$. With the stated $L$, the error is $o(1/\lambda)$. Hence $|J|\le\log_2\lambda+O_c(1)$.

Order $T$ by decreasing $k_v$, and write $D_s$ for its first $s$ vertices. The solver chooses the **smallest** $s$ with
$$
Z_s=\sum_{v\in T\setminus D_s}2k_v\le\lambda/128 .
$$
This is observable, and $s=|T|$ always works. Deleting the $|J|$ largest terms leaves the smallest tail of that length. Comparing with the infeasible-for-the-solver but mathematically defined deletion of $J$ gives
$$
Z_{|J|}\le2(|T|L+3r)\le2L^2+6R\le\lambda/128
$$
for all sufficiently large $N$. Thus $2^s=O_c(\lambda)$ on every promised input. The discarded link entries are paid for by considering each truth assignment to $D_s$ once. The other link entries will contribute to a much smaller compatibility computation.

## One scan per assignment

There are at most $R$ original ternary supports missed by $T$, or $8R$ distinct signed ternary clauses. Fix a truth assignment on $D_s$ and simplify each signed clause once. Keep all binary and unary residuals in a 2-CNF $B$, returning no for this assignment if an empty clause appears. Put the surviving full ternaries from missed supports in a separate list of at most $8R$ clauses.

Every other surviving full ternary contains $v\in T\setminus D_s$ and a neighbor $u\in Q_v$. Assign it to one such ordered pair $(v,u)$. There are at most $Z_s$ recorded pairs, on a set $X$ of at most $2Z_s$ variables. A clause with the two designated literals $\ell,\ell'$ and third literal $t$ puts $t$ in a group indexed by that pair and those two signs. A truth assignment on $X$ requires **all** literals in this group if both $\ell$ and $\ell'$ are false. There are at most $4Z_s$ groups. Variables in $D_s$ can be removed from $X$ since they cannot occur in a surviving full ternary.

The pair for each original support meeting $T$ can be chosen once before the assignments. Give it one incident $v\in T$, group supports by that $v$, and mark all its $Q_v$ entries by timestamps to locate one of the two neighbors in constant time. When any variable of the clause is fixed in $D_s$, the clause cannot remain a full ternary. Group indices for surviving clauses use only the recorded pairs from $T\setminus D_s$. Retain also two singleton groups for each member of $X$, one for each truth value, and singleton groups for the three possible literal choices in each exceptional clause. The total number of groups is at most $8Z_s+24R$, less than one address word in bits at all sufficiently large lengths.

Check $B$ for satisfiability by strongly connected components of its implication graph. For two groups $i,j$, put a conflict if some literal in group $i$ reaches the complement of a literal in group $j$. This includes $i=j$. The union of any selected groups can be imposed on $B$ if and only if their conflict submatrix is empty. Indeed, close their literals under implication. A complementary pair in this closure makes one initially selected literal reach the opposite of another by contraposition. A consistent implication closure extends to a model of $B$. Every clause touching its fixed truth values is already satisfied, and any original model of $B$ serves on the untouched variables. [Implication criterion and its formal semantic counterpart](three-valued-choices-for-the-missing-radius-three-assignments.md) · [Aspvall, Plass and Tarjan](https://collaborate.princeton.edu/en/publications/a-linear-time-algorithm-for-testing-the-truth-of-certain-quantifi/)

For every literal $t$ requested by group $j$, mark the component of $\neg t$ with bit $j$. Propagate the word of marks in reverse topological order on the component DAG. OR the propagated words at the components of all $t$ in group $i$ to obtain its row of the conflict matrix. Include grouped variables absent from $B$ as isolated literal vertices so that opposite requests still conflict along a path of length zero. There are $O(m+1)$ group entries and data vertices apart from $O(\lambda)$ auxiliary indices. This scan and the SCC computation take $O(m+\lambda+1)$ word steps.

Finally enumerate assignments on $X$ and one chosen true literal per exceptional clause. Select their singleton groups and the required signed-pair groups, and check the selected rows for conflicts. This decides the branch exactly: every model supplies such a choice, and the compatibility test extends any successful choice to a model. There are at most $2^{2Z_s}3^{8R}$ possibilities. Because $Z_s\le\lambda/128$ and $R\le\lambda/4096$, even a polynomial in $\lambda$ per possibility costs $O((N+1)^{1/3})$ for all sufficiently large $N$.

The running time on a promised file is therefore bounded by
$$
O\!\left(N+\exp(O((\log\log(N+2))^2))
+2^s\big(m+(N+1)^{1/3}\big)\right)=O_c(N+1).
$$
Use a complete solver on arbitrary-width files and on failures of the preliminary search. The widely separated numerical constants allow the solver to handle finitely many small lengths directly. Unknown $c$, the actual edit count, the neighbor $E$, and its assignments play no role in the algorithm. This is a sufficient fast regime and leaves the time for general SAT open.

## Verification

The [finite audit](../audits/dense_neighbor_link_matching.py) checks partial-transversal lifting, the link matching covering property, the tail charge for deleted supports, and the signed group solver on small instances against truth tables. The [majority extension proof](../lean/ThreeValuedDefectChoices.lean) verifies the semantic step used in the group solver. The density, encoding and full RAM bounds above use mathematical arguments.
