# The minimum number of variable names for independent lookups in late 3-SAT clauses

Fix positive integers $k,r$. A database consists of $k$ binary tables on $m$ addresses. A query $q=(q_1,\ldots,q_k)$ asks whether all the bits $x_i(q_i)$ are one. Write $V_{k,r}(m)$ for the minimum, over representations, of the maximum number of distinct variable names actually occurring in a database baseline. Each baseline is a proper 3-CNF. Each query is a conjunction of at most $r$ proper ternary clauses, independent of the database. The answer must be $\operatorname{SAT}(B_x\land Q_q)$. There is no uniformity, length bound, or witness-uniqueness assumption in the lower bounds.

**Theorem.** Put $S=\min\{s:\binom{s}{r}\ge m^k\}$. Then for large $m$,
$$
 S-r\ \le\ V_{k,r}(m)\ \le\
 S+O_{k,r}\big(S^{r/(r+1)}+m^{1/3}+\operatorname{polylog}m\big),\qquad
 V_{k,r}(m)=\Theta_{k,r}\big(\max(m^{k/r},m^{1/3})\big).
$$
In particular for $r<3k$ the leading term is $(r!)^{1/r}m^{k/r}$. The construction uses $O_{k,r}(S+m)$ proper clauses. The $m^{1/3}$ floor comes from the information an arbitrary table can encode in a proper 3-CNF even with a large public query alphabet.

## Lower bounds

Databases having a single one in each bank give an identity matrix of order $m^k$. By the [SAT set-pairs bound](how-many-tests-fit-in-the-last-sat-clauses.md), a representation with at most $s$ occurring names in each baseline needs $\binom{s+r}{r}\ge m^k$.

For the second bound hold all but the first bank constantly one. The first bank induces $2^m$ different answer functions. For a fixed query encoding at most $u=3r m^k$ names occur anywhere in the queries. All other names in a baseline of size $s$ can be renamed to the first $s$ of a common private alphabet, since query clauses never refer to them. Choose a list of at most $s$ names from these two alphabets. On the chosen names only $O(s^3)$ distinct signed proper clauses are possible. Repetition and clause order have no semantic effect. Thus
$$
                    m\le O\big(s\log(u+s+2)+s^3+1\big).
$$
For $s\ge m$ the desired lower bound follows directly; for $s<m$, either the cubic term pays a constant fraction of $m$ or $s=\Omega(m/\log m)$. This proves the floor for proper ternary baselines. Headers declaring additional, unused names do not increase the number of answer functions.

The semantic enumeration of Ilinca and Kahn sharpens the constant. With $s$ canonicalized names, only $(1+o(1))2^{s+\\binom{s}{3}}$ different proper 3-CNF **functions** exist. There are $1+(2^m-1)^k$ different answers across all databases: if the Cartesian product of the $k$ one-sets is nonempty, each factor is its coordinate projection. If $s=O(m^{1/3})$ then public-name selection contributes $o(m)$ log-count. Comparing both sides yields $s\\ge (6km)^{1/3}(1-o(1))$. Larger ratios already satisfy this asymptotic lower bound. For $k=1$ and every fixed $r\\ge3$ the constant is attained. Give each address a distinct triple on the smallest palette with at least $m$ triples. For each zero address put its all-negative triple in the baseline. The query pins its own three names true. A model can set every other palette bit false. Thus the worst-case optimum for one table and any such $r$ is $(6m)^{1/3}(1+o(1))$, including the public anchors. [Ilinca and Kahn, *The number of 3-SAT functions*](https://arxiv.org/abs/1005.2861)

## Using a subset as the address

Index the $m^k$ queries by the first $m^k$ distinct $r$-subsets of $\{0,\ldots,S-1\}$ in colexicographic order. Introduce $S$ public flags $y_i$. A query pins exactly the $r$ flags for its set, padding each pin to one proper clause with two public false anchors. We require room for at most $r$ true flags while permitting the database to compute on the chosen set. A circuit making $r$ full independent decoders would use another constant times $S$ names. The following construction makes the extra number sublinear in $S$.

Guess $r$ strictly increasing binary labels $L_1<\cdots<L_r<S$. For every $i$ impose
$$
                 y_i\ \Longrightarrow\ (L_1=i)\lor\cdots\lor(L_r=i).
$$
Split the fixed-length binary encoding of an index into $r+1$ chunks of lengths differing by at most one. For each label and chunk use a shared decoder tree to obtain all flags for its possible values. For each ordered choice $t_1,\ldots,t_r$ of a chunk position for each label, compute the predicate
$$
                    P_{i,t}=\bigvee_{h=1}^r [\,L_{h,t_h}=i_{t_h}\,].
$$
Impose the binary clause $\neg y_i\lor P_{i,t}$ for all choices. A matching whole label satisfies every test. If every label differs from $i$, take one mismatching chunk per label to find a failed test. For fixed $t$ the value of $P_{i,t}$ depends on at most $r$ chunks of the constant index $i$, even though there are $r+1$ chunks. Consequently there are only $O_r(S^{r/(r+1)})$ distinct predicates across all $i$ and $t$. Each OR costs $O_r(1)$ gates after the shared decoders. The guarded clauses cost $O_r(S)$ clauses and **no private name per clause**. If a query pins $r$ flags, its $r$ distinct indices must be exactly the sorted labels.

Compute the colex rank $u=\sum_{j=1}^r\binom{L_j}{j}$. For a set with largest index $a$, there are $\binom{a}{r}$ preceding $r$-sets with smaller largest index; this gives the formula by induction. Reject ranks $u\ge m^k$. Read off the $k$ base-$m$ digits of $u$ as its query coordinates. With $k,r$ fixed these comparisons, products, binomial coefficients and Euclidean divisions have elementary Boolean circuits of $\operatorname{polylog} m$ size using schoolbook arithmetic on $O_{k,r}(\log m)$ bits. They also work for non-power-of-two $m$.

For each bank split its binary coordinate into **three** balanced chunks. Decode all equality flags per chunk with $O(m^{1/3})$ gates. For each address containing zero, forbid its three equality flags from holding together by one negative ternary clause. Separate banks and chunk positions have distinct flag names. Three false anchors fixed by seven clauses convert every pin, binary clause and functional gate constraint into proper ternary clauses after removing tautologies and simplifying constants. For small $m$, handle any empty chunks directly. The query is satisfiable precisely when all addressed bits equal one. Set every unpinned $y_i$ false for the forward witness. This establishes both the stated upper bound and its clause budget.

## Exact polarity comparison for one clause

For $r=1$ and ordinary CNFs allowing units, the worst-case optimum is exactly $m^k-1$. The identity lower bound gives this integer. Conversely use one public flag per entire query, pin false just the flags of rejected queries, and let the final query pin its own flag true. If some query succeeds, at most $m^k-1$ names need pins. If all fail use the empty clause as baseline. For $k=3$ and $m\ge3$, requiring SAT to encode the opposite answer lowers the exact ordinary-CNF optimum to $3m-1$. Both upper bounds transfer to proper 3-CNFs with three extra anchor names. The examples count names before a fixed syntactic query arrives. A SAT RAM may process the original input by any algorithm. Priority for these representation bounds is unestablished. [Opposite-polarity lower bound](how-many-tests-fit-in-the-last-sat-clauses.md) · [Lean guard equivalence](../lean/SharedChunkGuards.lean) · [Finite subset decoder checks](../audits/positive_subset_flags_audit.py) · [Optimal encoded length](encoded-length-of-late-sat-lookups.md)
