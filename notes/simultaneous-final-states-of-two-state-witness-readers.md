# Counting shared witnesses for several two-state readers

Fix $r$ deterministic machines with states 0 and 1, prescribed initial states, and a common $v$-bit witness. Reader $i$ has an ordered list of $L_i$ rows. Each row names one witness bit and gives the next state as a function of that bit and the old state. Names may repeat within and between lists, in any order. Once the public input is fixed, the named bit at each row is independent of the state and witness.

**Theorem.** The exact number of witnesses ending in each of the $2^r$ possible final-state vectors can be computed in

$$
 O_r\!\left(1+v+\prod_{i=1}^r(L_i+1)\right)
$$

word operations, using $O_r(1+v+\sum_i L_i)$ words. A word holds a name, a row index, or an integer through $v+\sum_i L_i+1$. The result includes witnesses differing only on unused names. Output counts are written in binary.

### Partition by last reset

For a fixed value $b$ of its named bit, a row's transition is either a constant $c(b)$ or a permutation $s\mapsto s\oplus p(b)$. Call a constant a reset. For each reader, an assignment has a unique last reset or none. Once the last reset is chosen, each later row must be a permutation, the chosen row must reset, and earlier rows impose no condition. The final state is the XOR of the later flips with the chosen reset value, or with the initial state if no reset occurred.

For every name $x$ and each $b\in\{0,1\}$, maintain a disallowed flag or a vector $u_{x,b}\in\mathbb F_2^r$. Initially both vectors are zero. Scan the current reader backwards. At a row naming $x$, recurse to the next reader with only the allowed reset values of $b$ and add $c(b)$ to the current coordinate of their vectors. Restore the old pair, retain only permutation values, add their $p(b)$ in that coordinate, and continue scanning. Reaching the start adds the initial state to a separate offset and starts the next reader. Restore a reader's pair changes in reverse order when its sweep returns. Every update acts on the same pair for $x$, even when several readers or rows consult it. If neither value is allowed for a name, discard the branch.

At a leaf choose a base value for each name from its allowed set, and let $z$ be their vector sum plus the offset. Let $f$ be the number of names with both values allowed. Their difference vectors are $u_{x,0}\oplus u_{x,1}$. If their span is $D$ of dimension $e$, each vector of $z+D$ receives exactly $2^{f-e}$ witnesses. This is rank–nullity for the map from the $f$ independent choices to the output. Each witness belongs to exactly one last-reset profile.

### Native cost and output length

Maintain the base sum, the number of impossible names, $f$, and the multiplicity of each of the $2^r$ difference vectors. Updating or restoring a pair takes $O_r(1)$ operations. At a feasible leaf rebuild the span from the differences of positive multiplicity, in $O_r(1)$ time. Write $J=\prod_i(L_i+1)$. The total number of row visits, including infeasible sweeps, is at most $\sum_j L_j\prod_{i<j}(L_i+1)=J-1$. There are at most $J$ leaves. At any instant undo stacks contain at most $\sum_i L_i$ pairs.

For each output vector keep a histogram of contributions by exponent $f-e$ and increment a single small counter per contribution. A histogram bin never exceeds $J$. Since $\log(J+1)=O_r(\log(v+\sum L_i+2))$, each bin and each carry needs $O_r(1)$ words. Propagating carries once at the end costs $O_r(v+1)$ operations across all outputs. This avoids adding a $v$-bit number at every leaf.

For an $N$-bit file from which all the lists can be obtained in $E$ operations, add $E$ to the bound. For $v+\sum_i L_i=O(N)$ and $E=O(N)$, two readers cost $O(N^2)$ and three cost $O(N^3)$, including exact counts. A succinct description may expand to many more rows than its encoded length. The product bound then uses the expanded list lengths. If the declared witness range has many unused names, one may densely rename the $v'$ occurring names, count on those, and return the common factor $2^{v-v'}$ separately. On explicit strings, a fixed-alphabet trie can do this renaming in time linear in the total identifier length, after removing any syntactic leading zeroes. Writing every zero of a binary count still incurs its output cost.

### Checkpoints and SAT

Prescribing intermediate states cuts each list into readers with known start and end states. With arbitrarily many checkpoints even a single reader can encode every 3-CNF parsimoniously. Concatenate the three literal tests of each clause. Its first row overwrites the state with the first literal's value, the other two take OR with their literal, and the clause end must be 1. Equivalently, use one three-row reader per clause with all final states required to be 1. Witness names and signs come directly from the source clauses. Thus the fixed-$r$ exponent cannot be applied to this unrestricted encoding.

State-dependent choices of variable name give a different model. For example, in a general width-two branching program the two nodes of a level may name different variables. Such a level need not have a last-reset description in terms of a single bit. [Makita et al., *A Satisfiability Algorithm for Deterministic Width-2 Branching Programs*](https://doi.org/10.1587/transfun.2021EAP1120).

The standard-library audit compares every output count with direct assignment enumeration on 4,356 pairs of empty or single-row readers, 20,480 triples of single-row tables up to name coincidence (at one fixed start vector), and 900 random cases with repeated names and up to five readers. A 1,000-bit rank-two example checks the large-count path. Run `python several_two_state_reader_counts.py`. [Counting implementation and audit](../audits/several_two_state_reader_counts.py).
