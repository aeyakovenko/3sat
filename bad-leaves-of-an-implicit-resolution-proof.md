# Testing two bad leaves in an implicit resolution refutation

Fix $v\ge3$. One proof template for a public eight-clause contradiction can have **exactly the satisfying assignments of an arbitrary source CNF as its invalid inferences**. The refutation uses a full binary resolution tree with leaf weakening. Only one bit in the choice of a leaf's axiom depends on the source. Under the promise of at most two invalid leaves, there are three exact costs for identifying a valid proof.

| Information available | Query model | Worst-case cost |
|---|---|---|
| One complete proof line at a time | Deterministic, exact | $2^v$ line queries |
| Exact multilinear extension of the invalid-leaf indicator over $\mathbb F_4$ | Deterministic, exact, adaptive points allowed | $v$ field evaluations |
| The same extension | Randomized, error at most $1/3$ on every input | One field evaluation |

The field oracle evaluates a sum over assignments. Giving it unit cost changes the access model. With the succinct description in ordinary RAM memory, testing this template for invalidity is precisely the source SAT decision, including its promise. The public eight clauses themselves have a constant-size refutation. Krajíček's Lemma 4.1 already constructs succinct descriptions of full exponential tree-like resolution proofs and distinguishes their descriptions from proofs of their correctness. No priority is asserted here for that construction. [Krajíček, *Implicit proofs*, Lemma 4.1](https://www2.karlin.mff.cuni.cz/~krajicek/implicit.pdf)

## One axiom pointer per assignment

Let the public target contain the eight clauses $B_u$, $u\in\{0,1\}^3$, where $B_u$ is the unique clause on variables 1, 2 and 3 falsified by $u$. For a prefix $p$ of an assignment, label its tree node with the disjunction of the literals falsified by that prefix, one per assigned variable. The root clause is empty. Resolving the two children on the next variable yields the parent, regardless of any leaf pointer. Every branch uses the same variable order and resolves each variable once. If a calculus requires every weakening variable to occur in a target axiom, use the public target $B_v$ obtained by appending $(x_i\lor x_1\lor x_2)$ for $4\le i\le v$. These extra rows occur in no inference and the same $B_v$ works for every source at dimension $v$.

At a complete assignment $a$ the leaf claims to weaken

$$
B_{(a_1\mathbin{\rm XOR} F(a),\,a_2,\,a_3)}
$$

to its full assignment-blocking clause. The weakening is valid iff $F(a)=0$. When $F(a)=1$ its first literal is true at $a$, whereas every literal in the proposed conclusion is false there. Two source formulas give proof tables differing in exactly one pointer bit at each assignment in the symmetric difference of their model sets. There are no other changed bits in this representation. The [Lean file](ImplicitResolutionLeaves.lean) verifies the leaf criterion, local resolution schema, failed-leaf filter and pointer identity.

For dense proper DIMACS with $v$ occurring names, the pointer description can be the original file itself under a fixed interpreter. That interpreter evaluates the CNF on a supplied leaf assignment and changes the first pointer bit as above. Validity and satisfiability on this representation have opposite answers on the **same bytes**, with the same number of solutions and errors. An explicit Boolean expression for the pointer consists of one copy of the CNF and constant-size output logic. On a real word RAM, an algorithm can examine that expression's syntax and exploit its entire structure. For a distinct source of restrictions, general transfer of a proof-length lower bound to a SAT algorithm requires a suitable short soundness proof in the designated system. [Krajíček, *A note on SAT algorithms and proof complexity*, Theorem 2.1](https://www1.karlin.mff.cuni.cz/~krajicek/sat.pdf) · [Earlier reflection audit](certificate-reflection.md)

Every singleton or pair of distinct Boolean assignments can occur as the model set of a proper 3-CNF on these same $v$ variables. For a singleton, pin each coordinate. For a pair, pin equal coordinates and choose a representative among the differing ones. Require every other differing coordinate to agree or disagree with the representative as on the first assignment. These binary equivalences leave exactly the pair. A unit or binary clause becomes an equivalent conjunction of four or two proper ternaries, respectively, by adjoining all sign patterns on existing names outside that clause. This preserves the entire assignment domain and uses $O(v)$ clauses.

## The local query calculation

A local query names a single line of the implicit refutation and learns the line and its pointer. All other access to the source-dependent code is excluded in this model. Internal lines are public. An unqueried leaf can be the unique bad one, so a deterministic verifier must inspect every leaf on the valid execution. Reading them all suffices.

More generally, for the promise of zero or exactly $s$ bad leaves, put $U=2^v$. In the line oracle model, allowing any chosen $s$-subset, the optimal worst-case success probability using at most $q\le U$ queries is

$$
  \frac{1}{1+\binom{U-q}{s}/\binom{U}{s}}.
$$

Choose a uniform $q$-subset, report invalid on a hit, and otherwise report valid with the displayed probability. Conversely let $a$ be the probability of reporting valid on the actual valid oracle. For each random tape that does so, a uniformly random $s$-subset misses all probes made on the valid path with probability at least $z=\binom{U-q}{s}/\binom{U}{s}$. The answers on that event reproduce the valid transcript exactly. Worst-case success is therefore at most $\min(a,1-az)$. Optimizing gives the formula. For $s=1$, success $2/3$ requires and is attained by $q=\lceil U/2\rceil$. The singleton and pair realizations above use proper 3-CNF. For arbitrary $s$, a Boolean selector can list $s$ assignments in $O(sv)$ gates.

## Exact field queries for two bad leaves

For the bad set $S$ let

$$
  P_S(z)=\sum_{a\in S}\prod_{i:a_i=1}z_i\prod_{i:a_i=0}(1-z_i).
$$

In a field of odd characteristic the single midpoint evaluation $P_S(1/2,\ldots,1/2)=2^{-v}|S|$ distinguishes zero, one and two elements. In $\mathbb F_4=\{0,1,\omega,\omega^2\}$ there is a different exact answer. For an interior query $z\in\{\omega,\omega^2\}^v$, the contribution of one assignment is

$$
  C_z\omega^{r\cdot a},\qquad
  C_z=\prod_i(1-z_i)\ne0,
  \qquad \omega^{r_i}=z_i/(1-z_i),\quad r_i\in\{1,-1\}\subset\mathbb F_3.
$$

Both signs can be chosen independently. In characteristic two, the two contributions for $a,b$ cancel exactly if $r\cdot(a-b)=0$ in $\mathbb F_3$. Use $v$ interior points whose rows consist of the all-ones row and its $v-1$ single-sign changes in the first $v-1$ coordinates. Subtracting the all-ones row gives nonzero multiples of the first $v-1$ unit vectors. The rows span all of $\mathbb F_3^v$. At least one evaluation detects any distinct pair. Every singleton is detected at every one of these points.

For the lower bound, take the $q<v$ queries on the all-zero transcript of an adaptive deterministic tester. Start with the whole Boolean cube of possible singleton assignments. Whenever an active query has a $0$ or $1$ in a remaining free coordinate, fix the corresponding assignment bit to its opposite. That query's singleton contribution vanishes identically throughout the subcube, and it can be removed. Remove all queries killed by the restriction. Each such fixing removes one variable and at least one query. At the end there are $v'>0$ free coordinates and $q'<v'$ surviving rows, all interior on the free coordinates. Fixed coordinates of any surviving row contribute a nonzero constant common to all remaining assignments. There is a nonzero $h\in\mathbb F_3^{v'}$ in the kernel of the $q'$ rows. Every ternary vector is a difference of Boolean vectors, coordinate by coordinate using $(1,0)$ for $1$ and $(0,1)$ for $-1$. Extending that distinct pair by the fixed bits gives two bad leaves invisible at **every** queried point. They reproduce the all-zero execution, proving the lower bound even with unrestricted boundary evaluations.

Randomization changes the answer. Independently choose each interior sign uniformly. For a pair $a\ne b$, condition on all signs except one at a differing coordinate. At most one choice of that sign can cancel the pair, so a nonzero evaluation occurs with probability at least $1/2$. Report invalid when the answer is nonzero. On zero, report valid with probability $2/3$. This achieves the stated success on every promised set. With no query the two verdicts cannot both receive probability $2/3$.

The [finite arithmetic audit](implicit_leaf_field_audit.py) multiplies explicitly in $\mathbb F_2[X]/(X^2+X+1)$. Through $v=4$ it checks every $(v-1)$-element query set, including 2,763,520 sets at $v=4$. Each leaves an undetected pair. It verifies the spanning upper tests and the random cancellation estimate directly, and checks 2,780 proper 3-CNFs on three through six variables against their actual sets of invalid leaf weakenings.

Knowing that the interpolation oracle exists as a mathematical function does not construct it from a succinct verifier. Even the odd-characteristic midpoint on a proper two-model-promise CNF already decides that promise problem. On Boolean points, evaluating the source expression directly verifies one leaf at a time. Treating an ordinary arithmetization of the expression as the evaluated multilinear extension would invalidate the field-query argument. [Earlier SAT interpolation audit](sat-extension.md)
