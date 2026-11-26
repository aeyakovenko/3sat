# Counting models of proper 3-CNF and witnesses to a binary matrix product

## Exact minimum for ordinary proper 3-CNF

Fix an ambient set of $v\ge3$ Boolean variables. Each clause has exactly three distinct variables. Among satisfiable formulas of at most $m$ such clauses, the exact smallest number of models on those $v$ variables is

$$
\begin{cases}
(8-m)2^{v-3}, & 0\le m\le7,\\
2^{\max(0,v-m+4)}, & m\ge7.
\end{cases}
$$

Unused ambient variables count toward the model count. The inequality applies in particular when all $v$ variables must occur. The extremizers for the ambient version can leave variables unused. For example, two clauses covering six occurring variables have disjoint supports and give 49 models, while the ambient six-variable minimum is 48.

A clause forbids one coordinate flat of codimension three. The prescribed-dimensions covering theorem gives the lower bound. Its extremizers are already coordinate flats, so ordinary clauses attain the minimum. Up to seven clauses, exclude distinct patterns on one triple. After seven clauses that triple is fixed. Use each further clause to exclude value one on a new variable when two already fixed variables take their fixed values. Each step halves the remaining cube until one assignment remains. In particular, leaving at least one and at most two assignments requires exactly $v+3$ clauses at minimum, including $v=3$. The singleton threshold $m=v+4$ for proper ternary clauses is the binary codimension-three case of Jamison's punctured-space theorem, including attainment by coordinate flats. [All clause budgets and the finite-field proof](minimum-uncovered-binary-assignments.md) · [Jamison, Theorem 2](https://doi.org/10.1016/0097-3165(77)90001-2)

For a prescribed list of clause widths between one and $v$, use the dimension $v-k$ for a width-$k$ clause in the same covering theorem. The greedy computation there gives the exact minimum on the ambient variables even for mixed widths. It permits repeated rows. This answers a question about the number of possible witnesses given satisfiability. It does not determine whether a given formula has a witness.

## A sharp minimum when clauses arrive two at a time

Start with no variables. Each nonempty batch adds one or two proper ternary clauses and uses at most two variables already occurring in earlier batches. Let $v$ now count **occurring** variables. A pair on the same triple excludes at most two points in its three coordinates. Two distinct excluded points form an affine line over the binary field and therefore give one forbidden flat of codimension two on all variables. Count a singleton or a repeated clause as one codimension-three flat. For rows on different triples keep their two separate codimension-three flats. Let $r$ be the number of resulting flats, adding their contributions batch by batch.

If a batch uses $a_i$ old variables, its number of new variables minus its number of flats is at least $2-a_i$. For a single triple this difference is $(3-a_i)-1$. Two distinct supports use at least four variables and at most two flats. Thus $v-r\ge\sum_i(2-a_i)\ge2$ on every nonempty history.

* At $r=1$, the formula has just three occurring variables. One distinct clause gives seven models and two distinct clauses give six.
* At $r\ge2$, the binary codimension-two theorem gives at least $2^{v-r+1}\ge8$ whenever the formula is satisfiable. Flats of codimension three can be enlarged to codimension two while avoiding a fixed model for purposes of this lower bound.
* Eight is attained by two nonempty batches. The first consists of the two proper clauses padding $(\neg A\vee y)$ with opposite signs of a new bit $h_1$. The second pads $(\neg A\vee\neg y)$ with a new $h_2$. The conjunction forces $A=0$, and $y,h_1,h_2$ remain free.

Consequently six is the exact nonempty minimum, and any satisfiable formula requiring more than one batch has at least eight models. On the class with the extra promise of at most seven models, it suffices to check the empty conjunction and the one-triple case. At a promise of at most five models only the empty conjunction can be satisfiable. [Recognition, semantic reductions, affine spaces through each model and finite audits](one-or-two-old-variables-in-clause-batches.md)

This promise statement also distinguishes two different computational tasks. Suppose a **globally correct** deterministic SAT solver runs in $O(N^k)$ on all the at-most-five-model files of the class. All unsatisfiable outputs of the linear-time, linear-length two-clause reduction belong to that promise. On an arbitrary proper source formula, run that reduction and simulate the solver up to its fixed bound. Reject on a timely rejection and accept otherwise. Every negative file receives a timely rejection, and a true file can never be rejected by the solver. This decides full proper 3-SAT in $O(N^k)$ for $k\ge1$. Conversely a full solver at that clock has the asserted restricted speed. Thus even the easy promise verdict gives no globally safe fast rule on the negative files without resolving the same SAT clock. [Reduction and encoded-length accounting](one-or-two-old-variables-in-clause-batches.md) · [Negative deadlines on another family](witness-dependent-charges-and-the-negative-sat-clock.md)

## The number of extensions above each fixed boundary input

Let a gadget start with $b$ external input bits already available. Count them as old even before their first appearance in a clause. A batch may use at most two old bits **in total**, including old private bits. Let $t$ count all newly introduced private bits, and let $r$ count forbidden flats as before. The same accounting gives $t-r\ge\sum_i(2-a_i)\ge0$. The gadget accepts a boundary value $z$ if it has any extension on its private bits. Denote this projected relation by $P$.

For $z\in P$ let $\ell(P,z)$ be the maximum dimension of a binary affine space through $z$ contained entirely in $P$. Then the fiber over $z$ contains an affine space of private assignments of dimension at least

$$ b+t-r-\ell(P,z). $$

Indeed fix an accepting assignment $s$ extending $z$. For each forbidden affine flat choose a hyperplane through $s$ missing that flat. Such a hyperplane exists by taking a defining linear functional of the flat on which $s$ violates the defining equation. Intersect these $r$ hyperplanes. The resulting affine space contains $s$, satisfies all clauses and has dimension at least $b+t-r$. Its projection lies in $P$ and passes through $z$. Rank-nullity bounds the dimension lost when taking the fiber over $z$ by $\ell(P,z)$. This is a pointwise bound. An arbitrary choice of initial satisfying assignment gives the claimed subspace through that very assignment.

Take $P$ to be the graph $C=AB$ for binary $d$-square matrices over $\mathbb F_2$, with all $3d^2$ entries external. Then $\ell(P,z)=d^2$ at **every** point. Projection onto $(A,B)$ is injective on the graph. On the resulting direction subspace $L$, the output $C$ is affine. Its trace therefore has zero second difference. For any $(X,Y),(X',Y')\in L$ that difference equals

$$ \operatorname{tr}(XY'+X'Y). $$

This is a nondegenerate alternating bilinear form on the $2d^2$-dimensional space of input directions. A nonzero entry of $X$ can be paired against a single transposed entry of $Y'$, and a nonzero entry of $Y$ against one of $X'$. Since $L$ is contained in its orthogonal complement, its dimension is at most $d^2$. Keeping $B$ fixed and varying $A$ gives an affine graph of dimension $d^2$ through the target point, proving equality.

Every valid product therefore has **at least $2^{2d^2+t-r}\ge2^{2d^2}$ distinct private witnesses** in any such exact verifier.

Two valid products together give a stronger bound above each one. Fix any accepting lift $s$ of $(A,B,AB)$ and any lift $s'$ of $(A+I,B+I,(A+I)(B+I))$. For each forbidden flat there is a single hyperplane through both lifts that avoids it. In the quotient by the flat's direction, translate its forbidden value to zero. The two lift images are nonzero. Over $\mathbb F_2$ they are equal or independent, so one linear functional can take value one on both. Pull that fiber back and intersect the $r$ hyperplanes. Again their intersection has dimension at least $3d^2+t-r$.

The projection of this affine space onto the product graph contains both prescribed boundary points. The input direction $(I,I)$ therefore lies in its direction space. Taking the **matrix-valued** second difference with another direction $(X,Y)$ gives $XI+IY=0$, hence $X=Y$. Polarizing any further two directions $(X,X),(X',X')$ gives $XX'=X'X$. The linear space of possible $X$ consists of pairwise commuting matrices. It generates a commutative matrix algebra, of dimension at most $\lfloor d^2/4\rfloor+1$ by the Schur–Jacobson theorem. This upper bound for the affine dimension through the two boundary points is attained by taking $X$ to be scalar matrices plus matrices supported in a fixed rectangular upper-right block of size $\lfloor d/2\rfloor$ by $\lceil d/2\rceil$. The resulting space contains $I$, and squaring is additive on it over $\mathbb F_2$, so the output product varies affinely. [Jacobson, *Schur's theorems on commutative matrices*, Theorems 1 and 2](https://doi.org/10.1090/S0002-9904-1944-08169-X)

Rank-nullity on the original fiber now forces at least

$$ 2^{\,3d^2+t-r-\lfloor d^2/4\rfloor-1} $$

private assignments for **each** valid product, and an affine space of this size through each accepting lift. Since there are only $2^t$ private assignments available, the same reasoning gives $r\ge3d^2-\lfloor d^2/4\rfloor-1$ in any existential verifier expressed as a conjunction of complements of $r$ binary affine flats. This last inequality does not require a batch order. The per-fiber exponential estimate independent of $t,r$ uses $t\ge r$ from the two-clause growth rule.

The construction rule permits arbitrary reuse of old bits across different batches and imposes no bound on total workspace. It constrains each batch. Three proper clauses per batch permit a parsimonious simulation via the false-anchor construction, including external pinned occurrences linked to internal copies. Arbitrary tensor networks can cancel contributions, and the number of possible witnesses supplies no lower bound on their unrestricted volume. [Three-clause construction](one-or-two-old-variables-in-clause-batches.md) · [Unrestricted bit-network question](balanced-cuts-of-the-binary-product-graph.md)

## Exact modular answers with exponentially many witnesses

The witness bound has a control in the same batch model. For **every fixed integer $M\ge2$**, there is a linear-size two-old, two-clause transformation preserving the number of extensions **modulo $M$ at each external input**. Thus an ordinary Boolean circuit verifying a product, with a unique evaluation on each input, still gives a two-clause verifier with the exact zero-one graph tensor in any chosen positive characteristic.

Begin with the occurrence-copy construction. Each proper source clause is put on its own three fresh variables. Impose consistency between occurrences of each source variable by a chain of binary clauses expressing equality. If its value is an external input, include that external variable as one endpoint in the chain. Each legal source assignment now has one choice of the occurrence bits. To impose each binary clause $(u\vee v)$, use the complementary ternary pair with a fresh pad $z$. A false binary clause has no extensions, and a true clause leaves $z$ free.

For parity alone, attach a single additional proper clause $(z\vee p\vee q)$ on two fresh bits. There are three choices at $z=0$ and four at $z=1$, hence **seven** extensions for every satisfied binary clause. Every legal source assignment contributes an odd number, even when the verifier as a whole is forced to have exponentially many witnesses. Two old independent slack pads can also be grouped together with a single fresh bit in one proper clause, again giving seven choices.

For general $M$, take $a=\varphi(M)$ and attach $a$ clauses $(z\vee p_j\vee q_j)$ with fresh disjoint pairs. The contribution for a satisfied binary clause is $g=3^a+4^a$. This integer is coprime to $M$. It is odd and is one modulo three. For each prime $p\ge5$ dividing $M$, the number $p-1$ divides $\varphi(M)$, so $3^a$ and $4^a$ are both one modulo $p$. Finally impose the same binary clause using $a$ independent copies of this gadget. It contributes $g^a=1\pmod M$ if satisfied and zero otherwise. All petals share only their own pad with the preceding formula, every required pair of endpoints is distinct, and $a$ is constant for fixed $M$. The total number of records stays linear. The normalization and fresh-name accounting for the underlying source reduction give linear encoded output for ordinary proper input.

For a Boolean circuit, impose the usual functional gate constraints and pin acceptance. Fixed zero anchor bits turn short clauses into proper ternary clauses without witness ambiguity: three fresh bits and seven clauses pin a unique triple to zero. Simplify repeats or tautologies before padding and use distinct anchors within each clause. Then apply the modular construction. The number of true gate evaluations is exactly one on a valid exterior input and zero otherwise. Summing the unweighted accepting extensions over a field of characteristic $p$ gives the right graph entry by taking $M=p$. This includes the matrix product relation, with size proportional in records to the size of the chosen Boolean verifier and its external interface. For characteristic zero there is also a signed construction that works uniformly over **every** field. Use the single petal on each pad and give its $z=0$ configurations weight $-1$ and its $z=1$ configurations weight $+1$. For a true binary clause the contraction is $-3+4=1$ over the integers. A false one still contributes zero. These are nonzero unary weights, so all seven extensions still occur. Multiplying the local factors preserves the exact original count over the integers and after reduction to any field. A tensor implementation can use an explicit tree of binary copying constraints for every multiply used bit, with linear total size in the number of occurrences. Thus even an exponential lower bound on accepting extensions through every valid product is compatible with an exact signed contraction of the correct graph.

[Lean](TwoProductBoundaryLifts.lean) verifies the translated four-point polarization identity for arbitrary-length binary dot products and the commutation step; its identity-shift lemma takes the two matrix unit laws as hypotheses. The dimension bounds, gadget count and RAM arguments are manuscript proofs. The [finite audit](clause_batch_overlap_audit.py) also enumerates the affine spaces through all 260 prescribed product pairs at matrix sides one and two.

The formula-size and gate questions use different parameters from model counts. None of these arguments makes an unconditional time claim about an unrestricted SAT solver. Publication priority for the finite-budget formulation and the gadget applications has not been established.
