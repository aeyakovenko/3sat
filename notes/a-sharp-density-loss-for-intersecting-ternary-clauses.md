# A sharp density loss when ternary clauses overlap

For a proper ternary clause, its support is its set of three variable names, ignoring signs. Let $\tau$ be the minimum number of names that meet all the ternary supports of a CNF. Select $p$ pairs of distinct intersecting ternary supports, with no name used by two selected pairs. Set $q=7/8$ and $\beta=46/49$. The fraction $\mu$ of assignments satisfying the CNF obeys
$$
                  \mu\le q^\tau\beta^p .
$$
Both constants are sharp. In particular, even a single intersecting pair loses at least a $3/49$ fraction of the transversal bound. If $\mu> (46/49)q^\tau$, the distinct ternary supports must be pairwise disjoint. At equality intersecting supports are possible.

## The two possible intersections

Discard clauses outside the chosen width-three family and align all signs to the negative polarity. Alignment keeps the supports and cannot decrease the model count. In a fiber fixing all other variables, simultaneous demands that one variable take opposite values become a single demand; a single demand still permits one value. We work with independent, uniform bits, where zero satisfies the corresponding literal. The [transversal density bound](model-density-and-a-transversal-of-ternary-sat-clauses.md) bounds the density of a rank-at-most-three residual by $q^{\tau_{\rm res}}$. The classical matching bound for independence density is due to Bonato and coauthors. Historical priority for the pair refinement and its extremizer is unestablished. [Bonato et al., *Independence densities of hypergraphs*](https://arxiv.org/abs/1308.2837)

Take a selected pair with $t=1$ or $2$ common names. Read its common bits until a zero is found. If successful, both clauses are satisfied and we exposed one zero. If all common bits are one, read each private group until its first zero. Both groups must succeed, and on success two zeroes were exposed. Stop reading each group at its first zero. All unread bits remain independent. Any transversal of the residual clauses together with these $z$ exposed zeroes meets every original support. Thus $\tau_{\rm res}\ge\tau-z$; an empty residual clause gives zero acceptance. Every other selected pair is untouched.

On each successful branch induction on the number of pairs bounds its conditional acceptance by $q^{\tau-z}\beta^{p-1}$. The expected multiplier from this pair, after factoring out $q^\tau$, is
$$
 \frac{1-2^{-t}}{q}
      +\frac{2^{-t}(1-2^{-(3-t)})^2}{q^2}
      =\frac{46}{49}.
$$
The identity holds at both possible intersections. The base with no remaining pairs is the transversal inequality. This proof also applies when several sign patterns appear on a support.

For sharpness take the all-negative triples on $\{a,b,u\}$, $\{a,b,z\}$ and $\{u,z,t\}$. No single name hits all three, and $\{a,u\}$ does. If $a,b$ are not both one, the last triple contributes probability $7/8$. Otherwise $u=z=0$ is necessary and sufficient. The resulting density is $23/32=q^2\beta$. Disjoint copies of this gadget and isolated triples give equality for every $p\ge0$ and $\tau\ge2p$. For density near $q^\tau$, a maximal packing gives a stability statement: deleting its at most $5p$ names and their incident supports leaves a matching, and $p\le\log(q^\tau/\mu)/\log(49/46)$.

## Consequence for a solver given only the edited formula

Suppose a hidden CNF $E$ has model fraction $\mu>0$ and all but at most $r$ clauses of a width-at-most-three file $F$ occur in $E$. Consistently remove tautologies and repeated literals first. Use densities on the union of the variable sets. If $F$ has parameters $\tau,p$, the shared ternaries have a transversal of size at least $\tau-r$ and retain at least $p-r$ of the selected pairs. Hence
$$
 \mu\le q^{\max(0,\tau-r)}\beta^{\max(0,p-r)}.
$$
For fixed $r$, define
$$
 A=\log_2(8/7),\quad B=\log_2(49/46),\quad
 D=\log_2 25,\quad \theta=A+B/D=0.2122727\ldots .
$$
There is a single globally correct deterministic word-RAM solver with the following bounds. For $h=1,2,3$ it takes $O(N^h)$ time on $F$ if
$$
 \mu\ge c\big((N+1)^{h-1}\log_2(N+2)\big)^{-\theta}
$$
for fixed $c>0$. It receives neither the neighboring file nor any of these parameters. For linear time the [partial-transversal algorithm](dense-neighbor-sat-with-logarithmically-many-changed-clauses.md) gives a larger sufficient range.

To prove the time bounds denote $\log_2((N+1)^{h-1}\log_2(N+2))$ by $L$. Intern and deduplicate in $O(N)$ time to obtain $m=O(1+N/\log(N+2))$ distinct clauses. Work on two solver procedures in parallel by alternating their steps, using separate memory. The first finds a minimum transversal and branches on it. The estimates for its search and 2-SAT calls in the [transversal algorithm](model-density-and-a-transversal-of-ternary-sat-clauses.md) give $O(N^h)$ when $\tau\le L+O(1)$.

The second procedure finds a maximal collection of mutually vertex-disjoint pairs as above. One pass over the remaining distinct supports detects a repeated variable and produces two intersecting supports, or certifies that the remaining supports form a matching. Remove every support touching the selected pair and repeat. Timestamped arrays make the cost $O((p+1)m)$. Branch on assignments of all variables of the selected pairs, enumerating just patterns satisfying one selected signed clause on each support of a pair. If the pair shares one variable, at most 25 of 32 patterns survive; if it shares two, at most 13 of 16 survive. Opposite signs on a shared variable can only reduce those numbers. There are at most $25^p$ branches. Local constant-radix enumeration lists them in $O(25^p(p+1))$ time.

The unhit supports are disjoint, and their number is at most $\tau$. To handle all possible signs, split them into $a$ supports forbidding one or two of their eight patterns and $b$ supports forbidding three or more. An $a$-support's allowed set is a union of at most three subcubes. For one forbidden pattern, pick a satisfying literal. For two adjacent forbidden corners their union is an edge, so its complement needs only two terms. For two forbidden corners at distance two, their shared coordinate gives one term; in the other half exactly two opposite choices on the other two bits work. For antipodal corners, complement coordinates to make them 000 and 111; a cyclic transition from 1 to 0 characterizes the six other rows, using three terms. Any $b$-support has at most four subcubes: partition the three-cube into four parallel edges and retain the allowed part of each. An empty allowed set rejects immediately.

On each outer branch the remaining binary clauses form a 2-CNF. Project it to the literals of the unhit supports using strongly connected components and a pass over their acyclic graph with one bit per marked literal. A set of required literals extends to a binary-core model iff every singleton and pair does, provided the core is satisfiable. Thus a subcube choice requiring several literals has unary and pair conflicts only. The projection costs $O(m(1+\tau/w)+\operatorname{poly}(\tau))$ word steps at word width $w=\Theta(\log N)$. Split each four-way choice into two groups of size at most two. Each of the resulting at most $2^b$ subproblems has only $a$ three-valued choices. The other choices are Boolean, so their conflict constraints form a 2-CNF. An option at a three-valued site imposes units on that Boolean core. Project away the Boolean choices by the same pair test. Eppstein's deterministic algorithm on the remaining binary-constraint instance gives total time $2^b\,1.3645^a\operatorname{poly}(\tau+1)$ after the first projection. [Projection proof](three-valued-choices-for-the-missing-radius-three-assignments.md) · [Eppstein, *Improved Algorithms for 3-Coloring, 3-Edge-Coloring, and Constraint Satisfaction*](https://ics.uci.edu/~eppstein/pubs/Epp-SODA-01.pdf)

For the disjoint supports, all but at most $r$ retain every signed clause in the easy neighbor. Hence $\mu\le C_r(7/8)^a(5/8)^b$ with a constant depending only on $r$. Write $\kappa=\log(1.3645)/\log(8/7)$. Since $2<(8/5)^\kappa$, the search factor $2^b1.3645^a$ is $O_r(\mu^{-\kappa})$. The density promise ensures $\tau=O(\log N)$ and $\mu^{-\kappa}\operatorname{poly}(\tau+1)=o(N/\log N)$ for all three $h$. In the largest case the exponent on $N$ is $2\theta\kappa<0.989$; all other powers here are logarithmic. Consequently each outer branch costs $O(1+N/\log(N+2))$.

Finally $A\tau+Bp\le\theta L+O_{r,c}(1)$. Either $\tau\le L+O(1)$ or $Dp\le L+O(1)$, by the definition of $\theta$. In the second case $25^p=O(2^L)$ and the second procedure completes in $O(N^h)$. The first takes care of the other case. A general solver can use any correct fallback outside width three. None of the stated exponents is claimed optimal.

[Lean](../lean/TernaryOverlapDensity.lean) verifies the exact probabilities, the weighted recurrence used on every pair, and the five-vertex extremizer. The [finite audit](../audits/intersecting_triples_density.py) checks all 1,048,576 monotone ternary hypergraphs on six vertices, 6,561 small signed catalogs, and disjoint copies of the equality example. The link between the partial exposures and transversals, and the RAM algorithm, are proved in the text.
