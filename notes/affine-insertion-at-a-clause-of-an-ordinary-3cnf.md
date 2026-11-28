# A sharp Hamming-radius boundary for affine insertion in ordinary 3-CNF

Let $H(b,z)$ be an ordinary CNF context. Append a distinguished binary clause $x\lor y$ on two fresh variables. Replace it by $(x\lor t)\land(t\lor y)$, where the new bit $t$ must be an affine function of **all** the old bits $b,z,x,y$ over the two-element field. A rule is valid if the two formulas agree on every old assignment after substitution. The rule $t=x\oplus y$ is always valid. Ask whether it is unique. Width below refers to the context $H$.

**Width-three theorem.** Suppose $H(0,z)$ holds for every $z$ of Hamming weight at most two. Even with this promise, deciding uniqueness is at least as hard as ordinary 3-SAT under a deterministic linear-time, linear-length reduction. A construction achieving the reduction uses three distinct variables in every clause of $H$. Strengthen the promise to weight at most three and the same decision problem has a deterministic $O(N)$ algorithm on a logarithmic-word RAM, where $N$ counts encoded bits. Every input context in either promise already has the supplied satisfying assignment $b=0,z=0$.

## What a second affine rule would have to do

The weight-one promise is enough for this part. Write the correction to $x\oplus y$ as
$$
g=c+\delta b+\sum_i a_i z_i+\alpha x+\beta y .
$$
For any $(b,z)$ satisfying $H$, the substitution must take the prescribed values at $(x,y)=(0,0),(1,0),(0,1)$. Thus $g$ vanishes at these three points. Their differences force $\alpha=\beta=0$. At $b=0$, the zero vector and the unit vectors give $c=0$ and $a_i=0$ for every $i$. Only $g=\delta b$ remains. The nonzero correction works precisely when $H(1,z)$ has no model, since it changes the prescribed bit at $(0,0)$ for every context model with $b=1$. Consequently there are exactly one or two valid affine rules. Uniqueness is equivalent to satisfiability of $H(1,z)$. Restricting that variable in a width-three context yields a width-at-most-three formula in linear time.

More generally, it suffices that the models at $b=0$ affinely span the entire $z$-space. Computing affine approximations to propositional model sets has an established literature. The question here concerns a concrete two-clause substitution, a guaranteed Hamming ball of satisfying assignments, and the physical length of its representation. [Zanuttini, *Approximating Propositional Knowledge with Affine Formulas*](https://frontiersinai.com/ecai/ecai2002/pdf/p0287.pdf)

## Radius two can carry arbitrary 3-SAT

Start with a 3-CNF $F$ whose clauses each have three distinct variables. For each occurring variable introduce two bits $p_i,q_i$. At $b=1$ they indicate, respectively, that the positive or negative literal on variable $i$ is false. For every input variable impose
$$
(\neg b\lor p_i\lor q_i)\land(\neg b\lor\neg p_i\lor\neg q_i).
$$
For each source clause $\ell_1\lor\ell_2\lor\ell_3$ let $r_j$ be the indicated bit for the literal $\ell_j$. Add
$$
\neg r_1\lor\neg r_2\lor\neg r_3 .
$$
At $b=0$ only these all-negative triples impose any conditions. Every point of Hamming weight at most two satisfies all of them, because each triple has distinct variables. At $b=1$ exactly one bit of each pair is set. These choices represent the truth assignments on the occurring variables of $F$, and each negative triple checks exactly its source clause. Hence $F$ is satisfiable if and only if XOR is the unique affine rule. A 3-SAT decider gives the converse reduction by substituting $b=1$ in $H$. Both preserve linear physical length.

For ASCII DIMACS, name $b,x,y,t$ by the four single digits 1 through 4. If an old variable has canonical decimal identifier $v$, append a digit 0 or 1 to its spelling for the two new names. Their spellings are disjoint and cost just one additional byte per printed occurrence. One may emit the two consistency clauses at every literal occurrence, even when a variable appears many times. This avoids a dictionary and adds only a constant multiple of the input bytes. The variable bound can use the old header bound with an appended 9, or 9 alone if the old bound is zero. Proper triples give seven emitted clauses per source clause when consistency clauses are repeated. The distinguished clause can be carried separately or appended with its header count incremented once. All string and header operations take $O(N)$ deterministic time.

The usual width-at-most-three source also reduces. Discard tautologies, merge repeated literals within a clause, and pad any resulting binary clause $D$ with both signs of one fresh name in two ternaries. For a unit use all four sign choices on two fresh distinct names. Reserve two short fresh spellings by first relabeling every old identifier with one extra fixed decimal digit. Handle an empty clause using a fixed contradictory proper 3-CNF, and an empty conjunction using a fixed satisfiable one if occurring designated variables are required. These operations have linear time and output length. For an arbitrary-width ordinary CNF the journal also gives a linear physical reduction to proper 3-SAT. [Ordinary CNF to proper 3-CNF](sat-one-bit-from-a-uniquely-propagated-file.md)

## A one-bit edit of an ordinary proper 3-CNF file

The same radius boundary applies to an ordinary SAT query. Use guard $b$ with decimal name 1 and its complement $a$ with name 3. In the common body put $H(b,z)$ and enforce $a=\neg b$ using $a\lor b$ and $\neg a\lor\neg b$. Append the positive unit $a$ to the first file or $b$ to the second. Use three further reserved names 5, 6 and 7 for false anchors. Seven proper ternary clauses pin the anchors by forbidding each of their seven nonzero assignments. Pad each of the common binary clauses with one false anchor; pad the last unit with two distinct false anchors. This produces two proper files with the same headers and layout. In the last clause ASCII digits 3 and 1 differ in exactly one physical bit.

In the first file the control values are fixed to $a=1,b=0$ and the false anchors are zero. Every assignment of weight at most two to **all the remaining data variables** satisfies the file. In the edited file the control values are $a=0,b=1$, and satisfiability is exactly that of the source $F$. The easy file, the known model and the edit location can all be supplied with the hard file within linear total length. The guard and the fixed wrapper have constant size. If the source has no variables, a header bound of 9 still covers the controls. For each of the three time targets, a deterministic $O(N^k)$ solver for these edited files would give the same time bound for the source for $k=1,2,3$. Conversely any solver for ordinary SAT decides the edited files. Both statements hold even if the edit position and a model of the easy file are provided as part of the promise, using the succinct all-zero data assignment or a bit list on the occurring variables.

If the easy slice in this same wrapper includes the radius-three ball, the argument below gives a linear algorithm for the edited file. The ball is on all data variables. Excluding hidden witness variables from the ball would be a different promise.

## Radius three gives a linear algorithm

Any falsifiable clause of width at most three on $z$ has a falsifier of weight at most three. Set the variables occurring negatively in it to one and the rest to zero. If $H(0,z)$ contains the radius-three ball, every clause after restriction at $b=0$ is tautological or already satisfied. In the original context each nontautological clause must therefore contain $\neg b$. At $b=1$ it leaves at most two literals. The uniqueness test now reduces to one 2-SAT instance. A decimal digit trie can assign indices to the distinct occurring identifiers while scanning the input. The implication graph has $O(N)$ vertices and edges. Its strongly connected components decide satisfiability in deterministic linear time. [Aspvall, Plass and Tarjan, *A linear-time algorithm for testing the truth of certain quantified Boolean formulas*](https://collaborate.princeton.edu/en/publications/a-linear-time-algorithm-for-testing-the-truth-of-certain-quantifi/)

The same linear algorithm works at radius one for width-at-most-two contexts, since restriction leaves at most two literals regardless of the stronger radius promise. These reductions establish a boundary in the width and the promise. Proving that the radius-two problem requires superlinear deterministic time would require a new lower bound. A time lower bound for individual substitution rules does not follow from their number.

## A dense set of models changes what a clause edit can hide

There is a separate bound for any ordinary width-at-most-three CNF $F$, including unsatisfiable files. Suppose some CNF $E$ accepts a fraction $\mu>0$ of uniform assignments, and all but at most $r$ clauses of $F$ also occur in $E$. Take densities on the union of the variable sets, allowing unused variables freely. A single deterministic SAT solver, given **only $F$**, runs on such inputs in
$$
O\!\left(N\,7^r\,\mu^{-\log(7)/\log(8/7)}\right).
$$
In particular, one aligned clause edit of a formula with any fixed positive model density always has a linear-time solver on this class. The solver needs neither a neighboring file nor its density.

Discard tautologies and shorten repeat literals. Greedily choose a maximal collection of $k$ variable-disjoint ternary clauses. At least $k-r$ of the selected constraints are also satisfied by every model of $E$ when $k>r$. Each independently excludes one of eight assignments, so $\mu\le(7/8)^{k-r}$ in that case. Branch over the seven satisfying patterns on each chosen triple. Every remaining ternary touches a fixed variable by maximality, so each residual is a 2-SAT problem. The time is $O(N7^k)$, which proves the claimed bound, including $k\le r$. The search is correct on every width-three input. The density inequality bounds its running time on both verdicts. The clause branching is the standard backdoor-to-2-SAT argument used earlier in the journal. [Earlier clause branching](native-core-extensions.md) · [Williams, Gomes and Selman on backdoors](https://ijcai.org/proceedings/2003/167)

A radius-two ball in a growing data space contains only polynomially many required models. The reduction above guarantees that ball. For a sequence of one-clause edits to force unbounded time per encoded bit on this solver, the model fractions of their easy neighbors must tend to zero along any subsequence with diverging time ratio.

## Verification

[GuardedAffineSubdivision.lean](../lean/GuardedAffineSubdivision.lean) proves the semantic uniqueness criterion for an affine correction, the radius-one criterion, and the two local Hamming-ball lemmas. The physical encoding, the paired-variable construction and the running-time analysis are proved above. The [finite audit](../audits/guarded_affine_subdivision.py) checks every subset of the eight signed proper triples on three variables and six four-variable cases. It also reparses and checks ten complete ordinary DIMACS wrapper pairs, including both edited verdicts and the one-bit difference.
