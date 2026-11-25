# When can a proper 3-CNF force one variable?

In a proper 3-CNF each clause uses three distinct variables. Let $d(x)$ count the clauses containing variable $x$, in either polarity, and let $E=\sum_x\max(0,d(x)-3)$. If **$E\le1$, every setting of any one variable extends to a satisfying assignment**. With $E=2$ a formula of maximum occurrence four can already force a designated variable which occurs just three times. A single pinned bit therefore behaves differently in degrees three and four, even when one further occurrence of the forced variable must remain available for use outside the formula.

## A sharp incidence argument

Suppose fixing $H$ to a prescribed bit makes the formula unsatisfiable. Choose a clause-minimal unsatisfiable subformula $U$ of the residual, and write $m,n$ for its clause and variable counts. Each residual clause has length two or three. Choose one original preimage for each residual clause. Let $a$ count the chosen two-literal clauses and $D_-=\sum_{x\in\mathrm{var}(U)}(3-d_U(x))_+$. At most $d(H)$ preimages lost a literal. Counting incidences gives
$$
 3(m-n)+D_-=a+\sum_{x\in\mathrm{var}(U)}(d_U(x)-3)_+
 \le d(H)+\sum_{x\ne H}(d(x)-3)_+\le 3+E .
$$
Tarsi's deficiency lemma gives $m-n\ge1$. If $m-n\ge2$ the display already implies $E\ge3$. In the remaining case $m-n=1$.

The classical tree characterization constructs every minimally unsatisfiable formula of deficiency one by repeatedly splitting a leaf clause $C$. At a split introduce a fresh variable $v$ and replace $C$ by $C_1\lor v$ and $C_2\lor\neg v$, where $C_1,C_2\subseteq C$ and $C_1\cup C_2=C$. The initial clause is empty. Each final leaf has width at most its depth. All leaves of $U$ have width at least two, so both root subtrees contain an internal node with two leaf children. The two corresponding split variables occur exactly twice in $U$, as each was fresh and its two children were never split. Thus $D_-\ge2$, and the display yields $E\ge2$. More generally, minimum clause width $s\ge1$ in deficiency one guarantees at least $2^{s-1}$ distinct degree-two variables, by applying the same argument in the distinct subtrees at depth $s-1$. [Kullmann, tree characterization, Theorem 6.16](https://eccc.weizmann.ac.il/report/2007/055/revision/1/download/) · [Fleischner, Kullmann and Szeider on deficiency](https://ac.tuwien.ac.at/files/pub/fleischner-kullmann-szeider-2002.pdf)

Two simultaneous pins need not extend even at maximum occurrence two. The two proper clauses $(x,y,z)$ and $(x,y,-z)$ admit no model with $x=y=0$. More generally, at maximum occurrence three the original incidence graph has a matching covering its clauses, since any collection of $c$ clauses has $3c$ incidences on at least $c$ variables. Fixing $k$ bits can destroy at most $k$ matched edges among the surviving clauses. Its residual SAT problem therefore has maximum deficiency at most $k$ and is polynomial-time decidable for every fixed $k$. [Szeider's fixed-parameter algorithm](https://doi.org/10.1016/j.jcss.2004.04.009)

## Two optimal forced-TRUE gadgets

Here $-x$ denotes negation. Each displayed gadget has one all-positive clause, all other clauses have both signs, and the all-ones assignment satisfies it. Reversing every literal gives a forced-FALSE gadget with one all-negative clause. For both displayed gadgets, the distinguished variable $H$ has three occurrences and can be used once more within an occurrence bound of four.

The following six clauses achieve the minimum possible total excess $E=2$.
$$
 (H,-u,-v),\ (H,u,w),\ (H,u,-w),\
 (-u,v,p),\ (v,-p,t),\ (v,-p,-t).
$$
At $H=0$ the second and third clauses force $u=1$. Successive clauses force $v=0$ and $p=1$, after which the last two require opposite values of $t$. Only $u,v$ occur four times.

The minimum number of clauses for a forced bit with a spare occurrence is **five**, achieved by
$$
 (H,x,z),\ (H,-y,-z),\ (H,-x,y),\ (x,y,-z),\ (-x,-y,z).
$$
With $H=0$, the choice $x=1$ forces $y=1,z=0$ and contradicts the last clause. The choice $x=0$ forces $z=1,y=0$ and contradicts the penultimate clause. On at most four proper clauses with $d(H)\le3$, a fixed value of $H$ shortens at most three rows. Their union of excluded assignments has measure at most $3/4+1/8<1$. This proves minimality.

In fact the five-clause gadget above is the only optimal one up to renaming, complementing variables and reordering clauses, at maximum occurrence four with $d(H)\le3$. In a five-clause obstruction all five rows must survive and exactly three must shrink. The measures of the three binary and two ternary excluded subcubes sum to one, so they partition the cube. Every row of this residual is necessary. There are at least three remaining variables, and by Tarsi there are at most four. In the four-variable case the deficiency is one. The partition implies saturation, since appending any new literal to any residual clause exposes one of the assignments excluded by that clause alone. In the binary tree above this forces the literal of the root split to remain present on every leaf. Otherwise adding its path value still leaves each clause contained in its full root-to-leaf clause, whose conjunction is unsatisfiable. Five occurrences of the root variable would violate the degree cap of four.

With three remaining variables, the three binary rows exclude disjoint edges of their cube. Each coordinate must be absent from at least one of the five rows, so the three edges point in three distinct directions. In each coordinate, the number of vertices removed on either side is odd because one comes from the edge in that direction and the other edges each contribute zero or two. The remaining two vertices are antipodal. Their complement in the cube is a six-cycle, and its two perfect matchings are interchanged by a coordinate transposition after centering one antipode at zero. This proves uniqueness. In particular all three free variables of a five-clause gadget have degree four. Thus the six-clause construction also attains the least clause count among constructions with $E=2$, maximum occurrence four and a spare occurrence of $H$.

The [finite audit](forced_bit_occurrence_audit.py) exhausts 242,825 subsets of the 32 signed triples on four named variables through five clauses. It finds eight variants forcing the designated variable true within the two degree caps. All eight belong to the displayed signed-permutation orbit. [Lean](ForcedBitOccurrence.lean) checks the general binary-tree counting lemma, the incidence inequality following from the stated structural hypotheses and both concrete truth-table projections. The reduction to classical minimally unsatisfiable formulas and the uniqueness classification are manuscript arguments. Priority of these pin classifications has not been established.
