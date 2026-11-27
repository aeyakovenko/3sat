# The smallest unsatisfiable two-permutation instance with a satisfiable double cover

On $q$ labels consider two permutations $P,Q$. Row $i$ requires exactly one of $x_i,x_{P(i)},x_{Q(i)}$ to equal one. Write $A$ for this incidence matrix. These are the row-to-column arrays. In the image-of-a-set convention of the [SAT reduction](two-permutations-and-the-explicit-sat-clock.md), take their inverses. Throughout, **simple** means each row has three distinct labels. Each label consequently occurs in three distinct rows. The smallest unsatisfiable simple base having a satisfiable two-sheet cover has **nine labels**. There is an example with distinct row and column neighborhoods and with $P,Q,P^{-1}Q$ all nine-cycles. If any two rows are additionally required to meet in at most one label, the minimum rises to **twelve**.

## The exact condition for some cover to accept

A degree-$d$ cover replaces each label by $d$ sheets, keeps the identity incidence fixed, and lifts $P,Q$ to permutations whose projections are $P,Q$. Each base incidence may use its own fiber bijection. There exists a satisfiable degree-$d$ cover if and only if
$$
       Az=d\mathbf1,\qquad z\in\mathbb Z^q,\qquad 0\le z_i\le d .
$$
Indeed, $z_i$ counts the selected sheets over $i$. Summing all $d$ equations over one base row gives the equality. Conversely select sheets $0,\ldots,z_i-1$ over each $i$. On the $d$ sheets of row $i$, those same $z_i$ sheets have already been covered by the identity incidence. Partition the remaining row sheets into two groups of sizes $z_{P(i)}$ and $z_{Q(i)}$. On the $P$ edge choose a bijection mapping the first group to the selected sheets over $P(i)$ and its complement to their complement; do the same on the $Q$ edge using the second group. The assembled maps are permutations since the base maps are permutations. Each lifted row now contains precisely one selected label. This is a direct specialization of the graph-cover interpretation of rational local marginals. [Vontobel, *Counting in Graph Covers*](https://arxiv.org/abs/1012.0065)

In particular every base has a satisfiable three-sheet cover: select sheet zero, lift $P$ with offset $+1$ mod 3 and $Q$ with offset $+2$. The degrees admitting some satisfiable cover are closed under addition, by adding the integer fiber counts or taking disjoint unions of covers.

There is a general arithmetic dichotomy for these degrees. The class of $\mathbf1$ in the quotient group $\mathbb Z^q/A\mathbb Z^q$ has order one or three since $A\mathbf1=3\mathbf1$. In the order-three case feasible degrees are exactly the multiples of three. In the order-one case choose an integer $x$ with $Ax=\mathbf1$. For $d=3k+r$, $r\in\{-1,0,1\}$, set $z=k\mathbf1+rx$. If $k>\max_i|x_i|$ then $0\le z_i\le 2k\le d$ and $Az=d\mathbf1$. All sufficiently large degrees are feasible. Conversely a feasible $d$ coprime to three gives integers $u,v$ with $du+3v=1$, so $A(uz+v\mathbf1)=\mathbf1$. This criterion concerns existence across all covers of the specified degree; a specified individual lift can have a different verdict.

## An explicit connected extremal pair

The following arrays list the images on labels $0,\ldots,8$:
$$
\begin{aligned}
 P&=(1,7,0,6,2,3,8,5,4),\\
 Q&=(2,0,8,1,3,7,4,6,5),\\
 z&=(2,0,0,1,1,1,1,0,0).
\end{aligned}
$$
Here $Az=2\mathbf1$. With sheets indexed by $s\in\{0,1\}$, explicit lifts are $(i,s)\mapsto(P(i),s\mathbin{\mathrm{xor}}p_i)$ and $(i,s)\mapsto(Q(i),s\mathbin{\mathrm{xor}}q_i)$, where
$$
 p=(0,0,0,1,0,1,0,0,0),\qquad
 q=(0,0,0,0,1,0,1,1,1).
$$
Choose $s<z_i$ in each fiber. The base and this cover are connected. Indeed $P$ alone cycles through the entire base. A disconnected double cover of a connected base would split into two degree-one copies, which could not both be satisfiable here.

For a short proof of the base verdict relabel its columns by $(0,5,6,1,3,4,2,7,8)$, in this order. Its nine rows then read
$$
 056,\quad057,\quad068,\quad125,\quad136,\quad147,\quad238,\quad247,\quad348,
$$
where e.g. $056$ requires $x_0+x_5+x_6=1$. The first three force $x_6=x_7=b$ and $x_5=x_8=a$. Comparing $136$ with $147$, $147$ with $247$, and $125$ with $238$ gives $x_1=x_2=x_3=x_4=x$. The half-label rows then require $2x+a=2x+b=1$, forcing $x=0$ and $a=b=1$. Row $056$ is impossible. All three two-color matching unions are Hamiltonian, as can also be checked by tracing the displayed permutations.

This example has a solution to every additive consistency test obtained from the unrestricted integer system $Ay=\mathbf1$: take $y=\mathbf1-z$. In particular it supplies an integral signed preimage, which survives every reduction modulo an integer. It also has the strictly positive real relaxation $y=\mathbf1/3$. Its exact feasible positive cover degrees are $\{2,3,4,\ldots\}$, since 2 and 3 are feasible. Hence even simultaneous knowledge of lift existence at **every** degree above one agrees with a satisfiable base. Lifting and checking these verdicts cannot propagate a base obstruction to the next size.

## Why nine is minimal and why every nine-label witness uses a four-cycle

For a double cover give the labels with $z_i=2,1,0$ the names doubles, halves and zeros (the normalized marginal of a half is $1/2$). Every row contains either one double and two zeros, or two halves and one zero. Every column has degree three, so $3\sum_i z_i=2q$; in particular $3\mid q$. If there are no doubles, $x=\mathbf1-z$ is already Boolean. If there are no halves, use $x=z/2$. With exactly two halves, every row involving either contains both; select all doubles and just one half. These cover all possibilities at $q=3,6$, since their total weights are two and four.

At $q=9$ total weight is six. Any counterexample consequently has one double, four halves and four zeros. The six two-half rows make a loopless cubic multigraph on the four halves. If it is bipartite, select one bipartition side and the double to get a Boolean solution. On four vertices the multiplicities on opposite pairs must agree, by subtracting the degree equations. Thus the three multiplicities $a,b,c$ on the three perfect matchings satisfy $a+b+c=3$. If at most two are positive, the multigraph is bipartite. If all are positive, it is the simple $K_4$. The three rows incident with the double need six zero appearances among just four labels, so two of its rows share both the double and a zero. Every nine-label counterexample therefore has an incidence four-cycle.

The [finite audit](../audits/two_permutation_cover_audit.py) enumerates this entire necessary pattern, fixing the half and zero labels, ordering the $K_4$ edges lexicographically and treating the three double rows as an unordered multiset of zero pairs. There are 5,640 valid decorations. Direct testing of all $\binom{9}{3}$ Boolean candidates for each gives 2,040 unsatisfiable decorations, including 1,584 with all row neighborhoods and all column neighborhoods respectively distinct. These counts refer to decorated, indexed data, not isomorphism classes or distinct permutation pairs. For the displayed witness the audit checks the actual permutations and the sheet-by-sheet exact cover.

## Twelve labels without repeated row intersections

Take two doubles $D_0,D_1$, four halves forming the vertices of a $K_4$, and six zeros $z_0,\ldots,z_5$. On the six cycle edges $(z_i,z_{i+1\bmod6})$ place a row with those zeros and $D_{i\bmod2}$. Put the remaining six rows on the six edges of the $K_4$, adding one different zero to each. Assign the even-indexed zeros to the three edges of a four-vertex path. Its complement in the $K_4$ is also a four-vertex path; assign the odd-indexed zeros there. Every label occurs three times, and two different rows share at most one label.

If a double is selected, its three cycle edges force all six zeros off. Then both doubles are on, and the $K_4$ edges would require a bipartition. If both doubles are off, the zero bits alternate around the six-cycle, leaving three of the $K_4$ rows with their zero off. Summing the six $K_4$ row equations shows that exactly one half must be on (each occurs three times). Its three edges would have to be exactly the path carrying the three off-zeros. A vertex star is not a four-vertex path. The base is unsatisfiable while the indicated double/half/zero weights yield a satisfiable double cover. The construction is connected, and the argument for $q\le9$ proves minimality under the row-intersection condition.

To recover two permutations, decompose the regular bipartite incidence graph into three perfect matchings and use one as the identity to rename the columns. For example, the audit obtains
$$
 P=(6,0,5,9,2,3,10,1,11,8,4,7),\qquad
 Q=(9,4,0,1,3,6,7,8,2,10,11,5).
$$
It checks the absence of Boolean solutions before and after renaming, the row intersections, connectivity, and actual covers through degree 14. Regular bipartite edge coloring provides the general matching decomposition. [Cole, Ost and Schirra](https://cs.nyu.edu/media/publications/TR1999-792.pdf)

A [Lean 4.19 file](../lean/TwoSheetPermutationWitness.lean) verifies the explicit nine-label instance, its lack of a nonnegative integer solution, the signed integer certificate, the permutation inverses, and all eighteen rows of its displayed two-sheet lift. The minimum-size and general degree arguments are manuscript proofs.

The minimal finite witnesses and their census concern lift feasibility in the exact-cover formulation. They give no running-time lower bound for an unrestricted RAM. Priority for the extremal sizes has not been established.
