# Two-permutation covers with few failures of commutativity

For explicit permutations $P,Q$ on $q$ points, let $d$ be the number of points $u$ with $PQu\ne QPu$. The question is whether some $S$ gives a disjoint partition $S\mathbin{\dot\cup}P(S)\mathbin{\dot\cup}Q(S)=[q]$. There is a deterministic algorithm taking $O(q+2^{O(d)})$ word operations and $O(q+1)$ words of space. It returns a cover when one exists. After $O(q)$ preprocessing, the residual decision problem has $O(d+1)$ Boolean variables and bounded-width clauses. The general two-permutation problem has the same linear, quadratic and cubic clocks as explicit DIMACS 3-SAT. [Reduction in both directions](two-permutations-and-the-explicit-sat-clock.md)

When $P,Q$ commute, a nonempty orbit under the two permutations admits a cover exactly when it admits $h$ to $\mathbb Z/3$ such that
$$
                 h(Pu)=h(u)+1,\qquad h(Qu)=h(u)-1.
$$
Equivalently, fixing $u$ in that orbit, every relation $P^aQ^b u=u$ with $a,b\in\mathbb Z$ has $a-b\equiv0\pmod 3$. Set $h(P^aQ^b u)=a-b$ to pass from this condition to a labeling. All covers on the orbit are the three individual residue classes of any one such $h$. Hence an instance with $c$ orbits has either zero covers or exactly $3^c$, including the empty instance. Graph traversal tests the condition and constructs a cover in $O(q+1)$ word operations. The commuting classification also follows by lifting each orbit to the translational tiling of $\mathbb Z^2$ by $\{0,e_1,e_2\}$. Horak and Kim prove periodicity for prime tiles and classify the lattice tilings in this case. Their proof uses a congruence that also works locally here. [Horak and Kim, Theorems 16, 18 and 24](https://arxiv.org/pdf/1603.00051)

## A local identity at the points where the permutations commute

Write $A=P^{-1}$, $B=Q^{-1}$ and $x=1_S$. An exact cover satisfies the integer equations
$$
             (Tx)(u)=x(u)+x(Au)+x(Bu)=1.
$$
Let $D=\{u:ABu\ne BAu\}$. It has size $d$ because inversion preserves the number of disagreements of two permutations. Set $H=D\cup A^{-1}D\cup B^{-1}D$ and $b=|H|\le3d$. At $u\notin H$ one can interchange adjacent $A,B$ in any word of length at most three applied to $u$. The two letters meet at $u,Au$ or $Bu$, all outside $D$. Since $T^3x=T^2\mathbf1=9\mathbf1$, the multinomial expansion at this one point gives
$$
                 x(u)+x(A^3u)+x(B^3u)\equiv0\pmod 3.
$$
The three bits are equal. This conclusion only uses the equations on this bounded neighborhood.

Write $r(u)=(x(u),x(Au),x(A^2u))$. The equations at $u,Au,A^2u$ bound each cyclic adjacent pair in $r(u)$ by one, using $x(A^3u)=x(u)$ for the wrap. If the triple were zero, the equations at $u,Au$ would force $x(Bu)=x(BAu)=1$. Since $BAu=ABu$, the equation at $Bu$ would fail. Thus $r(u)$ has exactly one 1. If it is $(a_0,a_1,a_2)$, then
$$
                 r(Au)=(a_1,a_2,a_0),\qquad r(Bu)=(a_2,a_0,a_1).
$$
For the latter, apply the equations at the three row positions and use $BA^ju=A^jBu$ for $j=0,1,2$. The site of the 1 therefore moves by $-1$ under $A$ and $+1$ under $B$. With $H$ empty this supplies the claimed labeling, and $x(u)=1$ exactly where its phase is zero. Conversely any labeling satisfying the two increments gives a cover by any of its fibers. Each nonempty orbit contains all three phases since $A$ is a permutation.

## Reducing to the neighborhoods of the failures

Build the undirected graph of the $A,B$ arrows and delete $H$. Traverse each remaining component, propagating the phase differences $-1,+1$ along the corresponding arrows, reversing the sign when moving backwards. An inconsistent cycle precludes any cover by the local identity. On a consistent component $C$ write the phase as $t_C+\ell(u)$, where $\ell$ is the propagated label and $t_C\in\mathbb Z/3$ is one free choice. This specifies $x(u)=[t_C+\ell(u)=0]$ at every vertex of $C$.

A component with no edge to $H$ is a whole orbit and contributes three independent covers. Let $c$ count such components after successful propagation. Every other good component has an edge to $H$, giving at most $4b$ of them by the degree bound. Guess their $t_C$ and the $b$ bits at $H$. Rows whose three positions $u,Au,Bu$ all lie outside $H$ hold automatically by their phase differences. Explicitly test the remaining at most $3b$ rows. For each component with an edge to $H$ also test that the one-hot triple prescribed at its root agrees with the three bits reconstructed at the root, its $A$-image and its $A^2$-image. Every genuine cover passes this test. Conversely the surviving choices give covers because every row holds, and a cover determines each chosen root phase by that test. If $K$ choices survive, the exact number of covers is $K3^c$.

Only $2^b3^{4b}$ choices are possible. One can enumerate these with digit arrays of $O(b+1)$ words, even when the number of choices exceeds the RAM address space. Each boundary test reads at most a constant number of variables over constant-size domains, with $O(b+1)$ tests in total. Those tests give an equivalent bounded-width CNF with $O(d+1)$ variables and clauses by encoding each phase with two bits. This gives $O(q+2^{O(d)})$ decision time, allows linear-time reconstruction after a successful search, and yields the exact count in the factored form above. In particular pairs with $d=o(\log q)$ take $O(q)$ word operations. General pairs can have $d$ proportional to $q$.

The deterministic Exponential Time Hypothesis gives a conditional lower bound on the dependence on $d$. A $2^{o(d)}q^{O(1)}$ algorithm, applied to the explicit reduction above on 3-CNFs with $v$ variables and $O(v)$ clauses, would run in $2^{o(v)}$ time since $d\le q=O(v)$. By sparsification, this contradicts the hypothesis. The unrestricted linear, quadratic and cubic clocks remain open. Priority for the parameterization by the number of commutation failures is unverified. [Impagliazzo, Paturi and Zane, sparsification](https://cseweb.ucsd.edu/~russell/ipz.pdf)
