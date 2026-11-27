# Two clause prefixes and two variable pins

Let an ordered CNF have $v$ designated Boolean variables. Fix two of its prefixes, one containing the other. A query selects either prefix and prescribes values of at most two designated variables. Before the query, choose a list of complete assignments. The list must contain a witness for every satisfiable query. For $v\ge 3$, the largest possible minimum list size over these instances is exactly
$$
                       \binom v2+v.
$$
Other variables may appear in the formula. A listed assignment witnesses a query precisely when it satisfies that prefix and all its pins. The theorem also holds for arbitrary nested sets of projected satisfying assignments on the designated variables, and the lower bound is attained with an ordinary 3-CNF and auxiliary variables.

With one prefix the extremal count for $v\ge9$ is $\binom v2$, by the irredundant-subcube bound below. With three prefixes one can force $1+v+\binom v2$ witnesses by successively imposing Hamming weight at most two, one, and zero. The two-prefix improvement of one over the general degree-two basis bound depends on the geometry of Boolean solutions to 2-CNFs.

In the terminology of recursive teaching, this is the maximum size of a class $C\subseteq\{0,1\}^v$ with $\mathrm{RT}^{(2)}_1(C)=C$ in the indexing of Fallat et al. The first simultaneous round removes words isolated by at most two labeled examples, and the second removes words isolated in the remainder. A minimum list below gives a class removable in these two rounds. Conversely, use any such class as the weak set and the words left after its first round as the strong set. Each removed word then has a query with a unique designated witness, forcing the whole class into the list. Arbitrary nested finite sets can be encoded by successively forbidding excluded words in an ordered CNF. The unrestricted-round cardinality bound and its polynomial method are due to Samei et al. Historical priority for the exact two-round refinement has not been established. [Fallat et al., Definition 8](https://jmlr.org/papers/volume24/22-0330/22-0330.pdf) · [Samei et al.](https://www.sciencedirect.com/science/article/pii/S0304397514007026)

## What equality in the dimension bound forces

Take a minimum common list. For duplicate designated words retain a completion satisfying the strongest available prefix, so there is at most one representative per word. Write $A$ for the projected representatives surviving the stronger prefix and $B$ for the others. Every representative has a private query, since otherwise it could be removed. A private query for $b\in B$ uses the weaker prefix. A private query for $a\in A$ can use the stronger prefix, since tightening its original private query preserves its witness. Fix such a query for each representative. Refine its pins, using that representative's values, to exactly two different coordinates. The stricter query remains private and satisfiable.

Write $f_b,u_a$ for the indicators on the entire Boolean cube of the respective pin patterns. Each is a product of two coordinate literals and hence a real multilinear polynomial of degree at most two. On the representatives the $f_b$ are the indicators of the individual $b$'s, and on $A$ the $u_a$ are the indicators of the individual $a$'s. Evaluating a linear relation on $A$ and then on $B$ proves independence of all these functions. Their ambient space has dimension $D=1+v+\binom v2$, by the squarefree monomial basis. Thus every minimum list has size at most $D$.

Assume for contradiction that the list has size $D$. The pin indicators then span **every real function on the cube of multilinear degree at most two**. Write $E=\{x:f_b(x)=0\text{ for all }b\in B\}$, which contains $A$. Restricting the basis expansion of any such function $g$ to $E$ gives
$$
                         g(x)=\sum_{a\in A}g(a)u_a(x)\qquad(x\in E),
$$
because evaluation at $a$ determines its coefficient. Taking $g=1$ shows exactly one of these zero-one indicators is one at each $x\in E$. Taking each coordinate function $g(x)=x_i$ shows $x$ agrees in every coordinate with that unique representative. Consequently $E=A$. Over the reals the identity for the constant function counts indicators as integers and furnishes uniqueness.

In particular $A$ is the solution set of the 2-CNF forbidding the loose pin patterns. It is closed under coordinatewise majority. If a majority of three satisfying words violated a two-literal clause, each of its two literals would be false on at least two of the words, forcing one word to falsify both. Moreover each point of $A$ is uniquely specified within $A$ by its own two pins.

## A majority-closed set with two-pin certificates

For words $x,y$, write $I(x,y)$ for the Boolean box that fixes the coordinates on which they agree. On $A$ join distinct words $x,y$ precisely when $I(x,y)\cap A=\{x,y\}$. Between any $x,y\in A$ there is a path that changes only differing coordinates and changes each once. Indeed an intermediate point in their box splits the problem into two strictly smaller Hamming distances with disjoint sets of changed coordinates. Induction proves the claim and gives connectivity.

At a vertex $x$ identify a word $y$ with its set $S_y$ of differences from $x$. For any neighbor $a$ and any $y\in A$, the majority of $x,a,y$ corresponds to $S_a\cap S_y$ and lies between $x,a$. Hence $S_y$ contains all of $S_a$ or none of it. Distinct neighbors therefore have nonempty disjoint difference sets. The two pins isolating $x$ must hit each of these sets. Every vertex has degree at most two.

This connected graph is a path (possibly a singleton) or a four-cycle. To prove the cycle assertion, fix a degree-two vertex $x$ with neighbors $a,b$ and write $I=S_a,\ J=S_b$. Every other word contains at least one of these bundles in its difference set, by the first edge of a coordinate-monotone path from $x$. If some $y$ contains both, $w=\operatorname{maj}(a,b,y)$ has difference set $I\cup J$. It is adjacent to $a$ and to $b$, since an intermediate point on either edge would meet a bundle in a proper nonempty subset. This gives a square, which exhausts the connected graph by the degree bound. If no such $y$ exists, deleting $x$ separates the words containing $I$ from those containing $J$. For one from each side their majority with $x$ has neither bundle, hence equals $x$ and lies between them. No edge joins the two sides. Thus $x$ cannot lie on a cycle in this case.

On a path the unique simple route between its endpoints equals a coordinate-monotone route. Its edges change disjoint nonempty sets of coordinates, giving at most $v+1$ vertices. If the path has $v+1$ vertices, every edge changes a single coordinate and every coordinate changes exactly once. A permutation and complementation of coordinates then identify $A$ with the chain of initial segments $\varnothing,\{1\},\ldots,\{1,\ldots,v\}$.

## A short upper bound for $v\ge9$

The loose pin patterns form an irredundant family of codimension-two subcubes, each having its private vertex $b$. Meshulam's bound gives
$$
                    |B|\le\binom v2\,\frac{2^v}{2^v-v-1}.
$$
For $v\ge9$ the right side is strictly below $\binom v2+1$. Indeed $2^9>(9+1)(\binom92+1)$, and the polynomial $H(v)=(v+1)(\binom v2+1)=(v^3+v+2)/2$ satisfies $H(v+1)<2H(v)$ for $v\ge 9$, as $2H(v)-H(v+1)=v(v^2-3v-2)/2>0$. The integer bound $|B|\le\binom v2$ follows. [Meshulam's bound, Theorem 4 in Ellis](https://arxiv.org/pdf/1003.2960)

Since $|A|+|B|=D$, the strong set has at least $v+1$ vertices. Its graph cannot be a square at this dimension. It must be the full chain just described. On coordinates $i<j$ the chain realizes all binary patterns except $x_i=0,x_j=1$. Hence every loose cube is an inversion of this kind. As their union is the complement of the chain, every adjacent inversion must occur: the word with ones in $\{1,\ldots,i-1,i+1\}$ has exactly the inversion $(i,i+1)$. Every word with a nonadjacent inversion has an adjacent one somewhere between its endpoints. A nonadjacent inversion cube would thus have no private vertex, so $|B|\le v-1$. This contradicts $|B|=\binom v2$.

## An implication-graph proof for every $v\ge3$

Continue under the full-dimension assumption $|A|+|B|=D$. We show $|A|+|B|\le2v$, whereas $D-2v=(v-1)(v-2)/2>0$. If $A$ is empty, the loose indicators form a basis and evaluation on the representatives gives $1=\sum_b f_b$ on the entire cube. This partitions the cube into codimension-two subcubes of equal size, so there are exactly four representatives. Thus take $A\ne\varnothing$.

Let $H$ contain the binary clauses forbidding the loose patterns. Its models are exactly $A$, by the real-basis argument. Every clause is essential because its private word $b$ violates that clause alone. It suffices to exhibit an equivalent subcollection whose size plus $|A|$ is at most $2v$.

Call a coordinate *fixed* if it takes a single value on $A$. Complement the $c$ fixed coordinates to have value zero there. If the relation graph is a path, complement the $f=v-c$ other coordinates to be zero at the first endpoint. Each nonconstant coordinate then turns to one along exactly one path edge and stays one. If it is a square, take a vertex as the origin. The four words toggle two disjoint coordinate bundles independently. In either case $A$ contains the all-zero word and the word setting every nonconstant coordinate to one. Each clause is consequently an implication $i\to j$ (meaning $\neg x_i\lor x_j$) or a conflict $\neg x_i\lor\neg x_j$. No implication leads from a nonconstant coordinate to a fixed one, and every conflict contains a fixed coordinate.

Setting the fixed coordinates to zero leaves precisely a system of implications among the $f$ nonconstant coordinates. Every other clause is automatically satisfied. In any implication-only formula $x_i=1$ forces $x_j=1$ precisely when $j$ is reachable from $i$. For the reverse direction, set just the vertices reachable from $i$ to one. Thus strongly connected components in this graph are exactly the coordinate bundles taking identical values in $A$.

For a path with $f>0$, there are $k=|A|-1$ such bundles. Their reachability order is a chain since the words of $A$ turn on successive bundles. Preserve all reachability within each component by retaining, from its original arcs, a directed spanning tree out of one root and a tree into that root. The sum of these arc counts is at most $2(f-k)$. Between each two consecutive components keep one arc in the necessary direction. Such an arc exists since a path between consecutive components in the reachability order cannot pass through a third one. In total at most $2f-k-1$ free-variable clauses remain, and adding $|A|=k+1$ gives $2f$. For a square, its two bundles are incomparable, so at most $2(f-2)$ arcs suffice, again giving $2f$ after adding its four words.

It remains to force the $c$ fixed variables to zero. If $c>0$, form the graph of original implications between fixed variables only. Let it have $m$ strongly connected components of which $s$ are sinks in its acyclic component graph. Preserve strong connectivity using at most $2(c-m)$ arcs as above. From each nonsink component retain one outgoing fixed-to-fixed arc. Every true fixed variable would force an entire sink to be true, since following the retained arcs between components eventually reaches a sink.

For each sink $U$, consider its forward closure under **all** original implications, including those leading to nonconstant coordinates. Its only fixed variables are those in $U$, since no nonconstant variable can lead back to a fixed one. The assignment setting exactly this closure to one respects every original implication. It must violate an original conflict, since it has true fixed variables. Keep one such conflict. It either has both endpoints in $U$, or has one endpoint in $U$ and the other a nonconstant variable in the closure. In the latter case retain the first fixed-to-free arc on a closure path from $U$ to that endpoint. The rest of that path uses only free implications, whose reachability has already been preserved. Thus $U$ cannot be true under the retained clauses. The fixed-variable construction retains at most
$$
                    2(c-m)+(m-s)+2s\ \le\ 2c
$$
clauses. No clauses are needed for this part when $c=0$. Once all fixed variables are zero, the retained free implications enforce exactly $A$. The resulting subcollection is equivalent to $H$, so by essentiality it includes all $|B|$ clauses. Irredundancy and equivalent subformulas of 2-CNF have an established literature. [Liberatore on redundancy in 2-CNF](https://arxiv.org/abs/cs/0506074)

If $A$ is a singleton, all $v$ coordinates are fixed. Each sink then needs only an internal conflict and no fixed-to-free arc; the number of clauses is at most $2(v-m)+(m-s)+s=2v-m\le 2v-1$. This covers the one-vertex path as well. We have proved $|A|+|B|\le2v$ in all nonempty cases, contradicting full dimension for every $v\ge3$. At $v=2$ one prefix allowing all four words already forces four representatives, since both coordinates may be pinned.

## Attaining the bound

For attainment, use the weight-at-most-two predicate at the weaker prefix and add the weight-at-most-one restriction at the stronger prefix. At the weaker prefix pin each pair to one. Its two-element support is forced. At the stronger prefix pin each single variable to one. Its singleton support is forced. These $\binom v2+v$ supports are distinct. Both predicates have an ordered width-three encoding using one sequential counter. Use deterministic gates for the flags that the first $i$ bits contain at least $r$ ones, for $r=1,2,3$, assert at the first threshold that the final third flag is false, then assert that the second is false. The ordinary equivalence clauses for binary AND and OR gates have width at most three. Every satisfying designated word extends to all the counter gates.

The dimension bound transfers to more prescribed thresholds, and the two-threshold proof uses the exact real basis and the majority closure specific to pinning two coordinates. This theorem counts witnesses selected with knowledge of the formula, without a running-time bound on selection. Its connection to the RAM research is through the proposed prefix-witness argument. [Lean checks of clause closure and the edge argument](../lean/TwoThresholdPairs.lean) · [Finite checks of the structural lemmas](../audits/two_threshold_pair_pins_audit.py)
