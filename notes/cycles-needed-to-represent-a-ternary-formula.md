# How many cycles does a network need to represent a 3-CNF?

Let $b(f)$ be the minimum number of edges whose removal leaves a forest in a Boolean network of tables of arity at most three that represents $f$ on every assignment to its $h$ named inputs. The network may have arbitrarily many auxiliary bits and tree vertices. Among proper 3-CNF predicates on $h$ variables,
$$
                    \max_f b(f)=\Theta(h^3/\log h).
$$
Positive clauses alone attain the lower bound. There is also a sparse family in which almost every predicate needs the number of cycles in its ordinary occurrence graph up to a lower-order error. All formulas in the lower-bound families have the same satisfiability answer.

Krapivin, Przybocki and Subercaseaux give the $\Theta_k(h^k/\log h)$ worst-case scale for the number of bounded-width clauses in an existential encoding of a $k$-CNF predicate, including the earlier hypergraph-decomposition upper bounds. The cycle formulation follows by compressing the trees and paths between the surviving terminals. We give a direct construction and a separate count retaining the leading term for sparse formulas. Priority for the cycle formulation is unestablished. [Krapivin, Przybocki and Subercaseaux, introduction and §4.6](https://arxiv.org/html/2611.05614v1)

## Network and terminal convention

An internal edge carries one Boolean value shared by its two incident ports. A vertex carries a fixed relation on its at most three incident ports. Loops and parallel edges are allowed. Each of the $h$ named inputs appears at exactly one external port, and its value there is prescribed. Copies elsewhere use ordinary edges and equality tables. External ports can equivalently be drawn as labeled degree-one terminals. Adding such a leaf together with its edge leaves $|E|-|V|+c$ unchanged, where $c$ is the number of connected components. Unused named inputs can have a separate unconstrained unary table. A fixed external assignment is accepted exactly when internal values exist that satisfy all tables.

The single-port convention matters. If an input label could occur on arbitrarily many unrelated leaves at no cost, a formula could read the same named variable from many leaves of a tree. Recording those occurrences or joining them by explicit equality wires is necessary for the count below. An original SAT variable with many occurrences can always be supplied from its one terminal through an equality tree of maximum degree three.

## A forest with paired leaves

Choose a spanning forest. There are $b=|E|-|V|+c$ remaining edges. Cut each of these at its middle to create two new terminals and record their pairing. The resulting forest has $L=h+2b$ terminals. Initially allow independent values at all these terminals.

In each component remove subtrees containing no terminal, computing the possible values of their attachment edge by bottom-up existential projection of its constant-size tables. Intersect the resulting unary constraints at the retained ports and existentially remove the pruned ports. A component with no terminal contributes one constant bit to the answer. A component with one terminal contributes a unary relation. In each remaining component, replace every maximal path of degree-two tables by the binary relation obtained by Boolean matrix multiplication along the path. After the pruning, the leaves are terminals. A tree with $t\ge2$ leaves and maximum degree three has at most $t-2$ degree-three vertices. Hence the reduced forest has $O(L+1)$ vertices, path relations and truth tables. Its terminal predicate is exactly the original forest predicate on **every** assignment to the $L$ ports. Restoring the equalities and existentially choosing the $b$ shared bits recovers the original external predicate. Given indexed ports and edges, the reductions use $O(|V|+|E|+h+1)$ word operations.

There are at most $C^{L+1}$ possible reduced forests with ordered terminal positions before names and pairs are assigned, for an absolute $C$. For instance, root and order the trees and their children, encode the shapes with parentheses and encode the local tables, port orders and binary edge relations using a constant number of bits per node. The root markers and the one possible constant rejection fit in the same bound. Numbering the external terminals and pairing the remainder now gives
$$
     \binom{L}{h}h!\,\frac{(2b)!}{2^b b!}
                  =\frac{(h+2b)!}{2^b b!}
$$
descriptions per ordered layout. The pairs carry no individual names. An upper bound for the number of external predicates with $b(f)\le B$ is therefore
$$
       \sum_{b=0}^B C^{h+2b+1}\frac{(h+2b)!}{2^b b!}.
$$
In particular its logarithm is $O((h+B+1)\log(h+B+2))$. When $B=O(h)$ the sharper upper bound is $(h+B)\log_2 h+O(h)$ for $h\ge2$. Indeed the $h$ named positions have at most $L^h$ choices and a perfect matching of the remaining positions has at most $(2b)^b$ choices. The constants in $O(h)$ may depend on the fixed bound for $B/h$.

For comparison, converting each retained ternary relation into at most eight forbidding clauses gives an existential CNF of width at most three and $O(h+b+1)$ clauses. Conversely, any width-three existential encoding with $s$ clauses has a bounded-arity network with $O(s+h+1)$ vertices. Use one clause table per clause and equality trees to distribute input and witness bits. Unused inputs only add tree components. Thus the cycle parameter, after the additive cost of exposing the inputs, measures the size of a bounded-width existential presentation.

## Dense proper 3-CNFs

For each set $H$ of triples of distinct input names form the monotone formula
$$
               F_H(x)=\bigwedge_{\{i,j,k\}\in H}(x_i\lor x_j\lor x_k).
$$
Setting exactly $x_i,x_j,x_k$ to zero distinguishes the presence or absence of this triple independently of every other one. There are $2^{\binom h3}$ distinct predicates. The forest count implies that, for some absolute $a>0$ and all sufficiently large $h$, a vanishing fraction of them have $b(f)\le a h^3/\log h$. For that choice of $a$ the fraction is at most $2^{-\Omega(h^3)}$.

For the upper bound, order the $2h$ signed literals and partition them into blocks of $g=\lfloor\log_2 h\rfloor$ literals, taking $h\ge4$. Within each block precompute the conjunction of every subset, including the constant true for the empty set. One can form each nonempty conjunction from a literal and the entry with that literal removed. The cost is $O(\lceil 2h/g\rceil 2^g)$ bounded-fanin gates. Negated literals require $O(h)$ further gates.

Assign each clause to its first two literals in the chosen order. For each pair $(u,v)$ and each literal block, select the precomputed conjunction of precisely the third literals of the clauses in that group. AND those block outputs to form $D_{uv}$. All clauses having that pair are equivalent to $u\lor v\lor D_{uv}$. Finally take the conjunction over the pairs. This requires $O(h^2\lceil 2h/g\rceil)=O(h^3/\log h)$ gates and the same order of input wires. Represent each gate by its Boolean relation, require the circuit output true and distribute every signal of fanout greater than one by a binary tree of ternary equality tables. The resulting graph has $O(h^3/\log h)$ edges and hence at most that many independent cycles. Every original assignment has the prescribed verdict.

## Sparse formulas using almost every natural cycle

Take three disjoint sets of $n$ input names $A_i,B_i,C_i$, with $1\le i\le n$, and fix $d\ge2$ independent of $n$. Use the union of $d$ perfect tripartite matchings of triples, with no repeated triple and with connected incidence graph. Set $h=3n$ and $m=dn$. Every clause is positive and every variable occurs exactly $d$ times. The natural clause-variable incidence graph has $3m$ edges, $h+m$ vertices and one component. Splitting each variable vertex into an equality tree with one external input preserves the cycle count. Thus every such $f$ has
$$
                    b(f)\le 2m-h+1=(2d-3)n+1.
$$

A matching consists of triples $(A_i,B_{\pi(i)},C_{\rho(i)})$ for permutations $\pi,\rho$. Choose ordered matchings, requiring that $\pi_1^{-1}\pi_2$ be an $n$-cycle. The union of the first two matchings connects the $A,B$ classes and the first reaches every $C$ vertex. Exactly $(n!)^{2d}/n$ choices satisfy the cycle requirement. For $n\ge2$ the first two matchings never share a triple. For any other pair of layers, at a fixed $A_i$ the chance of sharing a triple is $1/n^2$, since at least one layer is independent and uniform. The expected total number of repeated pairs of triples is $O_d(1/n)$. At least half of the choices have no repeats for all large $n$. Any resulting hypergraph is counted at most $(d!)^n$ times because assigning layer labels to the $d$ triples at each $A_i$ determines the entire ordered list. Distinct hypergraphs have distinct predicates by the three-zero test. Their number is at least
$$
              \frac{(n!)^{2d}}{2n(d!)^n}
                   \;=\;2^{2dn\log_2 n-O_d(n)}.
$$

Compare this lower count with the forest upper count at $B=(2d-3)n-K_dn/\log_2 n$ rounded down. For sufficiently large constant $K_d$, at most a $2^{-\Omega_d(n)}$ fraction of the family admits such a network. Consequently an overwhelming fraction of the distinct predicates in this connected decomposable family satisfy
$$
             2m-h-O_d(n/\log n)\le b(f)\le 2m-h+1.
$$
This also includes $d=2$, where the obvious occurrence network has $n+1$ independent cycles. Counting unlabeled pairs in the forest is needed to recover this leading coefficient.

## What a SAT program actually returns

These bounds require one reusable network for all externally imposed truth assignments to a fixed formula. With dense variable names the sparse formulas above occupy $\Theta(n\log n)$ ASCII bits. A globally correct SAT program can recognize a well-formed formula of positive clauses and accept it in $O(N)$ time on $N$ encoded bits, since the all-ones assignment witnesses every such file. On a promise of proper positive input, even that validation is unnecessary. The representation lower bound and the running time of a solver that returns one verdict measure different tasks.
