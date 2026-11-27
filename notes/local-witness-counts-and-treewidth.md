# Local witness counts and treewidth

Let a satisfiable Boolean CNF on \(n\ge1\) counted variables have \(M\) satisfying assignments. Fix any one of them, \(a\). For a prime \(p\), let \(t_p(a)\) be the minimum number of variables one must pin **to their values in \(a\)** to get a witness count nonzero modulo \(p\). The empty restriction is allowed. In particular \(t_p(a)=0\) when \(p\nmid M\), and pinning everything leaves exactly one witness. All logarithms in the inequalities below are to base two.

**Separator bound.** If the primal graph has treewidth at most \(w\), then
\[
\sum_{p\ {\rm prime}} t_p(a)\log_2 p
\;\le\; (w+1)n(1+\lfloor\log_2 n\rfloor).
\]
The primal graph joins two variables whenever they occur in the same clause. The bound applies in particular to 3-CNF and includes counted variables used by auxiliary gates. If all restrictions of at most \(r\) variables have counts divisible by every prime up to \(K\), then
\[
 (r+1)\sum_{p\le K}\log_2 p
 \;\le\;(w+1)n(1+\lfloor\log_2 n\rfloor).
\]
The prime sum is \(\Theta(K)\) for large \(K\) by Chebyshev's estimate. Even the hypothesis limited to restrictions consistent with this one fixed \(a\) suffices.

Take a separator recursion on the variable sets \(U_v\). At node \(v\) remove a set \(S_v\subseteq U_v\) of at most \(w+1\) variables so each child component has at most \(|U_v|/2\) variables. Such a separator is obtained by assigning each vertex to one of its bags in a width-\(w\) tree decomposition and taking a weighted centroid bag. A graph component avoiding that bag lies in one component of the remaining decomposition tree, by connectedness of each vertex's bags and the shared bag of every adjacent pair. Restrict the decomposition to each recursive component. A one-variable leaf can use its sole vertex as separator. This gives at most \(1+\lfloor\log_2 n\rfloor\) nonempty sets on any root-to-leaf path. [Dvořák and Norin, *Treewidth of graphs with balanced separations*](https://doi.org/10.1016/j.jctb.2018.12.007)

For each node, independently of the prime, set the ancestor separators to their values in \(a\). Let \(M_v\) count extensions on \(U_v\) satisfying all residual clauses in that component. Clauses with no remaining variables are satisfied by \(a\); remaining clauses belong wholly to one component. Thus \(1\le M_v\le2^{|U_v|}\). When one additionally pins \(S_v\) to \(a\), the count in that component becomes \(\prod_{u\text{ child of }v}M_u\), with the empty product equal to one. The original unpinned \(M_v\) can differ from this product.

For a given \(p\), start with the root. Whenever a current node satisfies \(p\mid M_v\), pin its separator and replace the node by its children. Stop at nodes whose counts are units modulo \(p\). At termination the witness count is a product of such units, by independence of the remaining components. The cost is the sum of \(|S_v|\) over expanded nodes. At each fixed \(v\), all primes that expand it divide the **same positive integer** \(M_v\), so their log sum is at most \(\log_2 M_v\). Summing the costs gives the more precise estimate
\[
  \sum_p t_p(a)\log_2p
  \le \sum_v |S_v|\log_2 M_v
  \le (w+1)\sum_v |U_v|.
\]
The sets at each depth are disjoint, proving the claim. The restrictions are allowed to differ between primes. They give witnesses for an existential statement about counts and do not assume an algorithm for finding \(a\).

## Binary constraints on a path

Suppose the variables have Boolean unary constraints and arbitrary Boolean binary constraints between consecutive positions in one fixed order. On this class the stronger inequality
\[
       \sum_p t_p(a)\log_2 p\ \le\ \log_2 M\ \le\ n
\]
holds for every satisfying assignment \(a\). This gives \((r+1)\sum_{p\le K}\log_2p\le\log_2 M\) under the same restriction hypothesis.

Intersect the constraints on each adjacent pair into its single \(2\times2\) zero-one transition matrix. A missing constraint gives the all-ones matrix. Each nonzero singular matrix of this kind has support equal to a Cartesian product of two unary sets: its nonzero rows coincide, or it has just one nonzero row. Replace it by the two unary tests and delete that link. A variable forced to one value can be removed, intersecting the induced unary condition into each neighbour's allowed set. These operations preserve counts and the remaining components are independent. They cost no pins because they hold for every solution. Satisfiability rules out empty allowed sets. Repeat until obtaining independent blocks of unforced variables whose links are all nonsingular. Each surviving transition matrix has determinant \(1\) or \(-1\).

In a block \(B\), the row vector of counts conditioned on the last variable is \((1,1)A_1\cdots A_k\); a singleton block uses the empty product. Its entries sum to \(M_B\). Modulo any prime the vector is nonzero because every factor is invertible. If \(p\mid M_B\), both entries of the vector must be nonzero modulo \(p\). Fixing the last variable of that block to its value in the already chosen \(a\) suffices. Pin one variable in each \(p\)-divisible block and leave the other blocks free. Summing over primes costs at most \(\sum_B\log_2 M_B=\log_2 M\).

The sharper inequality can be an equality. Take \(s\) independent pairs constrained to equal Boolean values and \(u\) independent pairs constrained by one positive binary clause. Their respective block counts are two and three. Every successful restriction modulo two must touch all \(s\) equality blocks, and every successful restriction modulo three must touch all \(u\) clause blocks. One pin per such block suffices, also for a preselected \(a\). Hence \(t_2(a)=s\), \(t_3(a)=u\), and \(2^s3^u=M\). The path argument uses two Boolean states on a chain; the separator proof above is what applies to general bounded-treewidth CNFs.

## Unrestricted witness sets need only additive space

For every integer \(L\ge2\) and \(r\ge0\) there is a nonempty binary witness set on \(v=O(r+\log_2 L)\) variables such that fixing **any** \(h\le r\) coordinates to **any** values leaves a positive multiple of \(L\) witnesses. Conversely any nonempty set for which all counts under at most \(r\) pins are divisible by \(L\), even allowing zero counts, has \(\log_2 M\ge r+\log_2 L\). To see this, split a positive fibre at depth less than \(r\) on a coordinate on which two of its witnesses differ. Two witnesses exist since its positive size is divisible by \(L\). Each of the \(2^r\) resulting positive leaves has at least \(L\) elements. Thus also \(v\ge r+\log_2 L\).

For the construction let \(k=\lceil\log_2L\rceil\), \(v=4(k+r+1)\), and choose a uniform binary \(k\times v\) matrix \(A\). For each nonzero row combination its weight \(W\) is binomial with parameters \(v,1/2\). Thus \(\mathbb E[2^{-W}]=(3/4)^v\), and the probability that any such combination has weight at most \(r\) is at most \((2^k-1)2^r(3/4)^v<1\). Fix a matrix avoiding that event. After any \(h\le r\) columns are deleted, its remaining columns still span \(\mathbb F_2^k\), since an annihilating nonzero row combination would be supported on the deleted columns. Accept exactly those \(x\) for which the binary integer represented by the syndrome \(Ax\) is less than \(L\). After fixing \(h\) bits of \(x\), each syndrome occurs \(2^{v-h-k}\) times. The restricted count is exactly \(L\,2^{v-h-k}\). This uniform projection property of a linear-code coset is classical: the dual minimum distance exceeds the strength of the corresponding orthogonal array. [Delsarte, *An algebraic approach to the association schemes of coding theory*, §4.1.3](https://users.wpi.edu/~martin/RESEARCH/philips.pdf)

Taking \(r=K\) and \(L=\operatorname{lcm}(1,\ldots,K)\) gives \(v=\Theta(K)\), since \(\log L=\Theta(K)\). This set can be written as a CNF on just the \(v\) counted variables by forbidding each rejected point with one full-width clause. The product \((r+1)\sum_{p\le K}\log_2p\) is then \(\Theta(K^2)\), showing why the earlier separator bound needs a structural parameter. The truth-table CNF may be exponentially large. For every odd prime \(p\) dividing \(L\), the restricted counts above have exactly the same \(p\)-adic valuation as \(L\). A stronger guarantee of divisibility by \(L^{r+1-h}\) after \(h\) pins already requires \(v\ge (r+1)\log_2 L\) at \(h=0\).

Introducing the raw syndrome as counted auxiliary bits can destroy even the single-factor guarantee. For \(L=3\), \(r=1\), take the rows \(110\) and \(011\). The three accepted syndromes \(00,01,10\) have two preimages each. Every one-pin restriction on an original bit leaves three witnesses. Pinning the first syndrome bit instead leaves four or two witnesses. More generally, when \(r\ge k\), fixing all syndrome bits to one accepted value leaves a single coset of size \(2^{v-k}\), which loses every odd prime factor of \(L\).

## A three-literal permutation construction with fewer counted variables

Take \(s=q^2\) to be the least square at least \(r+K\), for \(K\ge2\). A satisfiable 3-CNF using \(O(s^{3/2})\) counted variables preserves divisibility by \(\operatorname{lcm}(1,\ldots,K)\) after **arbitrary** restrictions on at most \(r\) of them. Its number of clauses is \(O(s^2\log s)\). In particular at \(r=K\) this beats the quadratic **variable** cost and supplies no subquadratic encoded-length bound.

For each of \(s\) rows \(i\), encode its forward label by two base-\(q\) digits, each a one-hot vector of length \(q\). Enforce exactly one bit per digit with at-most-one binary clauses and a prefix OR circuit whose output is pinned true; all its gate values are uniquely determined and private to that row. Give each of the \(s\) label columns \(j\) a binary inverse identifier \(Q_j\) with \(\lceil\log_2 s\rceil\) bits. If \(j\) has digits \((u,v)\), insert, for every bit of \(i\), the clause
\[
  \neg H_{i,u}\;\lor\;\neg D_{i,v}\;\lor\;(Q_{j,\rm bit}=i_{\rm bit}).
\]
The final expression is a literal. Two different rows cannot choose the same label, since they would force two different inverse identifiers. There are as many rows as labels, hence the forward map is a permutation, and every inverse identifier is forced. Conversely each permutation extends uniquely. Short clauses here have their usual meaning in width-at-most-three CNF. They can also be made proper using three shared forced-false bits with their unique satisfying values.

For any assignment to at most \(r\) pinned variables consider its satisfying extensions. Partition those extensions by the full values of \(Q_j\) at every inverse column touched by a pin. In a nonempty part, fix the rows named by those identifiers and the rows containing any pinned forward or prefix-circuit variable. This fixes at most \(r\) rows in total. The group permuting all other rows acts within the part by permuting forward records, recomputing inverse identifiers and using the unique local gate values. It acts freely because the forward records have distinct labels. The size of this part is therefore divisible by \((s-r)!\), as is their sum. Pins on shared forced constants either do nothing or make the count zero. This construction requires no claim about permutations of intermediate gates in a sorting network.
