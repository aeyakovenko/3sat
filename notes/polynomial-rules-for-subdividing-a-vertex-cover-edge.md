# Which polynomial rules preserve a vertex cover when an edge is subdivided?

Let a bit at each vertex indicate membership in a proposed vertex cover. Subdivide a designated edge by a new vertex, keep all the old bits, and choose the new bit as a Boolean function of them. We characterize all degrees of rules that preserve the cover verdict on every input. For a cycle on $n\ge5$ vertices there is one affine rule and exactly $2^{n+3}$ rules of degree at most two per gap. For an arbitrary simple graph the number of affine rules at an edge $uv$ is $2^h$, where $h$ is the number of common neighbors of $u$ and $v$.

These counts apply to both verdicts. The resulting maps are injective since they retain every original bit. The result gives an exhaustive parameterization for the [finite RAM experiment](a-strict-clock-increase-under-one-bit-cycle-subdivision.md). The experiment measures optimal executed instructions on a selected set of inputs. The existence of a verdict-preserving rule puts no lower bound on that time.

## The rows that constrain the new bit

Use $x_i=1$ for a selected vertex and $y_i=1+x_i$ for an omitted vertex, with arithmetic over the two-element field. Inserting $x_u+x_v$ between the endpoints preserves the verdict. Write the actual inserted bit as $x_u+x_v+g(x)$.

If any retained edge has both endpoints omitted, either inserted bit gives the same verdict. If every retained edge is covered and both endpoints of the removed edge are selected, either bit again works. In every other case exactly one bit works. When both endpoints are omitted the new bit must be zero. When just one is omitted it must be one. Consequently the new bit is forced precisely when the omitted vertices form an independent set of the graph with edge $uv$ deleted, and that set contains $u$ or $v$. The correction $g$ must vanish on this collection and is free elsewhere.

## A basis for a cycle, at every degree

Number the retained path $1,2,\ldots,n$ so the subdivided edge is between $1$ and $n$. Suppose $n\ge5$. Change only the endpoint coordinates of the vector $y$, using
$$
q_1=1+y_1+y_2,\qquad q_n=1+y_n+y_{n-1},\qquad q_i=y_i\quad(2\le i\le n-1).
$$
This is an affine involution and preserves the degree filtration. Let $G_n$ have the path from 2 through $n-1$ and all six edges of the clique on $1,2,n-1,n$.

**Basis theorem.** In the $q$ coordinates, the corrections $g$ of degree at most $d$ have as a basis precisely the squarefree monomials of degree at most $d$ whose supports contain an edge of $G_n$.

To see the change of coordinates, write each endpoint pair in the order (endpoint, neighbor). The three allowed $y$ patterns 00, 10, 01 become the $q$ patterns 10, 00, 01 respectively. An omitted endpoint becomes an empty pair. At least one endpoint must be omitted on a constrained row. Thus across the four boundary coordinates there can be at most one 1. The internal path constraints are identical before and after the change. Invertibility gives an exact correspondence between constrained rows and independent sets of $G_n$.

For any independent set $S$, polynomial evaluation at its indicator is the XOR of coefficients of monomials indexed by subsets of $S$. Every such subset is independent. Induction on $|S|$ shows that all evaluations vanish there if and only if all coefficients on independent sets are zero. The remaining monomials are linearly independent by uniqueness of Boolean algebraic normal form. The underlying basis-by-faces observation is classical. [Björner, Frankl and Stanley on face rings](https://math.mit.edu/~rstan/pubs/pubfiles/68.pdf) · [Carlet on Boolean algebraic normal form](https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf)

In particular no nonzero affine correction is possible. There are $n+3$ independent quadratic corrections, one for each edge of $G_n$, so exactly $2^{n+3}$ preserving rules have degree at most two. To count higher degrees let $P_m(t)$ count independent sets of a path on $m$ vertices by cardinality, including the empty set. Thus $P_0=1, P_1=1+t$ and $P_m=P_{m-1}+tP_{m-2}$. The independence polynomial of $G_n$ is
$$
I_{G_n}(t)=(1+2t)P_{n-4}(t)+2tP_{n-5}(t).
$$
If the clique is empty or its selected vertex is 1 or $n$, the $n-4$ internal vertices are available. Selecting 2 or $n-1$ excludes one end of that internal path. The number of additional independent correction coefficients available at degree $j$ is therefore $\binom{n}{j}-[t^j]I_{G_n}(t)$. Exponentiating the cumulative sum through $d$ gives the number of rules of degree at most $d$ for $d\ge1$.

## The rank formula for every simple graph

Use a simple graph on $n$ vertices with designated edge $uv$. On the remaining vertices let $A$ be the family of independent sets that avoid the neighbors of $u$, and define $B$ with $v$ in its place. Put $C=A\cap B$. Write $I_D(t)=\sum_{S\in D}t^{|S|}$ for any such family. Define $r_d$ as the increase from degree $d-1$ to degree $d$ in the rank of evaluating Boolean polynomials on the constrained rows. Start at rank zero before degree zero. Then
$$
\sum_{d\ge0}r_dt^d=I_A(t)+I_B(t)+(2t-1)I_C(t).
$$
The degree-at-most-$d$ correction space has dimension $\sum_{j=0}^d(\binom{n}{j}-r_j)$.

For a proof, split the constrained rows by their two omitted-endpoint bits. The patterns $10,01,11$ have internal supports in $A,B,C$ respectively. Within each pattern replace its evaluations by their Boolean Möbius transform on internal subsets. Each of these three transforms is invertible because its family is downward closed. For a fixed internal support $S$, the transformed entries now depend only on coefficients with internal support exactly $S$. Distinct supports give independent blocks of the evaluation matrix.

At degree $|S|$, only the constant endpoint monomial is available in the block. Its column has rank one whenever $S\in A\cup B$. If only one of $A,B$ contains $S$, this is already the full block. If both contain $S$, all three endpoint patterns occur. At degree $|S|+1$, the endpoint monomials $1,y_u,y_v$ are independent on these three patterns over the two-element field. The rank increases by two and the block is full. Summing the increments gives $I_{A\cup B}+2tI_C$ as asserted.

Every internal vertex except a common neighbor belongs as a singleton to $A\cup B$. Since $C$ contains the empty set, the degree-at-most-one rank is $n+1-h$. The $h$ omitted-vertex coordinates of the common neighbors form a basis for all affine corrections. Each vanishes on every constrained row and they are linearly independent. Thus the affine rule at a triangle-free edge is uniquely the endpoint XOR. This also explains why subdividing an edge of a triangle has two affine rules.

## Verification

[QuadraticCycleInsertionSpace.lean](../lean/QuadraticCycleInsertionSpace.lean) proves the arbitrary-length endpoint change of coordinates, the vanishing criterion on hereditary mask families and finite quadratic rank checks. The general graph rank formula is proved above.

The [finite rank audit](../audits/subdivision_rule_rank.py) independently forms truth tables for both choices of the inserted bit, constructs the evaluation matrices, and checks the rank in every degree for all 16,933 labeled simple graphs of orders two through six containing a fixed distinguished edge. Relabeling covers an arbitrary choice of the edge. The audit also checks cycles of lengths seven through nine.
