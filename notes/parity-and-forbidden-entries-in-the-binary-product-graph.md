# How much of the binary matrix product must an exact tensor network see?

Let $P=AB$ for two $d\times d$ matrices over $\mathbb F_2$, put $D=d^2$, and give all external indices one bit each. The network coefficient field $F$ can be different from $\mathbb F_2$. Write $G_d(A,B,C)=[P=C]$ and $g_d(A,B,Z)=\langle P,Z\rangle\bmod 2$, with the scalar answer represented by $0_F$ or $1_F$. The inner product pairs corresponding entries. Thus $g_d$ is the parity of the explicitly specified cubic terms $A_{ik}B_{kj}Z_{ij}$. Write $V_F$ for minimum volume of an exact binary-wire tensor network with tensors of arity at most three, charging for copying.

* In every field the graph and the predicate that **no marked output entry is one** have volumes differing by at most $D$ two-wire tensors.
* In characteristic different from two the volume exponents of the graph and the **one-bit cubic parity** coincide. A single copy of a scalar network at side $d+1$ recovers the graph at side $d$ with $O(D)$ extra volume.
* If an unknown $D$-bit output is accessible solely through scalar parity queries, the exact weighted-query cost of equality is **one** in odd characteristic or characteristic zero and **$D$** in characteristic two. With residual rank at most $r$ and at most $s$ wrong entries, the characteristic-two optimum is exactly $\min(dr,s)$. This is a bound on what a black-box reduction can recover from the parity answers. A graph network receiving $A,B$ directly may use all their entries.

The changes of basis here are standard tensor operations. The point for the SAT attack is to specify which Boolean predicate an exponent lower bound would have to cover, and precisely where scalar access loses information. [Valiant, *Holographic Algorithms*](https://people.seas.harvard.edu/~valiant/holographic11-07.pdf) · [Bernstein and Vazirani, *Quantum Complexity Theory*](https://epubs.siam.org/doi/10.1137/S0097539796300921) · [The graph-to-SAT transfer](list-and-matrix-costs-for-ram-and-tapes.md)

## A forbidden-entry mask over any field

Attach a two-wire tensor to each $C$-leg of the graph, with row $z$ and column $c$, using
$$
 K=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
 K^{-1}=\begin{pmatrix}0&1\\1&-1\end{pmatrix}.
$$
On external mask $Z$, summing the old legs gives $\prod_{ij}K(Z_{ij},P_{ij})$. This is the bit asserting that the marked entries of $P$ are all zero. Replacing every $K$ by $K^{-1}$ in the reverse transformation recovers the graph. The determinant is $-1$ in every field. Each old external index becomes a single internal wire.

There is also a Boolean projection from the graph test to the forbidden-entry test at side $2d$, with constants, copies, and input negations. Take the top $d$ rows of $A'$ to be $[A\mid u\mid 0]$ where $u$ is the all-ones column. Take the top $d$ rows of $B'$ to be $[B\mid B]$ and row $d+1$ to be zero in its first $d$ entries and one throughout the last $d$. All remaining entries of both matrices are zero. The top output blocks are $P$ and its bitwise complement. Mark their entries respectively by $1-C$ and $C$, leaving the lower blocks unmarked. A marked one exists precisely when a proposed bit is incorrect. Repeated use of an external bit costs $O(D)$ explicit copying or negation sites for the whole construction.

## One scalar bit in odd characteristic

Put $H(z,c)=(-1)^{zc}$. Applying the two-wire matrix $H$ on each proposal leg gives the sign tensor $S_d(A,B,Z)=(-1)^{g_d(A,B,Z)}$. If $2$ is invertible then $H^{-1}=H/2$, so the graph and the sign cost at most $D$ extra sites in either direction. Separately, an exact graph network gives the scalar bit in every field by contracting the product legs with a deterministic circuit that accepts if the selected entries have odd parity. Every product and accumulator value has a unique consistent setting. The circuit takes $O(D)$ sites, including all copies.

To recover the sign from the scalar bit with a *single* network, set
$$
 A'=\operatorname{diag}(A,1),\quad B'=\operatorname{diag}(B,1),\quad
 Z'=\operatorname{diag}(Z,t).
$$
Then $g_{d+1}(A',B',Z')=g_d(A,B,Z)\oplus t$. Contract the new bit $t$ against the unary weights $(-1,1)$. The resulting value is $(1-g_d)-g_d=S_d$. All pinned legs cost $O(d)$ sites. Consequently
$$
 V_F(g_d)\le V_F(G_d)+O(D),\qquad
 V_F(G_d)\le V_F(g_{d+1})+O(D)\quad(\operatorname{char} F\ne2).
$$
The scalar is the value of a Boolean function on binary matrices. Substituting its formal arithmetic trilinear polynomial over a different coefficient field would generally give a different value even on binary inputs. A small exact tensor network can use cancellations among internal configurations.

## Exact cost with only parity queries

Let $X$ be any hidden binary word of length $D\ge1$, and let $C$ be public. Allow a finite weighted sum of decision trees, with arbitrary coefficients in $F$. At each node one may choose a mask $Z$ from previous answers and request the single bit $\langle X,Z\rangle$. The price is the maximum number of queries on any branch. The answer must equal $[X=C]$ as a field element for each $X$. The sum may have exponentially many terms. Every $X$ here can be a binary matrix product, by setting $A=I$.

When $2$ is invertible the exact Walsh identity
$$
 [X=C]=2^{-D}\sum_{Z\in\{0,1\}^D}(-1)^{\langle C,Z\rangle}(-1)^{\langle X,Z\rangle}
$$
has one query per term, and zero queries could give only a constant. For characteristic two, fix any leaf attained after at most $k<D$ questions. Its masks and answers are fixed once the path is fixed. The hidden words leading there solve a binary linear system of rank at most $k$. An empty fiber contributes zero, and a nonempty one has $2^{D-\mathrm{rank}}$ elements, also zero as a scalar in $F$. Summing the leaf contribution over all $X$ therefore gives zero. Linearity makes this true of every allowed weighted program of depth below $D$, whereas the target sums to one. Querying all $D$ coordinates attains the bound. Lean verifies that arbitrary field-weighted families of these short transcript indicators cannot isolate a single point, allowing a different binary query matrix for every transcript. [Lean theorem over all characteristic-two fields](../upstream-checks/ParityQueryFiber.lean)

This also proves the same dichotomy over any nonzero commutative ring with identity. If 2 is a nonunit, reduction modulo a maximal ideal containing 2 gives the characteristic-two obstruction.

## Errors promised to be low-rank, sparse, or both

Suppose $E=X+C$ has binary rank at most $r$ and Hamming weight at most $s$, with $0\le r\le d$ and $0\le s\le D$. The exact characteristic-two depth is
$$
                              \min(dr,s).
$$
For the lower bound, allow precisely $\min(dr,s)$ free coordinates among the first $r$ rows of $E$ and set everything else to zero. Every point of this cube obeys both promises, and the same leaf-fiber sum applies on the cube. In the query model each bit of $C$ is public, so querying a parity of $E$ costs one parity of $X$.

For the upper bound $s$, expand $\prod_i(1-E_i)$ and retain only monomials of degree at most $s$. All discarded monomials vanish on the promised errors. Each retained term costs at most $s$ single-coordinate queries on its branch. For the upper bound $dr$, use the $dr$-bit syndrome of a binary linear rank-metric code of dimension $d(d-r)$ and minimum nonzero rank at least $r+1$. Concretely, represent matrices as binary-linear maps of $\mathbb F_{2^d}$ in a fixed basis. For $r<d$ the code consists of $x\mapsto\sum_{i=0}^{d-r-1}a_ix^{2^i}$. A nonzero polynomial here has at most $2^{d-r-1}$ roots, hence kernel dimension at most $d-r-1$ and rank at least $r+1$. The same root bound makes the coefficient parametrization injective. For $r=d$ take the zero code. The syndrome of $E$ consists of $dr$ fixed scalar parity queries and vanishes exactly at the code. Under the rank promise its vanishing means $E=0$. For odd characteristic one signed query still suffices whenever $\min(dr,s)>0$; if the promise forces $E=0$, the answer is constant in every field. For a separate computational check, a leaf indicator in characteristic two is a product of affine linear polynomials in the bits. Every coordinate monomial can in turn be implemented by a branch. Hence the optimal depth on a promise is exactly the least degree at which the point indicator lies in the restricted multilinear polynomial space. The rank code and its factored implementation are classical ingredients. The lower bound here also covers sums with cancellations among adaptive query transcripts. [Delsarte, *Bilinear forms over a finite field*](https://doi.org/10.1016/0097-3165(78)90015-8) · [Gabidulin, *Theory of codes with maximum rank distance*](https://www.mathnet.ru/php/archive.phtml?jrnid=ppi&option_lang=eng&paperid=967&wshow=paper) · [Factored syndrome and finite checks](rank-neighborhoods-of-the-binary-product-graph.md)

This separates two uses of the November 24 result. A lower bound $d^{2+\delta-o(1)}$ for exact scalar-parity networks in a fixed odd-characteristic field would exclude SAT time $O(n^k)$ for every $k<1+\delta/2$, using the trace-verification reduction. The formal exponent $9/4$ does not supply the scalar-parity network lower bound. Over characteristic two, $D$ is an exact obstruction to extracting the whole verdict using only weighted parity queries, even though a concrete circuit for $g$ may have internal structure a reduction could exploit. The finite audit contracts the actual tensors and checks the two padded constructions on every binary matrix triple at sides one and two. It also computes the least restricted degree by binary elimination on every one of the 59 rank and weight promises at sides one through three. [Audit](../audits/matrix_graph_basis_audit.py) · [Exact SAT transfer and endpoint accounting](list-and-matrix-costs-for-ram-and-tapes.md) · [Earlier trace-phase circuit restriction](hadamards-in-a-matrix-product-phase.md) · [Upstream matrix multiplication preprint](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026)

On direct binary factors, characteristic two admits a near-quadratic network for the full graph by batching all the read requests of one modular expansion. The black-box parity depth lower bound above coexists with this upper bound. [Exact graph construction](matching-characteristic-networks-for-binary-products.md)
