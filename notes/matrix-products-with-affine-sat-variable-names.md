# Matrix-product checks with field elements in SAT variable names

Can a reduction send a field element to ordinary SAT without branching on any of its individual bits? One possibility puts each scalar in a variable name. SAT observes equality of those names, and a common injective renaming preserves satisfiability. In the following precise model this idea admits upper and lower bounds that match up to logarithms across all prime field sizes.

Fix the clauses, their literal positions and signs independently of the input matrices $A,B,C\in\mathbb F_q^{d\times d}$. At each position supply a variable name of the form $(\tau,f(A,B,C))$ with a fixed namespace $\tau$ and an affine scalar form $f$ in **all** input coordinates over $\mathbb F_q$. Constant names and disjoint auxiliary namespaces are allowed. The output verdict may uniformly be SAT for a correct product or for an incorrect product. Let $K$ count the distinct tagged affine maps that occur. Write $M\le\binom K2$ for the number of unordered pairs of distinct maps in the same namespace.

**Lower bound.** Every such encoding exact on all input triples satisfies
$$
d^2\ \le\ M\left(\frac{2}{q}+\frac1{q-1}\right).
$$
Also $K-u\ge d^2$, where $u$ is the number of nonempty namespaces. Hence $K=\Omega(d^2+d\sqrt q)$. This prices the reduction alone, even if checking the completed formula takes no time.

**Upper bound.** For prime $p$, there is a fixed width-three template for a product mismatch whose names have the required form and whose number of literal occurrences is
$$
O\bigl((d^2+d\sqrt p)\log(p+1)+d\log^2(p+1)\bigr).
$$
Converting its names to physical DIMACS integers costs one further $O(\log(dp+2))$ factor in encoded bit length. The names are opaque field elements at the level of satisfiability. Emitting their ordinary decimal representations and running a native SAT solver still permit binary operations on the numerical representations.

## Why the partition must change at many true points

The $Y$-coefficient vectors of every same-tag difference lie in a span of dimension at most $K-u$: compare each name to one chosen representative in its namespace. If $K-u<d^2$, a nonzero shift $Z$ annihilates all those differences. Then $C$ and $C+Z$ give exactly the same name partition for every $A,B,C$, violating correctness at $C=AB$. This proves the first dimension bound.

Discard duplicate tagged maps. The restriction of every distinct same-tag difference to $(A,B,AB)$ is a nonzero formal polynomial of degree at most two. Indeed an affine identity on the product graph first has zero constant term, then zero coefficients on $A$ and $B$ by setting one matrix to zero, and finally zero coefficients on $C$ by taking products of elementary matrices. A degree-two nonzero polynomial vanishes under independent uniform field substitutions with probability at most $2/q$ by the elementary polynomial root bound. Choose $A,B$ at which at most $E\le 2M/q$ pairs coincide.

Keep these matrices fixed and vary the proposal from $C=AB$ to $C+Z$. The equalities that actually held impose at most $E$ linear homogeneous conditions on $Z$. Their joint solution space $W$ has dimension at least $d^2-E$. For every $Z\in W\setminus\{0\}$ at least one formerly unequal pair must become equal. Otherwise every occurrence has exactly the same relation of equal names as on the true point, and the two CNFs differ only by a variable renaming while their required verdicts differ.

Use linear coordinates on $W$. The at most $M$ formerly unequal affine differences have a product which is nonzero at the origin and zero at every other point of $W$. Its individual-degree-reduced representative is a nonzero scalar times $\prod_{i=1}^{\dim W}(1-Z_i^{q-1})$. Reduction by $Z_i^q=Z_i$ cannot increase total degree, and uniqueness of the representative follows by induction on the number of variables. Thus $M\ge(q-1)\dim W$, which proves the bound. For a sharper constant, write the coefficient matrices of $B,C$ in a pair difference as $V,G$. If $G$ has rank $r\ge1$, then at fixed $A$ the coefficient of $B$ on the graph is $V+A^{\mathsf T}G$. It vanishes for a fraction at most $q^{-dr}$ of the $A$, since each column of $A$ must solve an independent rank-$r$ linear system. Otherwise the conditional coincidence probability is exactly $1/q$. If $G=0$ a nonconstant affine difference has probability $1/q$ and a distinct constant difference has probability zero. Thus one can take $E\le M\gamma$ with $\gamma=1/q+(1-1/q)q^{-d}$. There are only $M-E$ formerly unequal pairs, so $M-E\ge(q-1)(d^2-E)$. In particular $d^2\le M[1+(q-2)\gamma]/(q-1)$. This is the punctured-grid hyperplane covering argument. [Alon and Füredi](https://kam.mff.cuni.cz/~ksemweb/clanky/AlonFuredi-covering_the_cube.pdf) · [Bishnoi, Clark, Potukuchi and Schmitt, Theorem 6.1(c)](https://arxiv.org/abs/1508.06020)

## Shared names recover binary values using a short table

More generally, take $n$ input scalars in $\mathbb F_p$. Put $h=\max(1,\lceil\sqrt{p/n}\rceil)$, $b=\lceil\log_2p\rceil$, and let
$$
S=\{0,h,2h,\ldots,\lfloor(p-1)/h\rfloor h\}.
$$
The cyclic gap between successive table entries is at most $h$, including the wrap to zero. Every $x\in\mathbb F_p$ therefore has a shift $0\le k<h$ with $x+k\in S$.

Use one namespace for Boolean markers $M_v$ and $b$ more for value bits $L_{t,v}$. At every $v\in S$ place a positive unit for $M_v$ and units for the ordinary binary digits of $v$ at $L_{t,v}$. For each scalar $x_i$ introduce an auxiliary $b$-bit word $X_i$. For each integer $0\le k<h$, use $M_{x_i+k}$ to guard the requirement that $X_i$ equals the canonical residue of the value encoded by $(L_{t,x_i+k})_t$ minus $k$ modulo $p$. A Boolean comparison, subtraction and conditional addition of $p$ cost $O(b)$ bounded-fan-in gates; the guard may require the table value to be canonical. Impose gate equivalences with fresh auxiliary variables and guard the final comparison. All literal signs and structural names are fixed. The only data-dependent names evaluate $x_i+k$ in the appropriate fixed namespace.

At a forced table hit the pinned marker and value determine $X_i$ uniquely as the correct binary encoding. Several hits produce that same value. Conversely, setting all markers outside $S$ false makes all remaining guards vacuous; each correct $X_i$ then has an extension to all gate variables. This holds simultaneously for every coordinate, including arbitrarily many aliases. The table and guarded decoders use $O((p/h+nh)b)=O((n+\sqrt{np})\log(p+1))$ literal occurrences. For $p<n$ there are $p$ table entries and $h=1$, with the same bound.

For matrix multiplication set $n=3d^2$. Guess indices $i,j<d$, select all $A_{ik},B_{kj}$ and $C_{ij}$ from the decoded words with $O(d^2 b)$ Boolean multiplexer gates, and compare the claimed entry with the dot product. Ordinary schoolbook Boolean modular multiplication and modular addition use $O(b^2)$ gates per term, including reduction by a fixed modulus via binary long division. The mismatch checker therefore costs $O(d^2 b+db^2)$ gates. It has a satisfying assignment precisely for an incorrect product. Translate the bounded-fan-in circuit with its output pin to width-three clauses. For physical printing, number the fixed auxiliary names and use a distinct interval of length $p$ for each field namespace. The largest variable identifier is polynomial in $d,p$, giving the stated physical bit bound. [Binary matrix-product mismatch verifier](verifying-matrix-products-from-sat.md)

At $p\le d^2\operatorname{polylog}d$ this gives an actual quasiquadratic-bit SAT file with only affine scalar names and a fixed template. At $p=d^{2+\epsilon}$ the literal-count lower bound alone is $\Omega(d^{2+\epsilon/2})$. Thus one cannot make the alphabet indefinitely larger to support a low-degree verification theorem while retaining this form of near-quadratic encoding. A linear-time SAT solver on the constructed files would still operate on ordinary packed bits and have unrestricted memory. Deriving a degree or derivative bound for that whole computation is open. The reduction bounds do not establish a SAT running-time lower bound or a claim of historical priority. [Finite-field degree criterion](finite-field-dense-equality-tests.md) · [Finite checks](../audits/dense_product_verification_audit.py)
