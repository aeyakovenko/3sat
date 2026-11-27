# A single low-degree response falsifies every evaluation of a RAM read trace

Take a read-only array of $T$ field words and check its alleged read replies with a polynomial fingerprint at $d$ challenges. Even if the verifier first receives a single polynomial describing the reply at **every time and every challenge tuple**, the check can accept an impossible execution at every challenge. For $d=1$, a quadratic polynomial in time and affine polynomial in the challenge changes all but at most two of the $T$ reads. This time degree is optimal. For $d$ independent simultaneous field challenges and $T\ge 3d+1$, the optimum is $2d$ when the response is multilinear in their values.

This tests an attempted shortening of a SAT encoding of a failed RAM run. A positive answer for each fingerprint need not certify the same run. The journal's earlier counting argument permits unrelated counterfeits for different challenges, and applies to a broad class of summaries. Here all the counterfeits have a single algebraic description, fixed before the challenges are known. The fingerprint analyzed is the evaluation of the **time-indexed payload polynomial**. [Earlier collision argument and its different quantifiers](separate-fingerprint-witnesses.md) · [Rabin on algebraic fingerprints](https://www.cs.cmu.edu/~15-749/READINGS/optional/rabin1981.pdf)

## The native computation and its checker

Use a deterministic logarithmic-word RAM with a public length $T$. It initializes $T$ fresh cells to zero, reads the same cells in increasing order, and counts how many replies are nonzero. Its only positive exit requires at least $\lceil T/2\rceil$ nonzero replies. This is a fixed rejecting program with $O(T)$ steps. Use a register for the count, and a branchless nonzero test or equal-length branch arms. The addresses, timestamps and operations of the memory probes are fixed independently of their replies.

Consider a checker verifying the CPU transitions exactly, as well as the true zero writes, addresses, order and consistency in an address-sorted memory table. Its remaining link between the two tables consists of the $d$ field sums
$$
  \sum_{j=0}^{T-1}Y(j,\mathbf a)a_i^j=0 \quad (1\le i\le d).
$$
Here $j$ numbers the designated reads. The verifier may require one committed circuit for the function $Y$, and check its full polynomial degree in the read index and the challenges. The true sorted replies are zero. Other CPU fields in a particular challenge can be reconstructed by replaying the instructions on the supplied replies. The low-degree condition here is on the designated payload column. The claim does not impose such a degree on the CPU counter or the full history.

## Sharp kernel dimension

Work over a prime field of size $q>T+d$ with $d\ge1$. Let $Y(X,\mathbf A)$ have degree at most $r$ in $X$ and degree at most one in each $A_i$. If $0\le r<T-d$, the space of such polynomials passing the displayed checks at **every** challenge tuple has dimension
$$
                   \max(0,r-2d+1).
$$

To see this, form $H(Z,\mathbf A)=\sum_{j=0}^{T-1}Y(j,\mathbf A)Z^j$. Substituting $Z=A_i$ gives a polynomial of degree at most $T$ in $A_i$ and at most one in each other challenge. Its vanishing on the entire grid forces a polynomial identity by univariate interpolation in each variable. Hence $Z-A_i$ divides $H$. These are distinct prime factors over the polynomial ring, so their product divides $H$. For nonzero $H$, polynomial degrees add in each $A_i$. Its quotient is therefore independent of every challenge:
$$
    H(Z,\mathbf A)=\prod_{i=1}^d(Z-A_i)\,G(Z),\qquad \deg G\le T-1-d .
$$
If $H=0$, coefficient comparison and $r<T$ imply $Y=0$.

Write $g_j=[Z^j]G$, with zero coefficients outside its support. The coefficient of $A_1\cdots A_d$ in $Y(X,\mathbf A)$, multiplied by $(-1)^d$, is a polynomial $g(X)$ of degree at most $r$ with $g(j)=g_j$ for $0\le j<T$. Its last $d$ entries vanish. The challenge-constant coefficient in $Y(j,\mathbf A)$ is $g_{j-d}$. On $d\le j<T$ this agrees with $g(j-d)$. Since $T-d>r$, that equality extends polynomially to all $X$. At $0\le j<d$ it now gives $g(-d)=\dots=g(-1)=0$. The $d$ leading and $d$ trailing roots are distinct under the bound on $q$.

Conversely, take any polynomial $g$ of degree at most $r$ with these $2d$ roots. Write $\prod_i(Z-A_i)=\sum_{k=0}^d c_k(\mathbf A)Z^k$ and set
$$
 Y(X,\mathbf A)=\sum_{k=0}^d c_k(\mathbf A)g(X-k).
$$
The endpoint roots make its time-indexed polynomial exactly the displayed product with $G(Z)=\sum_{j=0}^{T-1-d}g(j)Z^j$. It therefore passes all challenges, including tuples with repetitions. The top challenge monomial recovers $g$, and coefficient interpolation recovers the whole $Y$ from $H$. This identifies the kernel with the degree-$r$ multiples of the polynomial on those $2d$ simple roots and gives its dimension.

## A uniformly dense false trace

Set $T\ge4d+1$ and take the monic choice
$$
   g(X)=\prod_{h=1}^d (X+h)(X-T+h).
$$
The response above can equivalently be evaluated by composing $d$ operators $g(X)\mapsto g(X-1)-a_i g(X)$. For $a_i\ne1$ the degree stays the same. For $a_i=1$ it falls by exactly one, since the entering degree is positive and less than the characteristic. Thus for *every* challenge tuple the response is a nonzero univariate polynomial of degree at most $2d$. At least $T-2d$ replies differ from zero, enough to take the CPU's positive exit. For fixed $d$ the same constant-size field expression works at all scales with $T$ supplied as a parameter. The integer coefficients can also be computed by elementary products and convolution.

With one challenge the expression is particularly simple. Take $g(X)=(X+1)(X-T+1)$ and give the CPU the replies $g(j-1)-a g(j)$. The evaluated sum telescopes, with both endpoint terms zero. A checker requiring the same challenge-independent table would reject any nonzero reply row since a fixed polynomial of degree $T-1$ cannot vanish at every field element. The obstruction is to replacing that commitment by a low-degree *function of the challenge*. The argument gives no lower bound on SAT decision time or on interactive verification that binds the actual replies before drawing its random coins.

The finite audit constructs the matrix of all evaluation constraints independently of the convolution construction and computes its nullity by field elimination. It also checks all challenge tuples on concrete forged runs. Lean verifies the ordinary polynomial evaluation identity for repeated linear-factor convolution over the integers, which descends to prime fields. The optimality and density arguments above are manuscript proofs. [Exact audit](../audits/polynomially_consistent_reads_audit.py) · [Lean convolution certificate](../lean/ChallengePolynomialReads.lean)
