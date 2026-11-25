# The price of a rank-dependent answer on unpromised matrices

Let $E$ be an arbitrary binary $d\times d$ matrix. A query returns $Ex$ or $E^{\mathsf T}x$ for any chosen binary vector. Count the maximum number of queries per transcript in a finite linear combination of transcript indicators over a field $F$ of characteristic two. Queries can be adaptive, and the input and output bases are unrestricted.

**Theorem.** Let $f:\{0,\ldots,d\}\to F$ be nonconstant, and let $h$ be the first index with $f(h)\ne f(h+1)$. The exact query cost of the total function $E\mapsto f(\operatorname{rank}E)$ is $d-h$. Right queries alone attain it. A constant function costs zero.

**Lower bound.** Put $m=d-h>0$. Restrict $E$ to the block diagonal matrix with blocks $I_h$ and a completely free $m\times m$ matrix $B$. A vector query in either direction can be simulated by a single query to $B$, adjoining the known answer on the identity block. Integrate a transcript by summing its value over all $B$. Independent left and right queries of ranks $a,b$ fix $a$ rows and $b$ columns after suitable, separate basis changes. Every consistent transcript therefore has $2^{(m-a)(m-b)}$ completions. If it has fewer than $m$ queries, the exponent is positive. Its sum vanishes in $F$, even if the directions were selected adaptively, since each transcript fixes the answers that led to them.

By contrast, one binary matrix has rank zero and $(2^m-1)^2$ have rank one. At rank $j\ge2$, fixing kernel and image leaves $|\mathrm{GL}_j(2)|$ isomorphisms, an even number. Consequently the integral of the target over this entire block restriction is $f(h)+f(h+1)\ne0$. This proves the lower bound for any finite linear combination.

**Upper bound.** For $0\le j\le d-1$ the indicator $[\operatorname{rank}E\le j]$ can be computed by adding one zero-answer transcript for each $(d-j)$-dimensional subspace of the input space, using a single fixed basis for each subspace. The count is zero if the kernel is too small and is odd otherwise. Indeed the number of $k$-subspaces of an $s$-space for $k\le s$ is the quotient of the odd integers $\prod_{i=0}^{k-1}(2^{s-i}-1)$ and $\prod_{i=0}^{k-1}(2^{k-i}-1)$ after cancelling powers of two in the ordered basis counts. This gives the indicator in $F$ using $d-j$ right queries. The identity
$$
f(r)=f(d)+\sum_{j=h}^{d-1}\bigl(f(j)-f(j+1)\bigr)[r\le j]
$$
now attains $d-h$.

## Consequence for promises

Suppose the allowed ranks are zero and a nonempty set $S$ of positive ranks, and the required answer is $[E=0]$. Among all representations whose output on **every** matrix depends only on rank, the optimal cost is $d-\min S+1$. Some adjacent change must occur before $\min S$, and the threshold $[r<\min S]$ attains the bound. For $S=\{1,\ldots,K\}$ with $1\le K<d/2$, allowing the answer to depend on more than rank outside the promise drops the optimum from $d$ to exactly $2K$. Hence every optimal signed representation must take different values on two unpromised matrices of the same rank. The characteristic-zero Freivalds polynomial has a rank-dependent answer even outside its promise. Averaging over all changes of basis in characteristic two can destroy precisely the distinction that gives the savings. [Exact signed-query bounds in each characteristic](residual-lines-and-the-ranks-needed-for-matrix-verification.md)

There is also an induction with a genuine increase at every step in this query model. Replacing $(d,K)$ by $(d+2,K+1)$ raises the exact cost $2K$ to $2K+2$ whenever $d\ge2K$. The coordinate proof tensors its lower-bound witness with one more $2\times2$ block. The characteristic-two vector proof counts completions of arbitrary mixed-direction queries, including top-level queries that combine the new coordinates with all the old ones. A lower bound at dimension $d$ on any fixed allowed rank set also holds in every larger dimension by adjoining zero rows and columns. Applying this induction to a RAM reading the physical factors $A,B,C$ would require a simulation preserving the deadline. Such a simulation remains missing.

The finite sparse-rank census can average over a subgroup of odd order without losing representations. It tests which symmetry is available when some ranks are absent. [Exact small census](sparse-rank-promises-in-characteristic-two.md)

## Odd characteristic can also force symmetry breaking

Let $F$ have odd characteristic $p$. Distinguishing the zero $d\times d$ binary matrix from an invertible one needs exactly **one** ordinary deterministic right query for every $d\ge1$. Test a fixed nonzero $x$. The test's value on singular nonzero matrices can depend on their kernels.

If the signed representation must give a rank-dependent answer on every input, the exact cost is
$$
 c_p(d)=
 \begin{cases}
  1,& e\nmid d,\\
  e\,p^{v_p(d/e)},& e\mid d,
 \end{cases}
 \qquad e=\operatorname{ord}_p(2).
$$
In particular, for $p=3$ the dimensions $d=2,6,18,54,\ldots$ give cost **exactly $d$** for every rank-dependent completion, while a single fixed query continues to solve the promise. Multiplying the dimension by three on this sequence triples the first optimum and preserves the second.

To prove the formula, take any total rank-dependent function expressible by $q$ signed queries. Its Walsh coefficients are constant on rank orbits because the function itself is invariant. This uses no division by the order of the change-of-basis group. Its Fourier support consists of masks of rank at most $q$, as proved for individual transcripts. The space of such rank-dependent functions has dimension at most $q+1$ since 2 is invertible and the Walsh transform is an isomorphism. In this space the $q+1$ functions $g(d-r,j)$ for $j=0,\ldots,q$ are independent, where $r$ is the input rank and $g(s,j)$ counts $j$-subspaces of a binary $s$-space. Evaluate at $d-r=0,\ldots,q$ to get a unit lower triangular matrix. The functions are computed by $j$ subspace basis queries and hence span the entire space. This also gives a finite linear system for the exact cost of a rank-dependent completion on any specified rank promise in odd characteristic.

At the two endpoints $r=d,0$, column $j=0$ agrees, and the two values of every $j>0$ column are $0$ and $g(d,j)$. Thus the desired optimum is the least positive $j$ with $g(d,j)\not\equiv0\pmod p$. A single such column, rescaled, gives the upper bound. If $e\nmid d$, $g(d,1)=2^d-1$ is nonzero. Otherwise write $d=em$. The Gaussian binomial product identity reads
$$
 \prod_{i=0}^{d-1}(1+2^i z)
   =\sum_{j=0}^d 2^{j(j-1)/2}g(d,j)z^j.
$$
For example this follows by induction from $g(n+1,j)=g(n,j)+2^{n+1-j}g(n,j-1)$, counting subspaces inside or outside a fixed hyperplane. In $F[z]$, one period of $e$ factors equals $1-(-z)^e$ since the powers of 2 are precisely the $e$th roots of unity. If $m=p^a b$ with $p\nmid b$, the full product is $(1-(-z)^{e p^a})^b$. Its least positive nonzero degree is $e p^a$. The powers of 2 on the right are units. This proves the formula and the multiplicative induction. In characteristic zero $g(d,1)$ never vanishes and the endpoint promise already has a rank-dependent one-query completion.

The restriction on the answer outside a promise is therefore quantitatively important in either characteristic. On this sequence the increasing lower bound comes entirely from how a test is required to behave on unpromised inputs. The fixed-vector deterministic test continues to meet its original deadline at every dimension.

[Lean check of the characteristic-two count parities, transcript integrals and threshold expansion](RankThresholdParity.lean) · [Finite characteristic and Gaussian-column audit](radial_rank_completion_audit.py)
