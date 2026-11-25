# A formal coefficient of the trace contraction survives bounded Boolean degree

Let $K=\mathbb F_{2^m}$ with $m\ge2$. Write $T(A,B,Z)=\sum_{i,j,k}A_{ik}B_{kj}Z_{ij}$ over $K$. Suppose a Boolean circuit computes $\operatorname{Tr}_{K/\mathbb F_2}T$ on all triples of $d$-square matrices. Arithmetize the bit circuit by XOR as addition, AND as multiplication and bit complement as addition of one. Before imposing any bit equations, assume each polynomial monomial of the output has degree at most $H$ in the input bits of **each** matrix block, with $1\le H\le m$. A syntactic degree bound suffices. A bound only on the squarefree representative does not give this hypothesis.

Replace each input bit of a field element $x$ by its usual coordinate polynomial $L_i(x)=\operatorname{Tr}(\beta_i x)=\sum_{j=0}^{m-1}(\beta_i x)^{2^j}$ in the dual basis, allowing a separate basis in each block. Call the resulting formal polynomial $P$. For every $H-1\le t<m$ its whole multihomogeneous component is

$$
 P_{(2^t,2^t,2^t)}=T^{2^t}.
$$

This gives a formal circuit for a specified Frobenius power of the contraction. At $H=1$ it recovers the contraction itself. At higher degrees, taking the indicated root while preserving a nearly quadratic circuit budget is a further requirement.

## The first possible wrap in a scalar weight

Let $W$ be a sum of $r$ powers from $1,2,\ldots,2^{m-1}$, repetitions allowed. If $W\equiv 2^t\pmod{2^m-1}$, $0\le t<m$, and $r\le t+1$, then $W=2^t$. Represent the summands as tokens in positions $0,\ldots,m-1$. Carry equal pairs to the next position cyclically. The number of tokens drops by one at each step. The final nonempty subset of positions with distinct tokens has ordinary value in $[1,2^m-1]$. Its residue forces it to be the singleton at $t$. If a carry ever wrapped from $m-1$ to $0$, follow the resulting token in the carry tree all the way to the root. At least $t$ subsequent carries are needed to reach position $t$. Including the wrap itself, at least $t+1$ carries and therefore $t+2$ starting tokens were needed. The example with two tokens at $m-1$ and one at each of $0,\ldots,t-1$ attains this threshold, with ordinary value $2^m+2^t-1$.

Every monomial of $P$ has total degree in each block equal to a sum of at most $H$ such tokens. On the scalar orbit $(\lambda A,\mu B,\nu Z)$ project to multiplicative character exponents $(2^t,2^t,2^t)$ by summing evaluations against $(\lambda\mu\nu)^{-2^t}$ over $(K^\times)^3$ and dividing by $(2^m-1)^3$. This is scalar Fourier projection in $K$. Its formal output selects the specified residue in each block. The carry lemma forces the ordinary degree in each selected block to be exactly $2^t$. On field-valued inputs correctness identifies the same projection with $T^{2^t}$ because the $m$ powers $2^j$ are distinct modulo $2^m-1$. Each individual variable in the two resulting polynomials has degree at most $2^t<|K|$. Agreement on the full field grid is therefore formal equality.

The size estimate does not require enumeration of the scalar orbit. Introduce one degree marker per block and truncate each marker above $N=2^{H-1}$. For every gate keep its coefficient table through $(N,N,N)$. Each AND needs at most $(N+1)^6$ field multiplications and additions for convolution. For each input entry the powers $x^{2^j}$ through $j=H-1$ can be shared across its $m$ bit coordinates. This gives the formal circuit for $T^N$ in $O((s+d^2m)(N+1)^6)$ operations when the bit circuit has size $s$. In particular the overhead is polylogarithmic in $d$ for $H=O(\log\log d)$. General closure of arithmetic circuits under taking factors in small characteristic has additional hypotheses in known results. This calculation does not give a size-preserving root circuit for this particular tensor. [Closure results for polynomial factorization](https://doi.org/10.4086/toc.2019.v015a013)

## Why the lowest coefficient can disappear on every extension

For a basis $\alpha_i$ of $K$ and its dual $\beta_i$, one has $\sum_i\alpha_i L_i(x)=x$ as a formal polynomial, by agreement on $K$ and the degree bound. A single Boolean layer replacing each bit by its AND with itself reconstructs formally as

$$
                    \sum_i\alpha_i L_i(x)^2=x^{2^m}.
$$

Indeed the coefficients of $x^{2^j}$ for $1\le j<m$ are the same zero coefficients as in the first identity. The remaining coefficient of $x^{2^m}$ is $\sum_i\alpha_i\beta_i^{2^m}=1$. Thus even changing the basis and checking homogeneity at every field scalar leave this formal representative undetected. For a trace-bit output, appending $h$ self-ANDs gives the formal power $P^{2^h}$. Every positive total-order Hasse coefficient below $2^h$ vanishes at every formal base point, at a cost of $h$ Boolean gates. A compiler is free to simplify these gates. The example isolates the limitation of extracting derivatives from an arbitrary correct bit representation.

In the [decision reduction](verifying-matrix-products-from-sat.md), a near-linear SAT algorithm also gives a near-linear-in-encoding RAM clock for the extension trace when $m\le d$, with a fixed irreducible modulus and dual-basis encoding of $Z$. Selecting one row and column costs $O(d^2m)$ bit gates, and the selected dot product takes $O(dm^2)$ bit gates by polynomial-basis schoolbook multiplication and reduction. The trace pairing of $Z$ with the proposed product takes $O(d^2m)$ gates in dual coordinates. Both SAT calls then fit $d^2m\operatorname{polylog}(dm)$ RAM work. The formal theorem assumes a bit circuit and its degree bound separately. The bounded-computation SAT encoding provides a verifier with execution witnesses. Neither the clock nor that verifier supplies the bounded-degree circuit the coefficient argument needs.
