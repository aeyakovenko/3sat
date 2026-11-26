# Some direct executions of matrix-product parity must read every input bit

Let $g(A,B,Z)=\langle AB,Z\rangle$ over $\mathbb F_2$ for three binary $d$-square matrices, and let $D=d^2$. Every deterministic algorithm for this scalar bit has inputs of **each verdict** on which it reads all $3D$ source bits. There are at least $2^{9D/4-O(d)}$ such triples of each verdict for every algorithm. This applies to a word RAM counting all original bits covered by a raw word load. It gives a read bound of $\lceil3D/w\rceil$ for words of $w$ bits. The earlier result gives typical minimum certificate size $(5/2-o(1))D$ and does not imply this worst-case claim. A deterministic reader can always inspect all $3D$ bits. [Typical certificates](coordinate-certificates-for-matrix-product-parity.md) · [Network motivation over odd characteristic](parity-and-forbidden-entries-in-the-binary-product-graph.md)

The underlying integer character sum is strictly positive for every side. Consequently the multilinear degree of $g$ as a Boolean function is exactly $3D$ in characteristic zero. It is also exactly $3D$ at infinitely many sides over **each** fixed odd-characteristic field. One cannot assert this simultaneously in all odd fields at each side. For example the full coefficient vanishes modulo 29 at side three. A second character sum gives degree at least $3D-3d+2$ uniformly over all fields of characteristic different from two at every $d\ge2$. In characteristic two the degree is three. These degree statements measure weighted coordinate-query computations directly on the factors and mask. Internal contraction in an unrestricted tensor network can sum many assignments without reading the external bits along a single query branch. [Decision trees and polynomial degree](https://doi.org/10.1145/129712.129757)

## The full Fourier coefficient

Write $u$ for the length-$d$ all-ones vector, $J=uu^\mathsf T$, $|A|$ for Hamming weight and $e=d\bmod2$. Define the **unnormalized** integer sum
$$
 H_d=\sum_{A,B,Z}(-1)^{g(A,B,Z)+|A|+|B|+|Z|}.
$$
Summing first over $Z$ gives $2^D\sum_{AB=J}(-1)^{|A|+|B|}$. Fix $A$ of rank $r$ with image $W$ and kernel $K$. The condition $AB=J$ requires $u\in W$. Each column of $B$ is a preimage of $u$. Their signs cancel unless $K\subseteq u^\perp$. Write $T:\mathbb F_2^d/K\to W$ for the isomorphism induced by $A$, $\bar u$ for the class of $u$ in the quotient, and $\lambda,\bar\lambda$ for the all-ones functional restricted to $W$ and descended to the quotient. If the two conditions hold, the contribution summed over $B$ is
$$
  2^{d(d-r)}(-1)^{\lambda(T\bar u)+e\bar\lambda(T^{-1}u)}.
$$
There are $c={d-1\brack r-1}_2$ choices each of $W$ and $K$, where the bracket counts subspaces. Put $G_r=|\mathrm{GL}_r(2)|$.

**Odd side.** Both paired evaluations $\lambda(u)$ and $\bar\lambda(\bar u)$ are one. In bases adapted to each vector and its dual functional the exponent is $T_{11}+(T^{-1})_{11}$. For uniform $T$, the pair $(v,f)=(Te_1,e_1^\mathsf T T^{-1})$ is uniform on $v\ne0,\ f(v)=1$: changes of basis act transitively. If $v=e_1$ the sign is positive. For each other $v$, the value of $f(e_1)$ is balanced subject to $f(v)=1$. The resulting sum over $T$ is $G_r/(2^r-1)$. In particular,
$$
 H_d=2^D\sum_{r=1}^d 2^{d(d-r)}c^2\,G_r/(2^r-1)>0.
$$

**Even side.** The inverse term disappears. Write $c_0={d-2\brack r-1}_2$, taking a bracket outside its range to be zero. This counts $W$ contained in $u^\perp$ as well as $K$ containing $u$, under the two previous conditions. If either holds, the direct term is identically zero and the sign is positive. Otherwise a random isomorphism sends the specified nonzero vector to a uniform nonzero vector. The average sign of the nonzero functional there is $-1/(2^r-1)$. Thus the rank-$r$ summand of $H_d/2^D$ is
$$
 2^{d(d-r)}\,c^2\frac{G_r}{2^r-1}
        \left(2^r(2a-a^2)-1\right),\qquad
 a=c_0/c=\frac{2^{d-r}-1}{2^{d-1}-1}.
$$
For $r<d$ it is positive, since $2^ra>1$ and $2a-a^2\ge a$. The last term is $-2^{d-1}G_{d-1}$. The preceding term alone outweighs it. With $L=2^{d-1}-1$ that preceding term is $2^dG_{d-1}(L^2+L-1)/L$. This includes $d=2$.

For growing $d$, $H_d=2^{9D/4+O(d)}$. Indeed $\log_2 {d-1\brack r-1}_2=(r-1)(d-r)+O(1)$ and $\log_2 G_r=r^2+O(1)$ uniformly, by the product formulas and $\prod_{i\ge1}(1-2^{-i})>0$. The log of the common factor including $2^D$ is $2D+r(d-r)+O(d)$. The extra even-side factor has absolute value at most $2^d$ and is bounded below by a positive constant at $r=\lfloor d/2\rfloor$ for all sufficiently large $d$. In the even case group the last two ranks first to remove the only negative term. The middle summand gives the lower estimate, and summing the upper estimates gives the other direction.

On either verdict, the signed sum of $(-1)^{|A|+|B|+|Z|}$ has absolute value $H_d/2$, because the signed sums over the two verdicts add to zero. A deterministic execution that misses even one original bit belongs to a transcript subcube whose sign sum is zero by flipping that bit. A fully exposed transcript contributes one in absolute value. The conclusion counts actual input triples separately on each verdict and charges each word load only once. This proof applies to the scalar computation; the journal’s RAM reduction to the scalar is a separate algorithm, so these are not automatically reads made inside any one SAT call. [Lean subcube cancellation and full-read bound](FullReadWalshMass.lean) · [Reduction involving the scalar computation](verifying-matrix-products-from-sat.md)

For any odd prime $p$, take $d$ odd and $d\equiv1\bmod \operatorname{ord}_p(2)$. In the odd-side formula all $r>\operatorname{ord}_p(2)$ terms vanish modulo $p$, since $G_r/(2^r-1)=2^{r(r-1)/2}\prod_{i=1}^{r-1}(2^i-1)$. For $2\le r\le\operatorname{ord}_p(2)$ the Gaussian bracket has a numerator factor $2^{d-1}-1$ divisible by $p$ and no denominator factor divisible by $p$. The $r=1$ term survives. For $d=1$ the same conclusion follows directly. Over a field of characteristic different from two the characters form a basis, and substitution of $(-1)^x=1-2x$ preserves total multilinear degree. The nonzero full coefficient of the sign gives full degree for the scalar bit. Over $\mathbb Q$ the full-degree result follows from positivity. Conversely the integer value at $d=3$ is $118784=2^{12}\cdot29$, so degree $27$ fails in characteristic 29.

## A dense frequency whose coefficient is always a power of two

There is also a uniform result with no divisibility exceptions. For $d\ge2$ take frequency matrices $U,J,V$ on $A,B,Z$ respectively. For $i<d$ take column $i$ of $U$ to be $u+e_i$, using one-based indices, and take the last column to be their binary sum. The first $d-1$ columns are independent, since their last coordinate detects the parity of a sum. Their span is a hyperplane $S$ with normal $n=(1,\ldots,1,e)$, and the sum of all columns is zero. Put $V=J+I$ for even $d$ and $V=J+I+E_{dd}$ for odd $d$. In both cases $V$ is invertible and $Vu\ne n$. For even $d$, $(I+J)^2=I$. For odd $d$, a vector in the kernel has its first $d-1$ entries equal to its own parity. The last row requires that parity to vanish, which forces its last entry to vanish as well. The combined frequency has weight $3D-3d+2$ for even $d$ and $3D-2d+1$ for odd $d$.

Hold $Z$ fixed. Summing the $k$th column of $A$ with the $k$th row of $B$ gives zero unless $Zb=U_{*k}$ is solvable and $u\in\mathrm{im}(Z^\mathsf T)$. If it is nonzero, this sum has absolute value $2^{2d-\operatorname{rank}Z}$ and sign $(-1)^{u^\mathsf T b}$. Over all $k$ these signs multiply to one, since the columns of $U$ sum to zero and $u$ annihilates $\ker Z$. Thus only two strata of $Z$ remain. In units of $2^D$ their contributions are the character sum on invertibles and $2^d$ times the character sum on $\mathrm{im}Z=S,\ \ker Z=\langle x\rangle,\ 0\ne x\in u^\perp$.

Write $K_m(t)$ for the additive-character sum on $\mathrm{GL}_m(2)$ at a frequency of rank $t$, and $k_m=(-1)^m2^{m(m-1)/2}$. The classical general-linear-group Gauss sum gives $K_m(m)=k_m$ and $K_m(m-1)=-k_m$. At each fixed kernel line the isomorphisms are from $\mathbb F_2^d/\langle x\rangle$ to $S$. The rank of the induced frequency is the rank of $V^\mathsf T:S\to\mathbb F_2^d$ followed by quotienting by $x$. It equals $m=d-1$ except when $x\in V^\mathsf T S$, when it equals $m-1$. Since $V u\ne n$, the hyperplanes $u^\perp$ and $V^\mathsf T S$ differ. Among nonzero $x\in u^\perp$ there is exactly one more outside than inside $V^\mathsf T S$. Consequently the unnormalized Walsh coefficient at $(U,J,V)$ is
$$
             2^D(k_d+2^d k_{d-1})
            =(-1)^{d-1}2^{D+d(d-1)/2}.
$$
It survives over every field in which two is invertible, proving the claimed near-full degree. Increasing the side by one multiplies this signed integer by $-2^{3d+1}$. The successor preserves an obstruction to avoiding the input reads. It does not force more arithmetic after the inputs have been read. [Li and Hu, Theorem 2.1](https://arxiv.org/abs/1105.4513)

The audit sums over all triples at sides one and two. It independently sums over the last matrix and its binary-vector fibers at sides through four, without using any rank-stratum formula, and checks the modular progression in ten fields. This is a direct-factor query result. Its upper limit is the input length; proving the SAT time milestones requires controlling the amount of computation as well. [Exact integer audit](direct_scalar_walsh_audit.py)
