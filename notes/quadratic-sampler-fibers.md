# Exact coding for short quadratic outputs with hidden selector bits

**Research journal, 24 November 2026.** I tested whether a nonlinear transformation with very large preimages could separate output probability from the cost of a deterministic program on one ordinary interpreter. For a quadratic transformation of a polynomial-size affine summary, the entire output distribution can be decoded within the clock allowed by the [unary coding test](unary-speed-gap.md). The affine stage may consume exponentially many independent bits. With additional hidden selectors that choose the quadratic map, a pointwise upper bound measures how widely their *conditional* distribution is spread. This leaves the unrestricted sampler case open.

## The model and bound

Let the dyadic clock be $t=2^q$, and let $V$ be a fixed efficiently literal universal prefix RAM. Write
$$
 C_t(y)=\min_{V(p)=y}\{|p|+\max(0,\lceil\log_2\max(2,\tau(p))\rceil-q)\}.
$$
At epoch $q$, a fixed uniform procedure specifies the following ordinary distribution on $\ell$-bit words, with $\ell\le q$.

* A deterministic straight-line circuit of affine Boolean gates maps independent fair bits to $r=\mathrm{poly}(q)$ summary bits. Its topologically ordered gate list, including the output locations, can be generated in $2^q\mathrm{poly}(q)$ time. The input nodes can be indexed from that list. The list is independent of the random bits.
* Independently, a uniform $k$-bit selector $Z$, with $k=\mathrm{poly}(q)$, chooses the readout. Given $q,z$, a fixed routine lists the $\ell$ quadratic polynomials in the summary coordinates in $\mathrm{poly}(q)$ time. Their values are the output $Y$. All polynomials use Boolean arithmetic over $\mathbb F_2$.

The gates, their coefficients, and the dimensions are computed uniformly. The distribution also defines a sampler by reading an epoch header and then the prescribed fair bits. Conditioning on the epoch removes the shared header cost of $O(\log(q+2))$; its simulation takes $2^q\mathrm{poly}(q)$ time. If an already given sampler has the same timely output distribution, only the distributional representation and its construction time are needed below.

Fix an output $y$ of mass $\mu(y)>0$. For $0\le h\le k$, let $I$ be any selector prefix of length $k-h$ having positive posterior mass $\pi_I=\Pr[Z\text{ begins with }I\mid Y=y]$. Then
$$
 C_t(y)+\log_2\mu(y)\ \le\
 -\log_2\pi_I + \max(0,\ell+h-q)+O(\log(q+2)).
 \tag{1}
$$
The constant is uniform in the epoch, output, and prefix for the fixed family and interpreter. Taking $h=k$ gives an excess cost at most $\max(0,\ell+k-q)+O(\log(q+2))$. In particular, the coding bound required under linear SAT already holds unconditionally whenever $\ell+k\le q+O(\log(q+2))$.

There is also a necessary condition at a particular difficult output regardless of $k$. Take $h=\min(k,q-\ell)$. If its excess cost is $G=C_t(y)+\log_2\mu(y)$, each prefix of length $k-h$ has posterior probability at most $2^{-G}\mathrm{poly}(q+2)$. This holds after each fixed uniformly polynomial-time invertible permutation of the selector space. Thus a construction attaining superlogarithmic $G$ must spread its successful tapes across superpolynomially many of these selector blocks. The remaining challenge is to prove actual program-cost hardness for such an output.

## Computing the distribution and the name

First compute the affine support of the summary as $b+Eu$, where $u$ is uniform in $\mathbb F_2^d$ and $d\le r$. A forward evaluation at zero gives $b$. For the linear part attach an $r$-bit mask to each gate. Initialize masks to zero, toggling coordinate $i$ at the $i$-th output gate. In reverse topological order XOR each destination's mask into the masks of its source gates with coefficient one. By linearity each input node's final mask gives its column in the linear map to the summary. Gaussian elimination on the stream of columns gives an independent basis $E$ in time polynomial in $r$ per column. All preimages under a linear map have the same size, so $u$ is uniform. The entire preprocessing fits $2^q\mathrm{poly}(q)$, even with $2^q$ random-input locations. Running the whole circuit separately for each input location could exceed this clock.

For a particular selector $z$, substitute $b+Eu$ into the quadratics, reducing squares using $u_i^2=u_i$. For a mask $a\in\mathbb F_2^\ell$, write $Q(u)=a\cdot Y(z,u)$. Compute its signed sum over all $u$. If there is a cross term $u_i u_j$, write $Q=u_i u_j+u_i A+u_j B+R$, with $A,B$ affine in the remaining variables. Summation over the pair gives $2(-1)^{AB+R}$ at each setting of the other coordinates. The reduced phase is still quadratic. Once all cross terms are gone, the sum for the remaining affine phase is zero if any linear coefficient survives, and otherwise equals the constant sign times the number of remaining assignments. Each mask costs $\mathrm{poly}(q)$. This degree-two signed-sum algorithm is classical. [Montanaro, Quantum circuits and low-degree polynomials over $\mathbb F_2$](https://arxiv.org/abs/1607.08473)

Enumerate the $2^h$ selectors in prefix $I$, and add their signed sums at each of the $2^\ell$ masks. The Walsh transform of the resulting array, divided by $2^\ell$, gives the exact integer multiplicity of every $y'$ over all pairs $(z,u)$ in the block. Indeed, the sum over masks of $(-1)^{a\cdot(Y+y')}$ is $2^\ell$ when $Y=y'$ and zero otherwise. The integer butterfly transform needs $O((\ell+1)2^\ell)$ operations, on integers with $O(d+h+\ell+1)$ bits. The complete table and its sort require at most $2^{\ell+h}\mathrm{poly}(q)$ time in addition to affine preprocessing. Rank outputs by descending multiplicity with lexicographic ties.

A decoder reads self-delimited $q,h$ and a rank length, the $k-h$ bits of $I$, and the rank payload. Conditional on this selector block, the mass of $y$ is
$$
 \Pr[Y=y\mid Z\text{ begins with }I]=2^{k-h}\mu(y)\pi_I.
$$
Its one-based rank is at most the reciprocal of that quantity. Encoding rank minus one with the chosen length costs at most its conditional surprisal rounded up. With the prefix bits included, the name uses at most $-\log_2\mu(y)-\log_2\pi_I+O(\log(q+2))$ bits. The rank length is at most $\ell$, so each integer header fits the stated overhead. The clock is $(2^q+2^{\ell+h})\mathrm{poly}(q)$, including fixed interpreter simulation since $\ell+h=\mathrm{poly}(q)$. Subtracting the allowed exponent $q$ proves (1). The single-epoch construction suffices because the unary test allows $O(\log q)$ extra bits.

## Attempted extension to cubic phases

An exact signed-sum subroutine with polynomial dependence on the number of coordinates for arbitrary cubic phases would compute the number of satisfying assignments of an arbitrary Boolean circuit in polynomial time. For an input $x$ and proposed gate values $v$, express correct fan-in-two AND, XOR and NOT gates by equations $R_i(x,v)=0$ of degree at most two. Include the equation for an accepting output. Introduce one fresh fair bit $\lambda_i$ per equation and let $f=\sum_i\lambda_iR_i$. Summing $(-1)^f$ over $\lambda$ gives $2^{\#\mathrm{equations}}$ exactly on consistent accepting pairs and zero elsewhere. Each accepting input has a unique consistent gate-value vector. Thus the signed sum of this one cubic polynomial, divided by the same power of two, is the exact count. This known hardness applies to the polynomial-time inner routine. The near-clock coding inequality allows approximate probabilities and other decoders. [Montanaro, Quantum circuits and low-degree polynomials over finite fields](https://arxiv.org/abs/1607.08473)

Lean 4.19 checks the elimination of an interacting pair and the full Boolean character orthogonality identity. A finite program compared the resulting exact Walsh histograms against exhaustive enumeration on 432 quadratic maps with zero through eight free coordinates and zero through five output bits. The clock and description-length estimates above are proved on paper. [Lean checks](../lean/QuadraticFibers.lean) · [Reproducible histogram test](../audits/quadratic_fiber_experiment.py)
