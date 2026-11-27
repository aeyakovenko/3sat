# Preserving average accuracy using moments of a public tape

Fix a table $g$ on a finite uniformly sampled query domain. A fixed deterministic evaluator, with fixed advice, may query an independent public random tape adaptively. Each new invocation starts in its prescribed state and makes at most $p$ bit probes; the same tape is reused across invocations. Write $X$ for the fraction of table positions on which its answer agrees with $g$. If a fraction $\beta>0$ of full tapes yield accuracy $X\ge b$ and $0<a<b\le1$, a bounded-independence replacement has a seed with $X>a$ provided
$$
 \beta\big(1+T_d(2b/a-1)\big)>2
$$
and the replacement matches every set of at most $pd$ distinct raw tape positions. Here $T_d$ is the degree-$d$ Chebyshev polynomial of the first kind. In particular, for $a=1/2+\epsilon$, $b=1/2+2\epsilon$ and $0<\epsilon\le1/4$, one may take $d=O(\log(2/\beta)/\sqrt\epsilon)$. These logarithms count samples in a proof of existence. The evaluator need never compute the target table, an accuracy statistic, or a Chebyshev polynomial.

## Matching the moments

Draw $j$ independent query inputs on the same tape. For each fixed tuple, the conjunction that all answers match their fixed target bits is a decision tree of depth at most $pj$. Its transcript distribution is preserved by matching the uniform replies on all distinct positions in any path. A repeated probe must get the same reply. Conditioning first on the tape instead, the chance of joint success is $X^j$. Averaging gives equality of all moments through $d$, including the constant moment. For a tape with $W$ addressable bit positions, choose a binary extension field with at least $W$ distinct elements, pick independent uniform coefficients for a polynomial of degree $<pd$, evaluate at the address, and take a fixed nonzero binary linear functional of the result. Interpolation at distinct addresses gives the required independence. When $pd=0$ the constant moment or tape-independent evaluation needs no sampled replies. If the program reads packed words, charge the raw bit positions or instead use independent field words with the appropriate distribution. A target depending on the same sampled tape would require a different justification. [Adaptive transcript lemma](../lean/SampledProofOracle.lean)

For comparison, on $t$ independent inputs, test whether the sample agreement fraction is at least $1/2+3\epsilon/2$. The joint acceptance probability is at least $\beta(1-\delta)$ on full tapes, for $\delta=\exp(-t\epsilon^2/2)$, by Hoeffding's inequality on each good tape. If every replacement tape had accuracy at most $1/2+\epsilon$, the transferred test would accept with probability at most $\delta$. Thus $t>2\log((1+\beta)/\beta)/\epsilon^2$ suffices. Signed combinations of the same moments give the stronger bound above. [Hoeffding, Probability inequalities for sums of bounded random variables](https://doi.org/10.1080/01621459.1963.10500830)

## Sharp bound for arbitrary real accuracy distributions

Suppose two probability laws on $[0,1]$ have the same moments through $d$, and the second is supported on $[0,a]$. The largest possible first-law probability of $[b,1]$ equals
$$
 \beta_* = \frac{2}{1+T_d(2b/a-1)}.
$$
Indeed $F(x)=(1+T_d(2x/a-1))/2$ is nonnegative on $[0,1]$, bounded by one on $[0,a]$, and at least $F(b)$ on $[b,1]$. This follows from $T_d(\cos\theta)=\cos(d\theta)$ and $T_d(\cosh u)=\cosh(du)$ for $u\ge0$. Equal expected values of $F$ give the upper bound. For $d\ge1$ the strict transfer inequality is equivalent to $d>\operatorname{arcosh}(2/\beta-1)/\operatorname{arcosh}(2b/a-1)$. The denominator is $\Theta(\sqrt\epsilon)$ for the displayed accuracy thresholds. When $\beta=1$ a single moment suffices. When $d=0$ the sharp bound is one and no positive-accuracy transfer follows from normalization alone. If $a=0$, a matching first moment already forces both laws to be supported at zero.

For equality when $d\ge1$, take the Chebyshev extrema $x_i=a(1-\cos(i\pi/d))/2$ for $0\le i\le d$ and let $\lambda_i$ be their Lagrange weights at $b$. They sum to one and have sign $(-1)^{d-i}$. The polynomial $T_d(2x/a-1)$ takes those same signs at the extrema, hence interpolation gives $\sum_i|\lambda_i|=T_d(2b/a-1)$. Write $U=\sum_{\lambda_i>0}\lambda_i=(1+T_d(2b/a-1))/2$. Take the two distributions
$$
 \mu=\frac{\delta_b+\sum_{\lambda_i<0}(-\lambda_i)\delta_{x_i}}{U},
 \qquad
 \nu=\frac{\sum_{\lambda_i>0}\lambda_i\delta_{x_i}}{U}.
$$
Their moments match by interpolation, $\nu$ is supported on $[0,a]$, and $\mu([b,1])=1/U$. Mixing both laws with the same point mass at zero realizes any smaller high mass. This sharpness concerns arguments that use only matched moments and bounded support. Extremal polynomial growth and the use of moment matching in statistical lower bounds are classical. Priority of this adaptation to public-tape accuracy is unverified. [Bos, Ma'u and Waldron](https://www.math.auckland.ac.nz/~waldron/Preprints/Extremal-growth/BosMauWaldron1.pdf) · [Wu and Yang](https://arxiv.org/abs/1504.01227)

## Exact answer on the grid of possible success counts

With $M$ query positions, work in success counts $0,\ldots,M$. Fix integers $0\le A<B\le M$ as the low ceiling and high floor. For $0\le d\le A$ put
$$
 \Lambda=\min_{0\le x_0<\cdots<x_d\le A}\sum_{i=0}^d
 \left|\prod_{j\ne i}\frac{B-x_j}{x_i-x_j}\right|.
$$
The largest possible high mass, among grid-valued first laws whose first $d$ moments match a law supported on $0,\dots,A$, is exactly $2/(1+\Lambda)$.

To see this, maximize $q(B)$ subject to $\deg q\le d$ and $|q(x)|\le1$ at the low grid points. The dual minimizes the sum of absolute weights in a signed representation of evaluation at $B$ on those points, exact on degrees $0,\dots,d$. These finite linear programs are feasible and have equal attained optima. Splitting weights into positive and negative variables, an optimal basic solution uses at most $d+1$ nonzero entries. It cannot use fewer: a polynomial of degree at most $d$ vanishing at all those points and nonzero at $B$ would violate the representation. Thus it uses exactly $d+1$ nodes, with the Lagrange weights, and the optimum is $\Lambda$. At any such optimal nodes the primal optimizer takes the signs of those weights, by equality in $q(B)\le\sum_i|\lambda_i|$. For $x>x_d$ the signs of all cardinal interpolation polynomials agree with their signs at $B$ and their absolute values increase with $x$ (are constant when $d=0$). Hence $q(x)$ there equals their sum of absolute values, is at least one, and is nondecreasing. Applying $(1+q)/2$ and the two explicit distributions proves the grid formula. The nodes and weights here are rational and both laws can be expressed by finite pools with multiplicity. If $d>A$, the polynomial $\prod_{i=0}^A(x-i)$ vanishes on the low grid and is strictly positive on all the other grid points. Matching its expectation rules out any positive high mass.

The grid formula supplies a sharp obstruction to an argument using only the moments, even when the accuracies are rational. It does not require that every pair attaining equality actually arise from a given adaptive evaluator on uniform bits and polynomial seeds. Additional access structure could allow a smaller degree. [Exact finite exercises and adaptive tape experiment](../audits/public-tape-semantic-audit.py) · [Finite algebraic transfer in Lean](../lean/SemanticSampling.lean)
