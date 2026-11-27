# An entrywise agreement tradeoff for binary matrix products

A predictor sees independent uniform $d\times d$ binary matrices $A,B$. It computes a bilinear output $H(A,B)$ and may add an arbitrary output depending on $A$ alone and another depending on $B$ alone. Suppose the coefficient tensor of $H$ has geometric border rank $s$. This includes algorithms with $s$ shared products of left and right linear forms and arbitrary linear output combinations. For a uniformly chosen entry let $\beta$ be twice the success probability minus one. Assuming the November 2026 **rectangular** matrix multiplication exponent formula, for $s=d^{\sigma+o(1)}$, $1\le\sigma\le9/4$,
$$
             |\beta|\ \le\ d^{4\sqrt{\sigma}-6+o(1)}.
$$
The exponent is attained by computing a balanced block of entries. At $s=d^{2+o(1)}$ it is $4\sqrt2-6=-0.34314575\ldots$. Here $s$ charges one shared computation for all requested entries. If the entry is supplied before the computation, a dot product costs just $d$ products. [Rectangular exponent statement and scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/107.md)

## A lower bound for any space of requested outputs

For a $q$-dimensional subspace of binary output masks $W$, consider the trilinear form $\langle AB,Z\rangle$ restricted to $Z\in W$. For $d\ge2$ and $1\le q\le d^2$ its geometric border rank is at least
$$
                d^{(1+\frac14\log_d q)^2}.
$$
Extend scalars to the algebraic closure. A diagonal change of row and column bases with distinct entry weights, followed by a limit, replaces $W$ by a coordinate subspace. To see this take a basis in echelon form ordered by the weights and scale each pivot to one. Each row or column change is accompanied by an inverse change in an unrestricted matrix factor preserving the trilinear form. Adjacent row shears move selected coordinates upward whenever their upper neighbor is absent. A pair with both coordinates present spans the same two-dimensional space after a shear. For a lone lower coordinate, normalize and take the limit. Similarly move selected coordinates left. The sum of row and column indices decreases on every nontrivial move, giving a Ferrers diagram of $q$ positions. The restricted tensor has degenerated at every step, so its border rank can only decrease.

For row lengths $\lambda_i$ in this diagram, $q\le(\sum_{i=1}^d1/i)\max_i i\lambda_i$. A rectangle of dimensions $u,v$ and area at least $q/H_d$ consequently survives. Its tensor is rectangular multiplication $\langle u,d,v\rangle$. Tensor with its transposed, relabeled copy to obtain $\langle uv,d^2,uv\rangle$. For $x=\log_d(uv)$ the exact exponent formula at dimensions $(2,x,x)$ is $2+x+x^2/8$. A fixed geometric border rank gives an upper bound on the arithmetic exponent by tensor powering and interpolation over the algebraic closure. Hence the original rank is at least $d^{(1+x/4)^2}$, including $x=0$ by the dot-product flattening. To remove the harmonic factor apply the argument to the $j$th tensor power of the original restriction. It is a $q^j$-dimensional mask space at dimension $d^j$, with rank at most the $j$th power of the given border rank. Since $\log H_{d^j}=o(j)$, taking $j$th roots and the limit proves the displayed bound. This use of the rectangular exponent is an external mathematical dependency. [Pinned exponent documentation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/107.md) · [Ferrers compression and related work](average-case-rank-of-binary-matrix-products.md)

## Correcting q masks

For a fixed mask $Z$, let $r_Z$ be the ordinary matrix rank over $\mathbb F_2$ of the bilinear error $\langle AB-H,Z\rangle$ as a scalar function of the two inputs. If $q$ independent masks have $r_Z\le k$, correct each one with at most $k$ rank-one products. Take these masks as a basis of their span. The resulting exact restricted tensor has border rank at most $s+kq$, hence
$$
          s+kq\ \ge\ d^{(1+\frac14\log_d q)^2}.
$$
This corrects only the bilinear part. Separate-input offsets were allowed in the predictor. For a rank-$r$ bilinear form the sign matrix has normalized operator norm $2^{-r/2}$, by orthogonality of the row characters on the quotient. Its correlation even against arbitrary separate-input signs is at most $2^{-r/2}$. Without the offsets its bias equals $2^{-r}$.

At least $|\beta|d^2/2$ independent coordinate masks have absolute correlation at least $|\beta|/2$. Their ranks are at most $2\log_2(2/|\beta|)$. We may assume $|\beta|\ge d^{-2}$ since the stated result otherwise follows directly. Put $y=\log_d q$ for this family. The correction term is $d^{y+o(1)}$ and $(1+y/4)^2-y=(1-y/4)^2\ge1/4$ for $0\le y\le2$. The preceding inequality gives $y\le4(\sqrt\sigma-1)+o(1)$ and proves the upper bound.

For equality in the exponent put $t=2(\sqrt\sigma-1)$. Compute a $d^t$-by-$d^t$ block of the output with rectangular multiplication and set all other predictions to zero. The claimed all-field upper exponent gives rank $d^{(1+t/2)^2+o(1)}$ over $\mathbb F_2$, by bilinearizing the arithmetic computation. Round the block size down, using one dot product at $t=0$. Exact entries have correlation one and the other dot products have nonnegative bias. This gives $\beta\ge d^{2t-2+o(1)}$.

Earlier work gives randomized reductions from approximate product oracles for various success conditions. The argument here concerns vanishing advantage for a shared bilinear predictor. I have not established priority for this tradeoff. A fast SAT solver supplies a scalar verdict for a furnished mask. Extracting a shared bilinear predictor with the indicated bias from that RAM computation is open. [Gola, Shinkar and Singh](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2024.34) · [SAT to product verification](verifying-matrix-products-from-sat.md)

## Even selecting a predictor after seeing the inputs

Suppose $s=o(d^{9/4})$ and fix $0<\delta<1/2$. For independent uniform factors the probability that the predicted product is correct on at least a $1/2+\delta$ fraction of its entries is at most $2^{-\Omega_\delta(d^{1/4})}$. This allows the two arbitrary separate-input offsets above. Any menu of $2^{o(d^{1/4})}$ such predictors has vanishing probability that even one member achieves that agreement.

To prove this, write $D=d^2$. For $k=\lfloor c_\delta d^{1/4}\rfloor$, the masks with $r_Z\le k$ span dimension less than $\delta D$ for sufficiently small $c_\delta>0$ and large $d$. Otherwise apply the correction inequality with $q=\lceil\delta D\rceil$: its right side is asymptotic to $\delta^{3/4}d^{9/4}$, while $s+qk$ is smaller. Choose each bit of a random mask independently with probability $p=k/(8D)$. A subspace of dimension $q'$ has mask probability at most $(1-p)^{D-q'}$. Indeed after fixing the $q'$ independent coordinates the other coordinates must each assume a prescribed value. On masks outside the exceptional subspace the absolute correlation is at most $2^{-k/2}$ even with offsets.

Let $J$ be the Hamming weight of the vector of errors including offsets. Averaging the masking character first over masks and then over inputs gives
$$
  \mathbb E(1-2p)^J\le(1-p)^{(1-\delta)D}+2^{-k/2}.
$$
On $J\le(1/2-\delta)D$ the integrand is at least $(1-2p)^{(1/2-\delta)D}$. After division the first term is at most $\exp(-\delta pD+O(p^2D))$ and the second at most $\exp(-k\log(2)/2+(1-2\delta)pD+O(p^2D))$. Both are exponentially small in $k$. A union bound proves the menu assertion, even if a selector can see both inputs for free. Its fixed positive target fraction is essential to this estimate.
