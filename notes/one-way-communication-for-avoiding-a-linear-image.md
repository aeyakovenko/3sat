# How many bits must one party send to avoid a linear image?

Alice knows $u\in\mathbb F_2^d$. Bob knows a binary linear map from a specified family and must output an $m$-bit word different from its value at $u$. For $m\to\infty$ and $d\ge m+\lfloor\log_2 m\rfloor$, there is a family of maps specified by $d+O(m^2)$ bits for which the exact deterministic one-way communication cost, up to an absolute additive constant, is
$$
                         d-m-\log_2 m+O(1).
$$
Both parties may compute arbitrary functions locally. The protocol must succeed on every input. Classical exclusion games ask Bob to avoid a specified coordinate restriction of Alice's input. Here Bob chooses a linear map. The covering theorem for random binary linear hashes is the main prior result used in the lower bound. Priority for this communication formulation is unverified. [Exclusion games](https://eccc.weizmann.ac.il/report/2016/016/download/) · [Alon, Dietzfelbinger, Miltersen, Petrank and Tardos, Theorem 2](https://theory.stanford.edu/~trevisan/cs174/linearhash.pdf)

## The family and a lower bound for each message length

Take $k=3m$. Bob holds $v\in\mathbb F_2^{d+k-1}$ defining the $k$-bit map $(T_v u)_j=\sum_{i=0}^{d-1}u_i v_{i+j}$, and an arbitrary $(m-1)\times k$ matrix $R$. His target to avoid is
$$
               H(u,v,R)=\big((T_vu)_0,\ RT_vu\big).
$$
A fixed output bit can be evaluated in polynomial time and logarithmic workspace by rescanning the input. The family can be used as a seed-independent range evaluator. For $m=\lfloor n^\epsilon\rfloor$ with fixed $0<\epsilon<1/2$, choose $d$ maximal with $2d+k-1+(m-1)k\le n$. Then $d=\Theta(n)$ eventually. Fix finitely many small sizes separately.

There is an absolute $C$ such that every left set $S$ of size at least $Cm2^m$ has a single Bob input with $H(S,v,R)=\mathbb F_2^m$. Reduce $S$ to $q=\lceil Cm2^m\rceil$ elements. For nonzero $z\in\mathbb F_2^d$, the $k$ shifted linear forms in $v$ giving $T_vz$ are independent, by the first nonzero coordinate of $z$. Under uniform $v$ the collision probability for a fixed unequal pair is $2^{-k}$, so the probability of any collision within this set is at most $\binom q2 2^{-k}=o(1)$. Also the first coordinate uses a uniformly random $d$-bit row. The sum of its signs over $S$ has second moment $q$, by orthogonality of unequal characters. With probability at least $1-4/q$ its absolute value is at most $q/2$, and hence both first-bit parts have size at least $q/4$. Choose a single $v$ meeting both conditions.

Each of the two parts of $T_v(S)$ now has at least $q/4$ distinct points. The binary linear covering theorem says that a uniform $R$ covers all $2^{m-1}$ bins on either fixed part with probability at least $3/4$ once $C$ is a sufficiently large absolute constant. A union bound gives a single matrix covering both. This proves the assertion, including the fixed first output coordinate. [Linear Hash Functions, Theorem 2](https://theory.stanford.edu/~trevisan/cs174/linearhash.pdf)

A message class of a correct one-way protocol therefore has fewer than $Cm2^m$ possible left inputs, up to integer rounding. Otherwise some Bob input would leave him no legal output throughout that class. Counting all $2^d$ left inputs gives the lower bound. Even allowing arbitrary variable-length messages, at most $(2^{a+1}-1)\lceil Cm2^m\rceil$ left inputs can have messages of length at most $a$. This controls the lower tail for a uniform left input independently of Bob's input.

## A nonlinear message attaining the logarithmic saving

Write $h=\lfloor\log_2 m\rfloor-1$ and $p=m+h$. There is a red–blue coloring of $\mathbb F_2^p$ such that for every $h$-dimensional subspace, **some coset is all red and some coset is all blue**. In a fair independent coloring the $2^m$ cosets of a fixed direction are disjoint. The probability none is entirely red is at most $\exp(-2^{m-2^h})$ and the same bound holds for blue. There are at most $2^{ph}$ directions by counting ordered lists of $h$ generators. Since $2^h\le m/2$, the union bound is less than one for large $m$. Fix such a coloring, or search for it without a local computation bound.

Alice sends the first $d-p$ bits of $u$ and the color of the remaining $p$ bits. On that slice Bob's map is affine. If the linear part has rank less than $m$, an output outside its whole image suffices. Otherwise each fiber is a coset of its $h$-dimensional kernel. Bob takes the output corresponding to a coset of the opposite color. This costs $d-p+1=d-m-\log_2 m+O(1)$ bits and works for *every* binary linear map. Each color class in this proof contains a translate of every kernel direction, the higher-rank Kakeya property. Kopparty, Lev, Saraf and Sudan study such sets and explicit constructions. The coloring proof charges only communication. [Higher-rank Kakeya sets](https://arxiv.org/abs/1003.3736) The finite audit checks a small coloring and its omitted outputs independently. [Audit](../audits/linear_image_exclusion_audit.py)

A RAM can read both parties' inputs. It can avoid this very family by complementing the parity of the packed inner product for the **first** output coordinate, then writing zeros. This uses $O((d+m)/w+\log w)$ native steps including the final parity fold, or $O(n/\log n)$ on the indexed family. The communication lower bound therefore isolates the effect of sending a summary before seeing the map. It gives no superlinear SAT time bound. [Sharp affine-query threshold for related shifted products](affine-avoidance-of-shifted-inner-products.md)
