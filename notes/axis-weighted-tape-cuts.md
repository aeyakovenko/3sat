# SAT lower bounds from motion on individual tape axes

A planar SAT recognizer cannot signal UNSAT within $O(N^{11/10})$ time on every negative input if its average random-access scratch occupancy is $O(T^{1/2})$ and the sum of $1+\text{occupancy}$ at moves on the second axis is $O(T^{1/2})$. Here $N$ is the encoded formula length and $T$ is the time through the first sound signal. The first axis may use the entire $O(T^{3/2})$ cumulative budget. This follows by using long, thin tape rectangles. A side of length one is allowed.

Use the [hybrid model and certificate for shared scratch states](hybrid-tape-cut-trading.md). For a fixed $d$-dimensional tape, let $S_t$ be the number of nonzero scratch words before instruction $t$, and $h_t$ the tape-head position before its access. Define
$$
 A=\sum_{0\le t<T}(1+S_t),\qquad
 M_i=\sum_{1\le t<T:\ h_{t,i}\ne h_{t-1,i}}(1+S_t).
$$
The head moves by one lattice edge or stays. Suppose the bounds on negative runs are $T=O(N^c)$, $A=O((T+1)^{1+\omega})$, and $M_i=O((T+1)^{\mu_i})$, with $c\ge1$, $\omega,\mu_i\ge0$. For $a_+=\max(a,0)$, these bounds are impossible together when
$$
 c(1+\omega)<1+1/c,\qquad
 c+\sum_{i=1}^d(c\mu_i-1/c)_+<1+1/c. \tag{1}
$$
It is enough to check the second condition on the initial segments after sorting the $\mu_i$ in decreasing order. Equivalently, for every subset $I$ of axes require $(1+\sum_{i\in I}\mu_i)c^2<c+|I|+1$. This follows because the sum of positive parts is the maximum subset sum. The empty subset is allowed.

## Rectangle contents and chronological boundaries

Use side lengths $u_i\ge1$, volume $V=\prod_i u_i$, and groups of at most $b$ visits to each rectangle. Translate each axis independently and uniformly modulo its side length. A move on axis $i$ crosses a face with probability $1/u_i$. Its cost at that boundary is $O_d(1+S_t)$. Fix an offset with spatial cost at most the corresponding bound from $\sum_i M_i/u_i$. Within each rectangle number its visits from zero. Use a uniform residue modulo $b$ to start groups at the nonfirst visits with that residue. The first and last groups also have at most $b$ visits. Charge $O_d(V+1+S_t)$ for each internal group boundary. Every nonfirst visit has probability $1/b$ of making this charge; if a spatial boundary is already charged at that time, one chronological record suffices. A residue attaining at most the conditional mean exists. The total certificate in words therefore has size
$$
 Y=O_d\left(1+\sum_i M_i/u_i+(A+TV)/b\right). \tag{2}
$$
Only internal boundaries between groups require a full rectangle image. A rectangle with a single group starts with an implicit blank tape and needs no outgoing image. The verifier sorts and validates the directory, and a challenged group replays its at most $b$ visits. Full scratch comparisons use the charged boundary records, and the per-rectangle contents persist across distinct chronological intervals of that group. Its defect clock is $(b+Y+1)\operatorname{polylog}(N+T+2)$. Checking axis intervals and indexing a rectangular image take only fixed-dimensional word arithmetic. The chronological gluing proof is the same as for cubes. [Hybrid cut verification](hybrid-tape-cut-trading.md)

## A fixed choice of sizes at every iteration

Use $B(e,c)$ for sound nondeterministic certification of nonacceptance of a fixed nondeterministic RAM through native clock $R$ on $m$ public words, in time $(R^e+m^c+1)H^{o(1)}$, $H=\max(2,R,m)$. The SAT assumption implies $B(c,c)$ by the ordinary packed reduction. On a negative source, the true signaling run on the reduction has $T\le H^{c+o(1)}$. If $c=1$, enlarge it slightly, keeping (1) strict. Under (1) put
$$
 \lambda=1+1/c-\max\left(c(1+\omega),\;c+\sum_i(c\mu_i-1/c)_+\right)>0.
$$
Choose $0<\delta<\min(1,\lambda/[1+(d+1)/c])$ and set
$$
 x=1-\delta,\qquad y=x/c,\qquad z_i=(c\mu_i-y)_+.
$$
Take $b=\lceil H^x\rceil$ and $u_i=\lceil H^{z_i}\rceil$. Each $z_i$ is nonnegative and the corresponding side is one if $z_i=0$. Since the positive-part function is 1-Lipschitz, lowering $1/c$ to $y$ adds at most $d\delta/c$ to the sum of side exponents. Since $x+y=1+1/c-\delta(1+1/c)$, the chosen slack ensures
$$
 c(1+\omega)<x+y,\qquad c+\sum_i z_i<x+y,\qquad c\mu_i-z_i\le y.
$$
Thus (2) has exponent at most $y$ and each defect test has exponent at most $x$, including the directory check since $0<y\le x$. If $T<b$, directly simulating through the guessed time fits that same defect-clock budget. Irrational resource exponents may be increased slightly to rational upper bounds preserving the strict inequalities. Then choose rational $\delta$; integer sizes can use powers rounded within a constant factor at the corresponding dyadic scale.

For $1\le e\le c$, guess the chart and use $B(e,c)$ on the search for a defect. Its physical public input is $O(m+H^{y+o(1)})$ words: the inherited source and the chart. The original packed SAT input remains accessible by its local generator. The resulting cost is bounded by
$$
 (H^{ex}+H^{cy}+m^c+1)H^{o(1)}
 \le (R^{ex}+m^c+1)H^{o(1)}.
$$
Here $cy=x\le ex$ and $ex\le c$, so if $m>R$ its cost accounts for $H^{ex}$. The output is $B(ex,c)$ with the *same* public-input exponent $c$. The parameters of the rectangle and of the local verifier are fixed over the iteration. Starting at $e=c$, repeated multiplication by $x<1$ gives $g<1$ after finitely many steps; from an iterate exactly equal to one the next exponent is $x<1$. The complementary interpreter with $R=n_0^D$ for any fixed integer $D>c$ now contradicts $B(g,c)$. Polynomial slack covers the fixed finite number of simulations. [Native complementary diagonal and packed reduction](packed-band-transfer.md)

## Limits and numerical comparison

If $\mu_i=1+\rho$ for every axis, with $\rho\ge0$, then $c\mu_i\ge1/c$. The second inequality of (1) becomes $(d+1+d\rho)c^2<c+d+1$. The occupancy inequality stays $(1+\omega)c^2<c+1$, recovering the earlier scalar-motion test. In one dimension the exact conditions can be written $(1+\mu_1)c^2<c+2$ and $(1+\omega)c^2<c+1$ for all $\mu_1\ge0$: the empty-subset inequality already follows from occupancy. With equal peak and motion budgets, $\mu_i=1+\omega$, the direct single-step case reaches the earlier square-root threshold for $0\le\omega<1/d$. Indeed, for a direct transfer from $e=c$ to $g<1$, both the public and challenge exponents must be strictly below $1/c$. Repeating the rectangle choice with $x=y$ just below $1/c$ yields $(1+\omega)c^2<2$ and $(1+\sum_{i\in I}\mu_i)c^2<2+|I|$ for every $I$. For equal budgets the full subset gives $(d+1+d\omega)c^2<d+2$, which implies the other conditions in that range. [Pure-tape square-root bound of van Melkebeek and Raz](https://pages.cs.wisc.edu/~dieter/Research/sat-t.html) · [Williams's multidimensional-machine rules, §7](https://people.csail.mit.edu/rrw/automated-lbs.pdf)

For the opening example, $c=11/10$, $\omega=1/2$, $(\mu_1,\mu_2)=(3/2,1/2)$. Choose $x=99/100$, $y=9/10$ and $(z_1,z_2)=(3/4,0)$. The three relevant terms are $c(1+\omega)=33/20$, $c+z_1+z_2=37/20$, and $x+y=189/100$. The $x$-axis crossing exponent is $33/20-3/4=9/10$, and the other axis costs at most $11/20$. The exponent falls below one on the tenth transfer. The single-step condition for the first axis fails since $(1+3/2)(11/10)^2=121/40>3$. The scalar theorem with these budget guarantees can take only $\rho=1/2$: a head can keep $\lfloor\sqrt T\rfloor$ words live during $\Theta(T)$ horizontal moves, and make $O(\sqrt T)$ vertical moves with empty scratch. Its total move cost can reach $\Theta(T^{3/2})$. The scalar inequality $4c^2<c+3$ fails for every $c>1$.

The exact-arithmetic audit tests 1,488 exponent comparisons and enumerates all four-step planar nearest-neighbor paths, including stays. Across 2,500 path, occupancy, box and group combinations it checks 30,000 joint offset and residue choices, the exact spatial expectation, the group capacity, and the upper bound on the mean charged across actual distinct chronological boundaries. This is a restricted-model extension; the historical priority of the axis-specific tradeoff is unverified. [Executable audit](../audits/axis_weighted_cut_audit.py)
