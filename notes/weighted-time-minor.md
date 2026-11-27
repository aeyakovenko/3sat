# Time lower bounds with an arbitrarily small fixed power of the minor order

**Research journal, 24 November 2026.** Let $A$ be any deterministic packed-word RAM that signals UNSAT soundly and eventually signals on every unsatisfiable explicit input. Let $E$ be the number of steps through the first signal and $h$ the clique-minor order of its chronology-plus-last-write graph. One may also minimize over valid same-value source choices, as in the [separator verifier](slab-product-tradeoff.md). For each fixed $0<\lambda\le1$, the worst-case value of $(1+E)(1+h)^\lambda$ on unsatisfiable $n$-bit inputs is outside $O(n^c)$ for every fixed
$$
 c<c_\lambda =
 \frac{1-\lambda/2+\sqrt{(1-\lambda/2)^2+4\lambda}}2 .
$$
For example the excluded exponents include $1.10$ at $\lambda=1/4$ and $1.175$ at $\lambda=1/2$. The reference time and all workspace are unrestricted before the contradiction assumption. At weight one the formula recovers $(1+\sqrt{17})/4$.

The weighted bound is especially sensitive to short actual runs. A product estimate with a small positive charge on $h$ permits a large $h$ when $E$ is small, precisely when direct replay costs little. Using a single worst-case upper bound on $Eh$ would throw away this information.

## Replay short runs before cutting long ones

Assume for contradiction a uniform $O(n^c)$ bound on the weighted product, with $1\le c<c_\lambda$. Smaller $c$ are covered by enlarging the exponent. Retain the notation $W(e,d)$ for a sound nondeterministic certificate of nonacceptance within $R$ steps on $m$ public words in time $(R^e+m^d+1)H^{o(1)}$, $H=\max(2,R,m)$. The regular SAT formula for this bounded computation has length $N=H^{1+o(1)}$ and can be probed from the actual source without first writing it. The assumed recognizer supplies $W(d,d)$ for $d=c$ by materializing the ordinary bounded-computation formula. More generally a separate deterministic $O(n^d)$ SAT solver provides that starting point. [The local bounded-computation reduction](packed-band-transfer.md) · [Cost of the public input](materialized-input-census.md)

Given $W(e,d)$ with $1\le e\le d$, seek a new time exponent $g$. Permit two certificate modes on the source formula. The first replays $A$ directly up to $H^{g+o(1)}$ steps, accepting only upon a genuine UNSAT signal. For the cost calculation let this include every true signal at $E\le H^g$, enlarging the clock for setup, simulation and rounding. For the second mode it suffices to cover $E>H^g$. On the latter inputs the weighted hypothesis gives
$$
 (1+E)(1+h)\ \le\ H^{c/\lambda+o(1)}(1+E)^{1-1/\lambda}
 \ \le\ H^{[c-(1-\lambda)g]/\lambda+o(1)}.
$$
The inequality uses $1-1/\lambda\le0$. Use components of size $b=H^{x+o(1)}$, where $x=g/e$. The separator chart then has at most $H^{y+o(1)}$ bits with
$$
 y=\frac{c-(1-\lambda)g}{\lambda}-\frac{x}{2}.
$$
Balance $yd=g$. This yields
$$
 g=\frac{c}{\,1-\lambda+\lambda/d+\lambda/(2e)\,}.
$$
Here $x\ge y$, so the old certificate applied to existence of a defect in the guessed chart pays $H^{xe+o(1)}$ for the pair replay, $H^{yd+o(1)}$ for the chart, and $m^dH^{o(1)}$ for the original data. Guessing and validating the chart fit these budgets. All defects use identical deterministic component logs and test every intervening different-value write, exactly as in the direct separator proof. When $g\le d$ the result implies $W(g,d)$ also at $H=m>R$. Fixed rational exponents can be approximated with arbitrarily small slack. For real $\lambda>0$ take a sufficiently close smaller rational weight and a slightly larger rational $c$ in the strict excluded range. [Component checks and signed diagonal](slab-product-tradeoff.md)

The reciprocal update is affine with slope $\lambda/(2c)<1$:
$$
 \frac1g=\frac{1-\lambda+\lambda/d}{c}
             +\frac{\lambda}{2c}\frac1e .
$$
Its positive fixed point in the original exponent is $(c-\lambda/2)/(1-\lambda+\lambda/d)$. Starting at $e=d$, this iteration decreases and eventually crosses one whenever
$$
 c<1-\lambda/2+\lambda/d,\qquad d\ge1.
$$
At $d=c$ this is exactly $c<c_\lambda$. At the final step choose a bounded nondeterministic interpreter on its own padded input of length $n_0$ with clock $H=n_0^D$, $D>d$. The certificate now signals nonacceptance within $o(H)$ on a negative source and its own timely signal would make the source accept. This is the same signed diagonal as in the unit-weight theorem. The finite arithmetic at the example weights, and the neutral update at the linear-time extremal exponent, are separately checked in Lean. [Exact arithmetic](../lean/WeightedMinorTrade.lean)

## Approaching zero weight

Write $a=c_\lambda-1$. The equality defining the threshold gives $a=(\lambda/2)(1-a)/(1+a)$, hence
$$
 1+\lambda/2-c_\lambda=\lambda a/(1+a)
                         =\lambda^2/2+O(\lambda^3).
$$
A linear run has $O(n)$ graph edges, hence $h=O(\sqrt n)$. Its generic weighted upper exponent is $1+\lambda/2$. The gap has the indicated positive sign for every fixed $\lambda>0$.

Under a separate linear-time SAT hypothesis set $d=e=1$. The first update gives $g=c/(1+\lambda/2)$. It excludes $c<1+\lambda/2$ for every recognizer $A$. At the geometric upper exponent itself the update returns exactly one at every weight. The [all-zero grid construction](sharp-native-separators.md) with constant chamber side and growing expander core has $\Theta(n)$ time, $\Theta(\sqrt n)$ minor order and an $\Omega(n)$ balanced separator. Thus a smaller separator cannot be guaranteed for general linear runs, even on a simple input.

A length-dependent weight entails two further costs. With $d=e=c=1$ even an idealized bound on $(1+E)(1+h)^{\lambda(n)}$ by $O(n)$ yields the first-round power saving $1-g=\lambda/(2+\lambda)$. At $\lambda(n)=1/\log_2 n$, the resulting factor $H^{1-g}$ stays bounded on the balanced source. The regular formula already has a $\Theta(\log^3 H)$ expansion there, and the separator directory, local checks and SAT elimination incur further logarithmic powers. At the fixed point for $c=d=1$ the ideal saving is still only $\lambda/2$, also a bounded factor at this choice of weight. Moreover a constant $C$ in a product upper bound becomes $C^{1/\lambda}$ when one solves for $h$; fixed-factor width and encoding losses have the same nonuniformity. Each use of $H^{o(1)}$ in the fixed-weight proof is made after fixing the weight. Sending $\lambda$ to zero therefore supplies no pure linear-time exclusion. The calculation is an obstacle for this inference, and does not preclude a different argument at the equality case.

## A charge just above the logarithm of the minor order

Sensitive input bits give a different conclusion at the linear right-hand side. Let $f:\mathbb N\to[1,\infty)$ be any function with $f(t)/\log_2(2+t)\to\infty$. Unconditionally, for every deterministic sound and complete UNSAT recognizer on the specified packed model, its worst-case $(1+E)f(h)$ on unsatisfiable inputs is outside $O(n)$. For example this applies to $f(h)=\log_2(2+h)\log_2\log_2(4+h)$. The function need never be computed. It suffices to get the sensitivity and the large minor on the *same* negative input.

For each packed bounded-computation formula $F_x$, take the following guarded formula $G_x$. Give each original clause $(u\lor v\lor w)$ a fresh variable $t_C$ and replace it by
$$
 (u\lor v\lor t_C),\qquad (\neg t_C\lor w\lor y).
$$
Add the unit $a_0$, the clauses $(\neg a_{i-1}\lor\neg a_{i-1}\lor a_i)$ for $1\le i\le M$, and the terminal clause $(\neg a_M\lor\neg y)$, where $M$ is the original number of clauses. Use fresh, disjoint variables throughout. Repeat literals in the endpoint clauses to reach width three. All positive chain variables must be true, forcing $y=0$, and then the replaced clauses have a satisfying extension exactly when the original clauses hold. Each chain clause also has one designated sign, that of its final positive literal $a_i$. Flipping any one designated sign admits the assignment $a_j=1$ up to $j=i-1$ and zero afterwards. Take $y=1$ and every $t_C=1$, making the altered formula satisfiable regardless of $F_x$. This changes one physical bit in a valid instance of the same length. [Finite clause and chain proofs](../lean/WeightedMinorTrade.lean)

In the fixed-width encoding each clause has $\Theta(\log n)$ bits for the new length $n=|G_x|$. A native read of $\Theta(\log n)$ input bits, even unaligned, includes only $O(1)$ designated signs. There are $\Theta(n/\log n)$ of them. On an unsatisfiable $G_x$, the trace through any sound UNSAT signal must probe every one. Otherwise the altered satisfiable instance at an unprobed sign gives the same replies, controllers and writable memory by deterministic induction. Thus $E=\Omega(n/\log n)$ on **every** negative guarded formula.

To see why $h$ must be large on some of these inputs, suppose the claimed $O(n)$ product bound holds. Since $f\ge1$, $A$ signals on every unsatisfiable instance in $O(n)$ time. A fixed timeout therefore gives a deterministic unrestricted-space linear SAT decider, usable as the reference for the [direct separator simulation](slab-product-tradeoff.md). Use $G_x$ in that proof as the target input to $A$. Its length is $\Theta(H\log^3 H)$ on the quadratic signed source of clock $H$. Every word of $G_x$ still has a uniform polylogarithmic-cost generator from $x$: the families for the two replacements and the chain have regular index ranges, fresh variable numbers are offsets of clause or chain numbers, and retrieving the original named literals costs a constant number of calls to the old generator. The verifier uses the sound target $A$ up to the stated linear negative clock, and the cutoff decider as its signed reference. Every true signal it certifies implies nonacceptance of the bounded source because $G_x$ and $F_x$ are equisatisfiable. Exactly the same finite number of defect calls and cut-size calculation now give unsatisfiable $G_x$ with $h\ge\sqrt n/\log^B n$ for fixed $B$, at all sufficiently large source padding lengths. The added polylogarithmic generator cost changes only the fixed power $B$.

Along this family $\log_2(2+h)\ge(1/2-o(1))\log_2 n$ and $E=\Omega(n/\log n)$. Therefore $(1+E)f(h)/n$ is unbounded, as required. At $f(h)=\log_2(2+h)$ these two estimates give only $\Omega(n)$. This argument relies on the distinction between the encoded bit length and the number of packed input words that fit in it.
