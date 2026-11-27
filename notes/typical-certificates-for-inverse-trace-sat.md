# Almost every inverse-trace SAT verdict requires almost every input pin

Fix any binary basis for the field with $2^d$ elements. For a uniformly chosen $x$ let $J(x)$ be the largest number of coordinates one can leave unspecified while the remaining coordinates of $x$ force the sign of $f(x)=(-1)^{\operatorname{Tr}(\operatorname{inv}_0(x))}$. Put

$$
 B=\log_2\log_2 d,\qquad m=\lfloor B+\log_2 B\rfloor .
$$

As $d$ tends to infinity, $J(x)\in\{m,m+1\}$ with probability tending to one. This holds separately for each verdict. The convergence bounds are uniform in the choice of the fixed basis. In the explicit SAT encoding with $d$ isolated, variable pin signs, the minimum number of pins determining the promised verdict is therefore either $d-m-1$ or $d-m$ on almost all inputs. The same inputs force that many distinct pin reads on every correct unrestricted deterministic SAT solver. Even a randomized solver seeking only two-thirds success under this input distribution needs a worst-case cap of at least $d-m-O(1)$ pin probes. [Formula construction and bit length](inverse-trace-challenges-on-sat-runs.md)

## Small sets of translated field elements

For distinct $u_1,\ldots,u_h$ in the field, Li and Zhong's equation (4.1), with trivial additive twist, gives $|\mathbb E_x\prod_{i=1}^h f(x+u_i)|\le 8h\,2^{-d/2}$ for $h\ge1$. It follows from a character-sum bound for the rational function with a simple pole at each shift. Expanding the product of the indicators $(1+\eta_i f(x+u_i))/2$ gives, for every specified sign pattern $\eta$,

$$
 \left|\Pr_x[\forall i,\ f(x+u_i)=\eta_i]-2^{-h}\right|
     \le 8h\,2^{-d/2}.
$$

When the shifts include zero, conditioning on $f(x)=\sigma$ and considering compatible patterns doubles the error because $f$ is balanced. The estimate is uniform in the shifts. [Li and Zhong, Lemma 4.1](https://arxiv.org/html/2610.27127v1#S4)

For a set $S$ of $j$ coordinates let $E_S$ be the event that the coordinate cube through $x$ with those free coordinates is monochromatic. Fix either sign at $x$. Set $h=2^j$, $p=2^{1-h}$, and $M=\binom{d}{j}$. The translated points of this cube are all distinct. The shift sets for $S$ and $T$ meet in a set of size $2^t$ for $t=|S\cap T|$, including zero. Consequently

$$
 \Pr[E_S]=p+O(h2^{-d/2}),\qquad
 \Pr[E_S\cap E_T]=p^2\,2^{2^t-1}+O(h2^{-d/2}).
$$

The second formula also covers $S=T$. The subtraction of one in the overlap exponent charges the already fixed sign at $x$ once.

## The largest cube through a typical point

For $j=m+2$, $h\ge 2B\log_2 d$ whereas $j=B+\log_2 B+O(1)$. The expected number of successful $S$ is at most $d^j(p+O(h2^{-d/2}))=o(1)$. A larger monochromatic cube contains one of dimension $j$ through the same $x$. Thus $J(x)\le m+1$ with probability tending to one.

For $j=m$, let $Z=\sum_S1_{E_S}$. We have $\mathbb E Z=Mp(1+o(1))$. The additive error in the two-cube estimate divided by $p^2$ tends to zero, since $h=O(B\log d)=o(d)$. For two independent uniformly chosen coordinate sets $S,T$ this gives

$$
 \frac{\mathbb E Z^2}{(\mathbb E Z)^2}
   \le (1+o(1))\,\mathbb E_{S,T}2^{2^{|S\cap T|}-1}+o(1).
$$

Here the relative error from the denominator tends to zero independently of the overlap. For every $t\ge1$ the probability of at least $t$ common coordinates is at most $(2j^2/d)^t$ at these lengths, by specifying a subset of $S$ that is included in $T$. Put $\delta=1-2^j/(j\log_2 d)$. Since $2^j\le B\log_2 d$ and $j\ge B+\log_2 B-1$, we have $\delta\ge(\log_2 B-1)/(B+\log_2 B-1)$ for large $d$. For $1\le t\le j$ the sequence $2^t/t$ is nondecreasing. The contribution of positive overlaps is therefore bounded by

$$
 \sum_{t=1}^j (2j^2/d)^t\,2^{2^t}
          \le \sum_{t=1}^j (2j^2 d^{-\delta})^t=o(1).
$$

Zero overlap contributes at most one. The second moment ratio tends to one, so $\Pr[Z=0]=o(1)$ by Chebyshev. This proves the lower side of the two-point interval. It proves the existence of a determining subset of the given input. Locating such a subset during a run is a separate query problem.

## Two-thirds average success still requires almost all the pins

Choose fixed $0<\epsilon<1/3$, and let $j=m+C_\epsilon$ for a sufficiently large fixed integer $C_\epsilon$. For each $S$ of size $j$, compare the $h=2^j$ signs around uniformly random $x$ with $h$ independent fair signs. The total variation distance is at most $O(2^h h2^{-d/2})$ by the pattern estimate. For independent signs the probability that their average has absolute value exceeding $\epsilon$ is at most $2\exp(-\epsilon^2 h/2)$. The union bound over $M\le d^j$ sets gives

$$
 \Pr_x[\text{some such cube through }x\text{ has bias greater than }\epsilon]
  \le d^j\bigl(2e^{-\epsilon^2h/2}+O(2^h h2^{-d/2})\bigr)=o(1).
$$

Indeed $h$ lies between $2^{C_\epsilon-1} B\log_2 d$ and $2^{C_\epsilon}B\log_2 d$. The first term beats $d^j$ by choosing the constant, while $h+j\log_2 d=o(d)$ controls the second.

Consider any deterministic adaptive algorithm capped at $d-j$ coordinate probes. Refine each stopping transcript by dummy probes until exactly $d-j$ distinct coordinates are fixed, retaining its original output. Each nonempty leaf is one full $j$-cube. Uniform input is uniform in its leaf. The total probability of the biased leaves is $o(1)$ by the preceding bound, even if the algorithm chose the free coordinates adaptively. It can succeed with probability at most $(1+\epsilon)/2+o(1)$. Averaging over random tapes yields the same result for any randomized algorithm with this cap. A cap permitting two-thirds success must thus exceed $d-m-C_\epsilon$ eventually. This argument uses no uniformity or computation bound on the algorithms.

## An explicit DNF consequence

In any fixed basis, every DNF for either exact verdict has $\Omega(2^d/(\log d\log\log d))$ terms. Cover the $(1-o(1))2^{d-1}$ typical inputs of that verdict. A term covering even one of them has at most $2^{m+1}$ points, by the two-point estimate. This lower bound also holds for any DNF consisting of sound terms that covers a fixed positive fraction of that verdict.

For that one-sided approximation the order of growth is sharp. With $j=m$, write $\mu=\mathbb E[Z\mid f(x)=\sigma]$ and $h=2^m=\Theta(\log d\log\log d)$. The number of monochromatic $j$-cubes of that sign is exactly $2^{d-1}\mu/h$ by counting incidences. The overlap calculation bounds the fraction of sign-$\sigma$ inputs with degree below $\mu/2$ by $O(j^2d^{-\delta})+2^{-\Omega(d)}$, which is $o(1/h)$. Here the exponentially small term absorbs the translated-pattern errors after division by $p^2$. Independently select each monochromatic cube with probability $A/\mu$ for a sufficiently large constant $A$, at large lengths where $\mu\to\infty$. A high-degree point is missed with probability at most $e^{-A/2}$. A selection of $O(2^d/h)$ terms covering any prescribed constant fraction less than one follows, for example by Markov's inequality on both selected count and missed count with $A$ chosen for the requested coverage.

For an exact upper bound, use $A=4\ln h$ and add individual terms for uncovered points of the designated sign. The expected cost is $O(2^d\ln h/h)=O(2^d/\log d)$, including the low-degree points. This leaves a factor of order $\log\log d$ between the exact DNF bounds. The denominator $\log d\log\log d$ also occurs for random Boolean functions in classical work on shortest DNFs. Historical priority for the inverse-trace specialization and the two-point result is unverified. [Pippenger, shortest DNFs of random Boolean functions](https://doi.org/10.1002/rsa.10065)

The explicit SAT family can always be decided on its promise by reading the $d$ pins and computing the field function. Counting distinct probes alone cannot exclude linear time in the encoded SAT length. Lean verifies the overlap cardinality and its counting factor. The audit enumerates fixed-coordinate cubes in dimensions 3 through 10 and checks the ideal moments on all small truth tables. The character-sum bound and the limiting probability estimates above are paper arguments. [Lean proof](../lean/InverseTraceSubcubeOverlap.lean) · [Finite subcube audit](../audits/inverse_trace_subcube_audit.py)
