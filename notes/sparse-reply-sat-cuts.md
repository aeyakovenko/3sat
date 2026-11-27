# A distributional lower bound on incorrect forecasts at a real SAT cut

Take the uniformly generated ordinary 3-CNF family with $2m$ independent pin signs, encoded length $N=\Theta(m\log m)$, all balanced cut ranks at least $\kappa m$, and at most nine pins unobserved by any halting correct solver. Fix any deterministic SAT solver on the stated logarithmic-word RAM with unrestricted work memory. Stop immediately after its first $m$ distinct pins. At every large scale, for almost every assignment of the data, a solver that finishes in $O(N)$ steps on the family must do at least one of the following on its actual suffix.

* Reread $\Omega(N/\log N)$ distinct pins observed by the cut.
* Retrieve $\Omega(N/\log^4 N)$ **distinct nonzero words** present at the cut, each before the suffix's first write to that address.

The exceptional probability is $2^{-\Omega(N/\log^4 N)}$, also conditional on either verdict. The time restriction has a more precise replacement below which depends only on the number of distinct addresses inspected. Taking the identically zero forecast gives nonzero words. General forecasts let the bound charge information that a suffix-side decoder guessed incorrectly. [Explicit SAT family and native input layout](expander-cut-signs.md)

## Quantifiers and product bound

Write $U$ for the work address range, $v$ for the word alphabet and $w_0=1+\lceil\log_2(Uv+2)\rceil=\Theta(\log m)$. Fix a deterministic predictor. Once per distinct address read before its first suffix-side overwrite, it predicts the word about to be loaded. It may use the controller at the cut, input, prior suffix events, its own scratch, and all previously returned true words. Its scratch starts empty. The starting controller is its only prefix state. The old-pin set, old/new tags, and elapsed prefix time are available only insofar as that controller encodes them. Assume it finishes each genuine prediction, and count all old pins it inspects, even if the native solver never rereads them. The native solver receives its genuine word as usual. A fixed $s$-bit advice string can be supplied to the predictor. For $s>0$ even the best string for this particular input may be chosen in hindsight. The predictor does not choose the cut.

Let $Q$ be the distinct native incoming addresses inspected, $K$ the number with a wrong first prediction, and $R$ the number of distinct previously seen pins the solver or predictor reads after the cut. There are constants $a,\delta,\gamma>0$ such that, for $0\le s\le\gamma m$ and integer $1\le L\le m$, the probability that **some** advice attains both
$$
 R\le \delta m,\qquad (Q+1)(K+s+L)\le a m^2/w_0^2
$$
is at most $O((1+\log(U+1))(2^{-\gamma' m}+2^{-L}))$ for a constant $\gamma'>0$. The null predictor gives the two native costs in the opening statement. The product imposes no prescribed time deadline. For a time bound $CN$ one has $Q\le O(m\log m)$, including a fixed number of access slots per instruction. Choose $s=0$ and $L$ a sufficiently small constant times $m/\log^3m$. The same proof permits $s$ below a sufficiently small constant times that scale. For $s>0$ the first alternative counts predictor pin reads too.

## One fixed balance and controller

For fixed data split $S$, denote its old and new pins by $x,y$. Write $F(x,y)$ for the true sign and $b_0$ for the binary rank of the cross adjacency. Then $2^{-m}\|F\|=2^{-b_0/2}$, with $b_0\ge\kappa m$. Fix a controller and cap parameters $r,q,k$. With public $y$, simulate the suffix using an arbitrary hypothetical initial array $Z$. Keep a local overlay of writes and cached responses. Truncate by the three caps with signed abstention zero, including on a hypothetical divergent branch. With the true prefix array $C(x)$, the truncated value $B$ has $FB=1$ exactly on qualifying runs, and $FB=0$ on the others, for every row reaching the specified cut.

The tree lemma gives $|P-B|\le\eta$ pointwise with bit degree $r$ and work degree $d\le\min(q,k+C\sqrt{q(k+\log(2/\eta))})$ for an absolute $C$. Expand $P$ in the Walsh characters of the bits making up $Z$. At most $D=\sum_{j\le\min(d,U)}\binom Uj(v-1)^j$ characters occur, and $\log_2 D\le O(1+d w_0)$. For each $(x,y)$ the coefficient vector $p(x,y)$ has squared Euclidean norm at most $(1+\eta)^2$ by Parseval. Each component retains $x$-degree at most $r$ because the work coefficient is an average over $Z$. [Adaptive tree approximation and small-error proof](adaptive-default-polynomial.md)

For any qualifying row set $A$ put $a_\alpha(x)=1_A(x)\chi_\alpha(C(x))$, extending $C$ arbitrarily off $A$. Then
$$
 |\mathbb E[F\langle a,p\rangle]|\le
 (1+\eta)2^{-b_0/2}\sqrt{D\,V(m,r)},\qquad
 V(m,r)=\sum_{j=0}^{\min(m,r)}\binom mj .
$$
Indeed, expand $p$ in its $V(m,r)$ possible $x$ characters with vector coefficients depending on $y$. Each corresponding sign change of the rows of $F$ has the same norm. Cauchy–Schwarz over the characters and vector coordinates gives the displayed bound since $\mathbb E\|a\|^2\le D$ and $\mathbb E\|p\|^2\le(1+\eta)^2$. The pointwise approximation adds at most $\eta\Pr[A]$ to the bound on $\mathbb E[1_A F B(x,y,C(x))]$. This *mass factor* permits the use of small-error approximation with a large catalog of read sets. [Vector-valued cut estimate](spectral-work-reads.md)

## Charging on the actual data-dependent split

Fix an advice string and write $\lambda$ for the probability of meeting the three caps. Make a companion run by resampling only those data pins the native prefix has not yet seen, using a single independent uniform full pin string $Y$. Conditional on that prefix the two completions are independent with the same law, so the probability both are cheap is at least $\lambda^2$.

For each fixed $Y$, a cheap companion identifies its split and controller by the following record. Include the controller, at most $r$ old pins queried by the companion suffix or predictor whose true values differ from $Y$, and the at most $k$ incoming addresses and true words where the predictor was wrong. Replay from this controller, predicting on the actual simulated history, consulting the two correction lists, and maintaining the write overlay and the cache. This recreates both native suffix and predictor queries without supplying the original split. It works because only already-seen pins can differ from $Y$ on the companion formula. Let $T$ be the resulting set of pin queries. At most $r$ are old, and at most nine new pins are missing since the full native run read all but nine. Include the at most $r+9$ corrections taking $T$ to the new side of the split. Thus the number of distinct pairs $(S,c)$ encountered on cheap companions for this fill is at most
$$
 J=N^{O(1)}V(2m,r)V(2m,r+9)(k+1)(Uv)^k .
$$
For a fixed pair, the event that the prefix reaches it and its companion is cheap is a row cylinder $A\times\{0,1\}^m$. All those cylinders, interpreted on the full $2m$ pins, are disjoint. On their union sum the fixed-balance bound and average over $Y$. This gives
$$
 \lambda^2\le \eta+J(1+\eta)2^{-\kappa m/2}\sqrt{D V(m,r)} .
$$

For completeness, bin $Q+1$ in $[u,2u)$ with $u$ a power of two. Use $q=\min(U,2u-1)$ and $k=\min(q,\lfloor a m^2/(w_0^2u)-s-L\rfloor)$, skipping negative caps. Then $k\le q$ and $q(k+s+L)\le 2a m^2/w_0^2$, giving $k w_0\le \sqrt{2a}\,m$. Set $\eta=2^{-4(s+L)}$. The work contributions to $\log J$ and $\log D$ are $O(\sqrt a\,m+\log N)$, also when $q=0$. Set $r=\lfloor\delta m\rfloor$. Choose $\delta$, then $a$, so small that the spectral term in the preceding display is $2^{-c_0m}$ for some $c_0>0$, by the binary entropy bound for $V$. Take square roots and sum over $2^s$ strings and at most $O(1+\log(U+1))$ bins. Choose $\gamma<c_0/4$. This gives the stated tail. Either sign has probability $1/2+o(1)$ by the constant-vector spectral bound on one balanced split. Conditioning preserves the conclusion.

## Where the argument stops

On these same formulas a globally correct solver recognizes the layout and computes the verdict in $O(m)=O(N/\log N)$ native operations, with complete SAT fallback on other inputs. Thus the theorem concerns what is retrieved on a run. These formulas cannot separate linear time even if their single-cut analysis is sharpened. Without a cap on $Q$, uniform real approximation of a scan until the first nondefault answer already costs $\Omega(\sqrt Q)$ work degree. The older worst-case sign-rank proof does give a nonzero retrieval bound with arbitrarily many zero queries. Its unbounded scores do not give the distributional norm estimate used here. [Matching algorithms and exact sign-rank argument](half-read-reuse.md) · [Uniform approximation obstruction](adaptive-default-polynomial.md)
