# The rank of parity queries down a quadratic field tower

On $E=\mathbb F_{2^d}$ write $I_d(x)=\operatorname{Tr}_{E/\mathbb F_2}(\operatorname{inv}_0 x)$, with $\operatorname{inv}_0(0)=0$. A survey of the quotient by an additive subfield means learning the coset using binary linear queries. The rank of a transcript is the dimension of the span of all forms actually queried. Its inputs form an affine flat of dimension $d$ minus this rank. The queries can depend on previous answers.

For even $d=2m$, a survey of $E/\mathbb F_{2^m}$ leaves **at least $\lfloor m/2\rfloor-1$ additional independent parity queries** on every input outside the subfield before any exact algorithm can decide $I_d$. For $d=2^\ell$ there is a natural policy that repeats the survey down the quadratic tower. On a uniform trace-one input its final rank has the exact law

$$
                 d-C_\ell,\qquad
 C_0=0,\qquad
 \Pr[C_{j+1}=r+1\mid C_j=r]=2^{-r},
$$

with the remaining probability at $r$. This is Morris's approximate counter. No coins are used by the survey. The probability is over its inputs. Its average rank on this sign is $d-\log_2\log_2 d+O(1)$, and its worst-case rank $d-1$ is optimal even among arbitrary parity decision trees. The result describes an input-reading policy for this explicit function, including its appearance on the [SAT pin family](inverse-trace-challenges-on-sat-runs.md). It does not require every SAT solver to follow that policy. Priority for the tower-transcript distribution is unverified. [Morris](https://doi.org/10.1145/359619.359627) · [Flajolet's analysis](https://algo.inria.fr/flajolet/Publications/Flajolet85c.pdf)

## What one quotient reveals

Let $K=\mathbb F_Q$ with $Q=2^m$ and $[E:K]=2$. Identify a quotient value with $h=x+x^Q\in K$. The kernel of this surjective linear map is $K$. For $h=0$ the answer is zero. For $h\ne0$ set

$$
 y=\frac{x^{Q+1}}h
   =\operatorname{inv}_0\big(\operatorname{Tr}_{E/K}(\operatorname{inv}_0 x)\big).
$$

Then $I_{2m}(x)=I_m(y)$. On the coset $x=a+t$, $t\in K$, the formula is $y=(a^{Q+1}+ht+t^2)/h$. This is affine over $\mathbb F_2$ with a one-dimensional kernel $\{0,h\}$. Its image is exactly the hyperplane $\operatorname{Tr}_{K/\mathbb F_2}(y/h)=1$. Indeed $x$ and $x^Q$ are the two roots of $X^2+hX+hy$. After dividing by $h^2$, the image of $v\mapsto v^2+v$ in $K$ is the absolute-trace-zero hyperplane, by its kernel size and trace invariance. The polynomial has its roots outside $K$ precisely when the displayed trace is one.

For $g_m=(-1)^{I_m}$, every monochromatic affine flat in $K$ has codimension at least $\lfloor m/2\rfloor$. Here is the calculation. Inversion permutes $K$, so $\widehat g_m(0)=0$. A nonzero Walsh sum without normalization is one plus the binary Kloosterman sum over $K^\times$. The latter has magnitude at most $2\sqrt Q$. At even $m$ it is odd and $2\sqrt Q$ is an even integer, giving $|\widehat g_m(u)|\le 2/\sqrt Q$ in normalized convention. In general the bound $(2\sqrt Q+1)/Q$ suffices. The absolute bias on an affine flat of codimension $r$ is bounded by $(2^r-1)\max_u|\widehat g_m(u)|$. This is strictly below one for $r<\lfloor m/2\rfloor$. At even $m$ the subfield of size $\sqrt Q$ attains equality in the codimension bound. [Lachaud and Wolfmann on the binary Kloosterman spectrum](https://doi.org/10.1109/18.54892)

A leaf in a fixed nonzero coset reached with $r$ additional independent queries has dimension $m-r$. Its image in $K$ has dimension at least $m-r-1$. Exact decision makes that image monochromatic. The preceding codimension bound in $K$ gives $r\ge\lfloor m/2\rfloor-1$, separately for every nonzero coset. At even $m$ there is also an entropy bound within each such coset. A character on $t$ nontrivial on the one-dimensional kernel cancels. Every remaining normalized Walsh coefficient is, up to a sign, a sum or difference of two coefficients of $g_m$, by expanding the image hyperplane indicator. All are at most $4/\sqrt Q$ in magnitude, including the constant coefficient. For any fixed $r$-dimensional span $V$ of residual query forms, the probability that the algorithm stops with that span is at most $16\cdot2^r/Q$. Indeed the mean squared bias on its cosets is $\sum_{u\in V}|\widehat g(u)|^2$, and any used stopping coset has squared bias one. Hence the entropy of the stopping span plus its expected dimension is at least $m-4$ under a uniform input on that coset. This bound also allows the algorithm to ask other parities adaptively after the survey.

## Repeated quotients and an exact distribution

Let $d=2^\ell$ and $E_i=\mathbb F_{2^{d/2^i}}$. Start with $x_0=x$ and set

$$
 x_{i+1}=\operatorname{inv}_0\big(\operatorname{Tr}_{E_i/E_{i+1}}(\operatorname{inv}_0 x_i)\big).
$$

At stage $i$ the policy learns $h_i=\operatorname{Tr}_{E_i/E_{i+1}}x_i$. If it is zero, the answer is zero. Otherwise $x_{i+1}$ is affine in $x_i$ on that coset. On each fixed transcript so far, subsequent quotient bits are therefore affine functions of the original input and can be obtained by parity queries with known offsets. The policy computes $I_d$ after at most $\ell$ stages. On either verdict the quotient dimensions sum to at most $d/2+d/4+\cdots+1=d-1$, which bounds the number of independent queries even on a run that never stops early. The last field is $\mathbb F_2$. At its preceding stage a nonzero quotient forces $x_\ell=1$.

Trace transitivity yields $x_j=\operatorname{inv}_0(\operatorname{Tr}_{E_0/E_j}(\operatorname{inv}_0 x))$. It is uniform on $E_j$ for a uniform original input. The first $j$ quotients are nonzero exactly when $x_j\ne0$, an event of probability $1-2^{-d/2^j}$. Every $I_d(x)=1$ input lies in this event. On a fixed surviving transcript, the composite affine map to $E_j$ has kernel dimension at most $j$ on the original fiber. Each stage can add at most its one kernel dimension. A final monochromatic leaf for any algorithm that has collected these $j$ quotient values must consequently have rank at least $d-j-\lceil d/2^{j+1}\rceil$. For $j=\ell$ the last field's monochromatic flats are singletons and the bound becomes $d-\ell$. Taking $d/2^j$ between $2\log_2 d$ and $4\log_2 d$ yields $d-O(\log d)$ rank on at least $1-d^{-2}$ of uniform inputs. This restriction is on the surveys made by the policy.

To compute the rank distribution of the policy itself, reconstruct transcripts in reverse order, starting from the singleton $\{1\}$ in the last field. At any lower field $K$, a fixed surviving lower transcript gives a nonempty affine set $A\subseteq K$ of dimension $r$. It omits zero because every point has trace-one inverse. For every $u\in K^\times$ take the next quotient value $h=1/u$. The compatible elements of $A$ are precisely those for which $\operatorname{Tr}(uz)=1$. Each has two lifts to the larger field. All of their lifts form a single affine leaf in the coset of quotient $h$.

| Behavior on $A$ of $z\mapsto\operatorname{Tr}(uz)$ | Number of $u$ | Number of upper inputs for each $u$ |
| --- | ---: | ---: |
| Constant one | $Q/2^{r+1}$ | $2^{r+1}$ |
| Nonconstant | $Q(1-2^{-r})$ | $2^r$ |

All other $u$ have no lifts. The trace pairing is nondegenerate. To be constant one on $A$ requires annihilating its $r$ directions and taking value one on a point outside their span. This gives the first count and excludes $u=0$. Nonconstancy gives the second count and divides the fiber in half. In total $Q|A|$ upper inputs map into $A$. Since a uniform upper input maps to a uniform lower one, uniform sampling conditional on the lower transcript weights the first row of the table by exactly $2^{-r}$. Its affine dimension increases by one. In the other row it stays at $r$. Applying this to a uniform input conditional on $I_d(x)=1$ proves the stated transition law. The dimension of its final affine leaf is precisely $d$ minus its total rank.

In particular $\mathbb E[2^{C_\ell}]=\ell+1$, by conditioning on $C_j$. For an elementary lower bound on $\mathbb E C_\ell$, the waiting time to go from $r$ to $r+1$ has mean $2^r$. The expected hitting time of $r$ is $2^r-1$, hence $\Pr[C_\ell<r]\le (2^r-1)/\ell$. Sum this geometric lower-tail estimate about $\lfloor\log_2\ell\rfloor$ and use Jensen's inequality for the upper bound to obtain $\mathbb E C_\ell=\log_2\ell+O(1)$. For $\ell\ge1$, the maximal saving $\ell$ occurs with probability $2^{-\ell(\ell-1)/2}$, and the minimum saving one occurs with probability $2^{-(\ell-1)}$. Thus both endpoint ranks are attained on trace-one inputs. Lean checks the integer mass and conditional moment identities. A separate enumeration evaluates the original inverse trace and the complete survey independently for every input through field degree 16. [Lean arithmetic](InverseTraceTowerMoment.lean) · [Exhaustive field audit](inverse_trace_tower_audit.py)

There is also an exact description of the zero sign. Suppose stage $i$, numbered from zero, is the first with $h_i=0$, and put $b=d/2^{i+1}$. At stage zero this event has probability $2^{-b}$ and its leaf is the subfield of dimension $b$. For $i\ge1$ its unconditional probability is $2^{-b}-2^{-2b}$ by trace transitivity. Start the backwards reconstruction at the $b$-dimensional subfield of $E_i$, containing zero. Its first nonzero upper quotient has no constant-one functional on this linear space. Every compatible functional cuts it in half, and the two lifts per surviving point give an upper affine leaf of dimension $b$ avoiding zero. Each of the remaining $i-1$ backwards steps now follows the same Morris transition, initialized at $b$. This argument uses only that the lower affine leaf omits zero, independently of the inverse-trace sign of its members. Together with the trace-one law this determines the full distribution.

## The worst-case optimum over all policies

For every $d\ge2$ the minimum worst-case rank of an exact parity decision tree for $I_d$ is $d-1$. A direct algebraic calculation supplies the lower bound. Write $K_0$ for the kernel of absolute trace in $E$. Its vanishing polynomial is $L(X)=\sum_{i=0}^{d-1}X^{2^i}$. The constant and linear coefficients of $L(X)/X$ are both one, so $\sum_{z\in K_0\setminus\{0\}}1/z=1$. For each nonzero $a$, the XOR of $I_d$ over the hyperplane $\operatorname{Tr}(ax)=0$ is therefore $\operatorname{Tr}(a)$. Choose $a$ of trace one. Odd weight on that $(d-1)$-dimensional hyperplane forces Boolean algebraic degree at least $d-1$, by summing its multilinear monomials over the cube. An accepting leaf of rank $r$ is the product over $\mathbb F_2$ of $r$ affine literal functions. Summing the indicators of disjoint accepting leaves bounds the degree above by the largest accepting rank. The same argument for $1+I_d$ gives the lower bound on the largest rejecting rank, too.

For the upper bound, any Boolean function of even weight on an affine cell of dimension at least two admits a nonconstant parity query leaving an even number of accepted inputs in both halves. Choose linear coordinates on the cell and any nonzero form orthogonal to the XOR of its accepted coordinates. The parity of the number in the one-half is zero; the other half also has even weight. Recurse until dimension one, where even weight is monochromatic. The initial weight of $I_d$ is $2^{d-1}$. This last argument concerns worst-case parity queries. Computing or describing the query forms can itself require work on a RAM.
